module Optimisation.DeadArgumentEliminator

-- import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap
import Data.Maybe

import CommonDef
import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Optimisation.DeadCodeElimination
import CairoCode.Traversal.Base
import CairoCode.Traversal.ValueTracker
import Utils.Lens
import Utils.Helpers

import Debug.Trace

%hide Prelude.toList

-- Note: Initially a DeadReturnEliminator was planned alongside this.
--       However, it would only work after Untuppling (as Idris is single return)
--       Further, most idris code would not profit from it (as tuple returns are rare)
--       Last, a data flow based dead constructor argument could do the same and more (so if needed a data flow analysis is more viable)

ArgUsageState : Type
ArgUsageState = SortedMap CairoName (List Bool)

collectUsedRegisters : (CairoName, CairoDef) -> ArgUsageState -> SortedSet CairoReg
collectUsedRegisters def state = snd $ runVisitConcatCairoDef (traversal $ valueCollector idLens (dbgDef def) prepareB weakGeneralizedTrack returnCollector) def
    where dbgDef : (CairoName, CairoDef) -> CairoReg -> SortedSet CairoReg
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (singleton reg)
          prepareB : CairoReg -> SortedSet CairoReg -> SortedSet CairoReg
          prepareB r rs = insert r rs
          returnCollector : InstVisit (SortedSet CairoReg) -> Traversal (ScopedBindings (SortedSet CairoReg)) (SortedSet CairoReg)
          returnCollector (VisitReturn res impls) = pure $ foldl union empty (res ++ (values impls))
          returnCollector _ = pure empty
          weakGeneralizedTrack : (v:(InstVisit (SortedSet CairoReg))) -> Traversal  (ScopedBindings (SortedSet CairoReg)) (ValBindType v (SortedSet CairoReg))
          weakGeneralizedTrack (VisitCall res linImpls name args) = registerTracker (VisitCall res linImpls name neededArgs)
            where neededArgs : List (SortedSet CairoReg)
                  neededArgs = case (lookup name state) of
                    Nothing => args
                    (Just argUse) => map snd (filter fst (zip argUse args))
          -- We can not Optimize as arguments are accessable over PROJECT as well (and we do not now if it is used that way)
          -- Todo: Think about the whole access Closure args over Project again but its convinient for Closure gen
          -- weakGeneralizedTrack (VisitMkClosure res name miss args) = registerTracker (VisitMkClosure res name miss neededArgs)
          --   where neededArgs : List (SortedSet CairoReg)
          --         neededArgs = case (lookup name state) of
          --           Nothing => args
          --           (Just argUse) => map snd (filter fst (zip argUse args))
          weakGeneralizedTrack inst = registerTracker inst
          -- Note: The Idris default implementation is slow, this is faster in the cases where it matters
          Semigroup (SortedSet CairoReg) where
            (<+>) a b = if a == b
                then a
                else foldl (\acc, e => insert e acc) a b
          -- we use the default as we need no Branch awarneness just merging
          BranchAware (SortedSet CairoReg) where

updateUsedArguments : (CairoName, CairoDef) -> List CairoReg -> ArgUsageState -> (Bool, ArgUsageState)
updateUsedArguments def@(name, _) params state = integrate (lookup name state) (collectUsedRegisters def state)
    where argsNeeded : SortedSet CairoReg -> List Bool
          argsNeeded req = map (\reg => contains reg req) params
          integrate : Maybe (List Bool) -> SortedSet CairoReg -> (Bool, ArgUsageState)
          integrate Nothing req = (True, insert name (argsNeeded req) state)
          integrate (Just oldArgs) req = let newNeeded = zipWith (\a,b => a || b) oldArgs (argsNeeded req) in
            (newNeeded /= oldArgs,  insert name newNeeded state)


updateUsedArgumentsDef : (CairoName, CairoDef) -> ArgUsageState -> (Bool, ArgUsageState)
updateUsedArgumentsDef def@(_, FunDef params _ _ _) state = updateUsedArguments def params state
-- Starts with all True anyway
-- updateUsedArgumentsDef def@(_, ExtFunDef _ params _ _ _) state = updateUsedArguments def params state
updateUsedArgumentsDef _ state = (False, state)

singleUsedArgumentsPass : List (CairoName, CairoDef) -> ArgUsageState -> (Bool, ArgUsageState)
singleUsedArgumentsPass defs state = foldl process (False, state) defs
    where process : (Bool, ArgUsageState) -> (CairoName, CairoDef) -> (Bool, ArgUsageState)
          process (changed, s) def = let (nChanged, nState) = updateUsedArgumentsDef def s in
            (changed || nChanged, nState)

-- runs singleUsedArgumentsPass until nothing changed
iterUsedArguments : List (CairoName, CairoDef) -> ArgUsageState -> ArgUsageState
iterUsedArguments defs state = continueCheck (singleUsedArgumentsPass defs state)
    where continueCheck : (Bool, ArgUsageState) -> ArgUsageState
          continueCheck (False, state) = state
          continueCheck (True, state) = iterUsedArguments defs state

collectClosures : List (CairoName, CairoDef) -> SortedSet CairoName
collectClosures defs = snd $ runVisitConcatCairoDefs (pureTraversal closureCollector) defs
        where closureCollector : InstVisit CairoReg -> SortedSet CairoName
              closureCollector (VisitMkClosure _ name _ _) = singleton name
              closureCollector _ = empty
              -- Note: The Idris default implementation is slow, this is faster
              Semigroup (SortedSet CairoName) where
                (<+>) a b = if a == b
                    then a
                    else foldl (\acc, e => insert e acc) a b

collectUsedArguments : List (CairoName, CairoDef) -> ArgUsageState
collectUsedArguments defs = iterUsedArguments defs (fromList $ map buildEntry defs)
    where buildEntry : (CairoName, CairoDef) -> (CairoName, List Bool)
          buildEntry (name, FunDef params _ _ _) = (name, replicate (length params) False)
          buildEntry (name, ExtFunDef _ params _ _ _) = (name, replicate (length params) True)
          buildEntry (name, ForeignDef _ args _ ) =  (name, replicate args True)

removeCallArguments : SortedSet CairoName -> ArgUsageState -> (CairoName, CairoDef) -> (CairoName, CairoDef)
removeCallArguments volatileDefs argsNeeded def = snd $ runVisitTransformCairoDef (pureTraversal eliminateCallArgs) def
    where neededArgs : CairoName -> List CairoReg -> List Bool
          neededArgs name regs = fromMaybe (map (\_ => True) regs) (lookup name argsNeeded)
          adaptParam : Bool -> CairoReg -> CairoReg
          adaptParam True reg = reg
          adaptParam False reg@(Eliminated _) = reg
          adaptParam False reg = Eliminated (Replacement reg)
          adaptArgs : CairoName -> List CairoReg -> List CairoReg
          adaptArgs name regs = if contains name volatileDefs
            then zipWith adaptParam (neededArgs name regs) regs
            else map snd (filter fst (zip (neededArgs name regs) regs))
          eliminateCallArgs : InstVisit CairoReg -> List (InstVisit CairoReg)
          eliminateCallArgs (VisitCall res impls name args) = [(VisitCall res impls name (adaptArgs name args))]
          -- We can not Optimize as arguments are accessible over PROJECT as well (and we do not now if it is used that way)
          -- eliminateCallArgs (VisitMkClosure res name miss args) = [(VisitMkClosure res name miss (adaptArgs name args))]
          eliminateCallArgs inst = [inst]

removeFunArguments : SortedSet CairoName -> ArgUsageState -> (CairoName, CairoDef) ->  (CairoName, CairoDef)
removeFunArguments volatileDefs argsNeeded (name, FunDef params impls rets body) = let neededArgs = fromMaybe (map (\_ => True) params) (lookup name argsNeeded) in
        if contains name volatileDefs
            then (name, FunDef (discardedParams neededArgs) impls rets body)
            else (name, FunDef (neededParams neededArgs) impls rets body)
    where neededParams : List Bool -> List CairoReg
          neededParams neededArgs = map snd (filter fst (zip neededArgs params))
          adaptParam : Bool -> CairoReg -> CairoReg
          adaptParam True reg = reg
          adaptParam False reg@(Eliminated _) = reg
          adaptParam False reg = Eliminated (Replacement reg)
          discardedParams : List Bool -> List CairoReg
          discardedParams neededArgs = zipWith adaptParam neededArgs params
removeFunArguments _ _ def = def

processDeadArgumentsElimDefs : SortedSet CairoName -> ArgUsageState -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
processDeadArgumentsElimDefs volatileDefs keepArgs defs = map processDef defs
    where processDef : (CairoName, CairoDef) -> (CairoName, CairoDef)
          processDef = (removeFunArguments volatileDefs keepArgs) . eliminateDeadCode . (removeCallArguments volatileDefs keepArgs)

public export
eliminateDeadArgumentsDefs : List (CairoName, CairoDef) ->  List (CairoName, CairoDef)
eliminateDeadArgumentsDefs defs = processDeadArgumentsElimDefs volatileDefs usedArguments defs
    where usedArguments : ArgUsageState
          usedArguments = collectUsedArguments defs
          volatileDefs : SortedSet CairoName
          volatileDefs = collectClosures defs

-- Note: To be certain we need to do 1 again as 2 can enable 1 and repeat until we are done
