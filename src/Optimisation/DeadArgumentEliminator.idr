module Optimisation.DeadArgumentEliminator

import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap

import CommonDef
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
ArgUsageState = SortedMap Name (List Bool)

collectUsedRegisters : (Name, CairoDef) -> ArgUsageState -> SortedSet CairoReg
collectUsedRegisters def state = snd $ runVisitConcatCairoDef (traversal $ valueCollector idLens (dbgDef def) prepareB weakGeneralizedTrack returnCollector) def
    where dbgDef : (Name, CairoDef) -> CairoReg -> SortedSet CairoReg
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (singleton reg)
          prepareB : CairoReg -> SortedSet CairoReg -> SortedSet CairoReg
          prepareB r rs = insert r rs
          returnCollector : InstVisit  (SortedSet CairoReg) -> Traversal (ScopedBindings (SortedSet CairoReg)) (SortedSet CairoReg)
          returnCollector (VisitReturn res impls) = pure $ foldl union empty (res ++ (values impls))
          returnCollector _ = pure empty
          weakGeneralizedTrack : (v:(InstVisit (SortedSet CairoReg))) -> Traversal  (ScopedBindings (SortedSet CairoReg)) (ValBindType v (SortedSet CairoReg))
          weakGeneralizedTrack (VisitCall res linImpls name args) = registerTracker (VisitCall res linImpls name neededArgs)
            where neededArgs : List (SortedSet CairoReg)
                  neededArgs = case (lookup name state) of
                    Nothing => args
                    (Just argUse) => map snd (filter fst (zip argUse args))
          weakGeneralizedTrack (VisitMkClosure res name miss args) = registerTracker (VisitMkClosure res name miss neededArgs)
            where neededArgs : List (SortedSet CairoReg)
                  neededArgs = case (lookup name state) of
                    Nothing => args
                    (Just argUse) => map snd (filter fst (zip argUse args))
          weakGeneralizedTrack inst = registerTracker inst


updateUsedArguments : (Name, CairoDef) -> List CairoReg -> ArgUsageState -> (Bool, ArgUsageState)
updateUsedArguments def@(name, _) params state = integrate (lookup name state) (collectUsedRegisters def state)
    where argsNeeded : SortedSet CairoReg -> List Bool
          argsNeeded req = map (\reg => contains reg req) params
          integrate : Maybe (List Bool) -> SortedSet CairoReg -> (Bool, ArgUsageState)
          integrate Nothing req = (True, insert name (argsNeeded req) state)
          integrate (Just oldArgs) req = (newNeeded /= oldArgs,  insert name newNeeded state)
              where newNeeded : List Bool
                    newNeeded = zipWith (\a,b => a || b) oldArgs (argsNeeded req)

updateUsedArgumentsDef : (Name, CairoDef) -> ArgUsageState -> (Bool, ArgUsageState)
updateUsedArgumentsDef def@(_, FunDef params _ _ _) state = updateUsedArguments def params state
updateUsedArgumentsDef def@(_, ExtFunDef _ params _ _ _) state = updateUsedArguments def params state
updateUsedArgumentsDef _ state = (False, state)

singleUsedArgumentsPass : List (Name, CairoDef) -> ArgUsageState -> (Bool, ArgUsageState)
singleUsedArgumentsPass defs state = foldl process (False,state) defs
    where process : (Bool, ArgUsageState) -> (Name, CairoDef) -> (Bool, ArgUsageState)
          process (changed, state) def = let (nChanged, nState) = updateUsedArgumentsDef def state
            in (changed || nChanged, nState)

-- runs singleUsedArgumentsPass until nothing changed
iterUsedArguments : List (Name, CairoDef) -> ArgUsageState -> ArgUsageState
iterUsedArguments defs state = continueCheck (singleUsedArgumentsPass defs state)
    where continueCheck : (Bool, ArgUsageState) -> ArgUsageState
          continueCheck (False, state) = state
          continueCheck (True, state) = iterUsedArguments defs state

collectClosures : List (Name, CairoDef) -> SortedSet Name
collectClosures defs = snd $ runVisitConcatCairoDefs (pureTraversal closureCollector) defs
        where closureCollector : InstVisit CairoReg -> SortedSet Name
              closureCollector (VisitMkClosure _ name _ _) = singleton name
              closureCollector _ = empty

collectUsedArguments : List (Name, CairoDef) -> ArgUsageState
collectUsedArguments defs = iterUsedArguments defs initialArgUseState
    where buildEntry : (Name, CairoDef) -> (Name, List Bool)
          buildEntry (name, FunDef params _ _ _) = (name, replicate (length params) False)
          buildEntry (name, ExtFunDef _ params _ _ _) = (name, replicate (length params) True)
          buildEntry (name, ForeignDef _ args _ ) =  (name, replicate args True)
          initialArgUseState: ArgUsageState
          initialArgUseState = fromList $ map buildEntry defs

removeCallArguments : SortedSet Name -> ArgUsageState -> (Name, CairoDef) -> (Name, CairoDef)
removeCallArguments volatileDefs argsNeeded def = snd $ runVisitTransformCairoDef (pureTraversal eliminateCallArgs) def
    where neededArgs : Name -> List CairoReg ->  List Bool
          neededArgs name regs = fromMaybe (map (\_ => True) regs) (lookup name argsNeeded)
          adaptParam : Bool -> CairoReg -> CairoReg
          adaptParam True reg = reg
          adaptParam False reg@(Eliminated _) = reg
          adaptParam False reg = Eliminated (Replacement reg)
          adaptArgs : Name -> List CairoReg -> List CairoReg
          adaptArgs name regs = if contains name volatileDefs
            then zipWith adaptParam (neededArgs name regs) regs
            else map snd (filter fst (zip (neededArgs name regs) regs))
          eliminateCallArgs : InstVisit CairoReg -> List (InstVisit CairoReg)
          eliminateCallArgs (VisitCall res impls name args) = [(VisitCall res impls name (adaptArgs name args))]
          eliminateCallArgs (VisitMkClosure res name miss args) = [(VisitMkClosure res name miss (adaptArgs name args))]
          eliminateCallArgs inst = [inst]

removeFunArguments : SortedSet Name -> ArgUsageState -> (Name, CairoDef) ->  (Name, CairoDef)
removeFunArguments volatileDefs argsNeeded (name, FunDef params impls rets body) = if contains name volatileDefs
        then (name, FunDef discardedParams impls rets body)
        else (name, FunDef neededParams impls rets body)
    where neededArgs : List Bool
          neededArgs = fromMaybe (map (\_ => True) params) (lookup name argsNeeded)
          neededParams : List CairoReg
          neededParams = map snd (filter fst (zip neededArgs params))
          adaptParam : Bool -> CairoReg -> CairoReg
          adaptParam True reg = reg
          adaptParam False reg@(Eliminated _) = reg
          adaptParam False reg = Eliminated (Replacement reg)
          discardedParams : List CairoReg
          discardedParams = zipWith adaptParam neededArgs params
removeFunArguments _ _ def = def

processDeadArgumentsElimDefs : SortedSet Name -> ArgUsageState -> List (Name, CairoDef) -> List (Name, CairoDef)
processDeadArgumentsElimDefs volatileDefs keepArgs defs = map processDef defs
    where processDef : (Name, CairoDef) -> (Name, CairoDef)
          processDef = (removeFunArguments volatileDefs keepArgs) . eliminateDeadCode . (removeCallArguments volatileDefs keepArgs)

public export
eliminateDeadArgumentsDefs : List (Name, CairoDef) ->  List (Name, CairoDef)
eliminateDeadArgumentsDefs defs = processDeadArgumentsElimDefs volatileDefs usedArguments defs
    where usedArguments : ArgUsageState
          usedArguments = collectUsedArguments defs
          volatileDefs : SortedSet Name
          volatileDefs = collectClosures defs

-- Note: To be certain we need to do 1 again as 2 can enable 1 and repeat until we are done
