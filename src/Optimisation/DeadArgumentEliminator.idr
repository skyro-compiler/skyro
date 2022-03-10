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
collectUsedRegisters def state = snd $ runVisitConcatCairoDef (traversal $ valueCollector idLens (dbgDef def) weakGeneralizedTrack returnCollector) def
    where dbgDef : (Name, CairoDef) -> CairoReg -> SortedSet CairoReg
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (singleton reg)
          returnCollector : InstVisit  (SortedSet CairoReg) -> Traversal (ScopedBindings (SortedSet CairoReg)) (SortedSet CairoReg)
          returnCollector (VisitReturn res impls) = pure $ foldl union empty (res ++ (values impls))
          returnCollector _ = pure empty
          weakGeneralizedTrack : (v:(InstVisit (SortedSet CairoReg))) -> Traversal  (ScopedBindings (SortedSet CairoReg)) (ValBindType v (SortedSet CairoReg))
          weakGeneralizedTrack (VisitCall res linImpls name args) = registerTracker (VisitCall res linImpls name neededArgs)
            where neededArgs : List (SortedSet CairoReg)
                  neededArgs = case (lookup name state) of
                    Nothing => args
                    (Just argUse) => map snd (filter fst (zip argUse args))
          weakGeneralizedTrack inst = registerTracker inst

updateUsedArgumentsDef : (Name, CairoDef) -> ArgUsageState -> (Bool, ArgUsageState)
updateUsedArgumentsDef def@(name, FunDef params _ _ _) state = integrate (lookup name state) (collectUsedRegisters def state)
    where argsNeeded : SortedSet CairoReg -> List Bool
          argsNeeded req = map (\reg => contains reg req) params
          integrate : Maybe (List Bool) -> SortedSet CairoReg -> (Bool, ArgUsageState)
          integrate Nothing req = (True, insert name (argsNeeded req) state)
          integrate (Just oldArgs) req = (newNeeded /= oldArgs,  insert name newNeeded state)
              where newNeeded : List Bool
                    newNeeded = zipWith (\a,b => a || b) oldArgs (argsNeeded req)
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


collectNonClosures : List (Name, CairoDef) -> List (Name, CairoDef)
collectNonClosures defs = filter (\(n,_) => not $ contains n allClosureCalls) defs
 where closureCollector : InstVisit CairoReg -> SortedSet Name
       closureCollector (VisitMkClosure _ name _ _) = singleton name
       closureCollector _ = empty
       allClosureCalls : SortedSet Name
       allClosureCalls = snd $ runVisitConcatCairoDefs (pureTraversal closureCollector) defs

collectUsedArguments : List (Name, CairoDef) -> ArgUsageState
collectUsedArguments defs = iterUsedArguments defs initialArgUseState
    where buildEntry : (Name, CairoDef) -> (Name, List Bool)
          buildEntry (name, FunDef params _ _ _) = (name, replicate (length params) False)
          buildEntry (name, ForeignDef _ args _ ) =  (name, replicate args True)
          initialArgUseState: ArgUsageState
          initialArgUseState = fromList $ map buildEntry defs

removeCallArguments : ArgUsageState -> (Name, CairoDef) -> (Name, CairoDef)
removeCallArguments argsNeeded def = snd $ runVisitTransformCairoDef (pureTraversal eliminateCallArgs) def
    where neededArgs : Name -> List CairoReg ->  List Bool
          neededArgs name regs = fromMaybe (map (\_ => True) regs) (lookup name argsNeeded)
          filterArgs : Name -> List CairoReg -> List CairoReg
          filterArgs name regs = map snd (filter fst (zip (neededArgs name regs) regs))
          eliminateCallArgs : InstVisit CairoReg -> List (InstVisit CairoReg)
          eliminateCallArgs (VisitCall res impls name args) = [(VisitCall res impls name (filterArgs name args))]
          eliminateCallArgs inst = [inst]

removeFunArguments : ArgUsageState -> (Name, CairoDef) ->  (Name, CairoDef)
removeFunArguments argsNeeded (name, FunDef params impls rets body) = if name == entry_name
    then (name, FunDef params impls rets body)                -- leave the main alone to preserve signature
    else (name, FunDef neededParams impls rets body)
    where neededArgs : List Bool
          neededArgs = fromMaybe (map (\_ => True) params) (lookup name argsNeeded)
          neededParams : List CairoReg
          neededParams = map snd (filter fst (zip neededArgs params))
removeFunArguments _ def = def

public export
eliminateDeadArgumentsDefs : List (Name, CairoDef) ->  List (Name, CairoDef)
eliminateDeadArgumentsDefs defs = map processDef defs
    where usedArguments : ArgUsageState
          usedArguments = collectUsedArguments (collectNonClosures defs)
          processDef : (Name, CairoDef) -> (Name, CairoDef)
          processDef = (removeFunArguments usedArguments) . eliminateDeadCode . (removeCallArguments usedArguments)

-- Note: To be certain we need to do 1 again as 2 can enable 1 and repeat until we are done
