module Optimisation.DeadCodeElimination

-- import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap

import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
import CairoCode.Traversal.Defaults
import CairoCode.Traversal.Composition
import CairoCode.Traversal.ValueTracker
import Utils.Helpers
import Debug.Trace
import Utils.Lens

%hide Prelude.toList

-- Here starts the dead code detector
-- exported subset for reuse
export
registerTracker : (v:(InstVisit (SortedSet CairoReg))) -> Traversal (ScopedBindings (SortedSet CairoReg)) (ValBindType v (SortedSet CairoReg))
registerTracker = generalizeTrack initParam generalTrack implicitRegTracker
    where initParam : Maybe LinearImplicit -> CairoReg -> SortedSet CairoReg
          initParam _ reg = singleton reg
          implicitRegTracker : SortedMap LinearImplicit ((SortedSet CairoReg), CairoReg) -> Traversal (ScopedBindings (SortedSet CairoReg)) (SortedMap LinearImplicit (SortedSet CairoReg))
          implicitRegTracker impls = pure $ mapValueMap (\(val, reg) => insert reg val) impls
          generalTrack : (ret: List CairoReg) -> (params:List (SortedSet CairoReg)) -> Traversal (ScopedBindings (SortedSet CairoReg)) (List (SortedSet CairoReg))
          generalTrack rets args = do
            ctx <- getAllCaseBindings
            let requriedRegs = foldl union empty (ctx ++ args)
            pure $ map (\reg => insert reg requriedRegs) rets

-- the register collector
collectUsedRegisters : (CairoName, CairoDef) -> SortedSet CairoReg
collectUsedRegisters def = snd $ runVisitConcatCairoDef (traversal $ valueCollector idLens (dbgDef def) insert registerTracker returnCollector) def
    where dbgDef : (CairoName, CairoDef) -> CairoReg -> SortedSet CairoReg
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (singleton reg)
          returnCollector : InstVisit  (SortedSet CairoReg) -> Traversal (ScopedBindings (SortedSet CairoReg)) (SortedSet CairoReg)
          returnCollector (VisitReturn res impls) = pure $ foldl union empty (res ++ (values impls))
          returnCollector _ = pure empty
          -- Note: The Idris default implementation is slow, this is faster
          Semigroup (SortedSet CairoReg) where
              (<+>) a b = if a == b
                  then a
                  else foldl (\acc, e => insert e acc) a b
          -- we use the default as we need no Branch awarneness just merging
          BranchAware (SortedSet CairoReg) where

-- Here starts the dead code marker

markUnusedRegisters : SortedSet CairoReg -> (CairoName, CairoDef) -> (CairoName, CairoDef)
markUnusedRegisters liveRegisters def = substituteDefRegisters marker def
    where marker : CairoReg -> Maybe CairoReg
          marker (Const c) = Nothing        -- We leave constant registers untouched
          marker (CustomReg n _) = Nothing  -- We leave custom registers untouched, they are custom for a reason
          marker (Eliminated _) = Nothing   -- Is already Eliminated
          marker reg = if contains reg liveRegisters
            then Nothing                                -- We leave life registers untouched
            else (Just (Eliminated (Replacement reg)))  -- The rest is eliminated

-- Here Starts the  dead code eliminator
isRegEliminated : CairoReg -> Bool
isRegEliminated (Eliminated _) = True
isRegEliminated _ = False

isRegAssigEliminated : CairoReg -> Bool
isRegAssigEliminated (Const _) = True
isRegAssigEliminated rest = isRegEliminated rest


-- Here Starts the implicit preserver
substituteLinearImplicits : (CairoName, CairoDef) -> (CairoName, CairoDef)
substituteLinearImplicits def = let substitutions = snd $ runVisitConcatCairoDef (pureTraversal $ generalize discoverLinearImplicitSubstitutions) def in
        substituteDefRegisters (\r => lookup r substitutions) def
    where discoverLinearImplicitSubstitutions : (rets:List CairoReg) -> SortedMap LinearImplicit (CairoReg, CairoReg) -> (params:List CairoReg) -> SortedMap CairoReg CairoReg
          discoverLinearImplicitSubstitutions res linImpls _ = if all isRegAssigEliminated res
            then fromList $ values linImpls
            else empty
          Semigroup CairoReg where (<+>) left _ = left

-- Here All is put together as a compiler phase
eliminateAssignsDef : (CairoName, CairoDef) -> (CairoName, CairoDef)
eliminateAssignsDef def =  snd $ runVisitTransformCairoDef (fallbackTraversal (lift assigEliminatorSpecialCase) (ignoreControl $ instFallback $ lift $ generalize assigEliminatorGeneral), ()) def
    where assigEliminatorSpecialCase : InstVisit CairoReg -> Maybe (List (InstVisit CairoReg))
          assigEliminatorSpecialCase inst@(VisitReturn _ _) = Just [inst]
          assigEliminatorSpecialCase _ = Nothing
          assigEliminatorGeneral : (rets:List CairoReg) -> SortedMap LinearImplicit (CairoReg, CairoReg) -> (params:List CairoReg) -> Maybe (List (InstVisit CairoReg))
          assigEliminatorGeneral res _ _ = if all isRegAssigEliminated res then Just [] else Nothing

-- Todo: Find out which step is slow in test030 and fix if it is a where problem
public export
eliminateDeadCode : (CairoName, CairoDef) -> (CairoName, CairoDef)
eliminateDeadCode def = let lifeRegisters = collectUsedRegisters def in
    orderUnassignedRegIndexes (substituteLinearImplicits (eliminateAssignsDef (markUnusedRegisters lifeRegisters def)))

-- For testing when dead code elim should be disabled
-- eliminateDeadCode def = orderUnassignedRegIndexes def
