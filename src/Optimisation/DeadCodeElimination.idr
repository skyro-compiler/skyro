module Optimisation.DeadCodeElimination

import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap

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
collectUsedRegisters : (Name, CairoDef) -> SortedSet CairoReg
collectUsedRegisters def = snd $ runVisitConcatCairoDef (traversal $ valueCollector idLens (dbgDef def) prepareB registerTracker returnCollector) def
    where dbgDef : (Name, CairoDef) -> CairoReg -> SortedSet CairoReg
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (singleton reg)
          prepareB : CairoReg -> SortedSet CairoReg -> SortedSet CairoReg
          prepareB r rs = insert r rs
          returnCollector : InstVisit  (SortedSet CairoReg) -> Traversal (ScopedBindings (SortedSet CairoReg)) (SortedSet CairoReg)
          returnCollector (VisitReturn res impls) = pure $ foldl union empty (res ++ (values impls))
          returnCollector _ = pure empty


-- Here starts the dead code marker

markUnusedRegisters : SortedSet CairoReg -> (Name, CairoDef) -> (Name, CairoDef)
markUnusedRegisters liveRegisters def = substituteDefRegisters marker def
    where marker : CairoReg -> Maybe CairoReg
          marker (Const c) = Nothing        -- We leave constant registers untouched
          marker (CustomReg n _) = Nothing  -- We leave custom registers untouched, they are custom for a reason
          marker (Eliminated _) = Nothing   -- Is already Eliminated
          marker reg = if contains reg liveRegisters
            then Nothing                            -- We leave life registers untouched
            else (Just (Eliminated (Replacement reg)))      -- The rest is eliminated

-- Here Starts the  dead code eliminator
isRegEliminated : CairoReg -> Bool
isRegEliminated (Eliminated _) = True
isRegEliminated _ = False

isRegAssigEliminated : CairoReg -> Bool
isRegAssigEliminated (Const _) = True
isRegAssigEliminated rest = isRegEliminated rest

-- Here Starts the implicit preserver
substituteLinearImplicits : (Name, CairoDef) -> (Name, CairoDef)
substituteLinearImplicits def = substituteDefRegisters (\r => lookup r substitutions) def
    where discoverLinearImplicitSubstitutions : (rets:List CairoReg) -> SortedMap LinearImplicit (CairoReg, CairoReg) -> (params:List CairoReg) -> SortedMap CairoReg CairoReg
          discoverLinearImplicitSubstitutions res linImpls _ = if all isRegAssigEliminated res
            then fromList $ values linImpls
            else empty
          Semigroup CairoReg where (<+>) left _ = left
          substitutions : SortedMap CairoReg CairoReg
          substitutions = snd $ runVisitConcatCairoDef (pureTraversal $ generalize discoverLinearImplicitSubstitutions) def

-- Here All is put together as a compiler phase
eliminateAssignsDef : (Name, CairoDef) -> (Name, CairoDef)
eliminateAssignsDef def =  snd $ runVisitTransformCairoDef (fallbackTraversal (lift assigEliminatorSpecialCase) (ignoreControl $ instFallback $ lift $ generalize assigEliminatorGeneral), ()) def
    where assigEliminatorSpecialCase : InstVisit CairoReg -> Maybe (List (InstVisit CairoReg))
          assigEliminatorSpecialCase inst@(VisitReturn _ _) = Just [inst]
          assigEliminatorSpecialCase _ = Nothing
          assigEliminatorGeneral : (rets:List CairoReg) -> SortedMap LinearImplicit (CairoReg, CairoReg) -> (params:List CairoReg) -> Maybe (List (InstVisit CairoReg))
          assigEliminatorGeneral res _ _ = if all isRegAssigEliminated res then Just [] else Nothing

public export
eliminateDeadCode : (Name, CairoDef) -> (Name, CairoDef)
eliminateDeadCode def = orderUnassignedRegIndexes $ substituteLinearImplicits (eliminateAssignsDef (markUnusedRegisters lifeRegisters def))
    where lifeRegisters : SortedSet CairoReg
          lifeRegisters = collectUsedRegisters def

-- For testing when dead code elim should be disabled
-- eliminateDeadCode def = orderUnassignedRegIndexes def
