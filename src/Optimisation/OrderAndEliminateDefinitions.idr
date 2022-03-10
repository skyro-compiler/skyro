module Optimisation.OrderAndEliminateDefinitions

import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Utils.Helpers
import CairoCode.Traversal.Base
import Primitives.Primitives

-- Topological Orderer (it is so small that it is not worth a file)
sortUsedDefsTopologicalRecurive : SortedMap Name CairoDef -> SortedSet Name -> Name -> (SortedSet Name, List (Name, CairoDef))
sortUsedDefsTopologicalRecurive allDefs done cur = if contains cur done
    then (done, [])
    else case lookup cur allDefs of
      Nothing => (done, [])
      Just curDef => let (newDone, orderedDefs) = processDef (cur, curDef) in (newDone, orderedDefs ++ [(cur, curDef)])
  where dependencyCollector : InstVisit CairoReg -> SortedSet Name
        dependencyCollector (VisitMkClosure _ name _ _) = singleton name
        dependencyCollector (VisitCall _ _ name _) = singleton name
        dependencyCollector (VisitOp _ _ primFn _) = primFnDependencyNames primFn
        dependencyCollector _ = empty
        dependencies : (Name, CairoDef) -> SortedSet Name
        dependencies def = snd $ runVisitConcatCairoDef (pureTraversal dependencyCollector) def
        processDep : (SortedSet Name, List (Name, CairoDef)) -> Name -> (SortedSet Name, List (Name, CairoDef))
        processDep (nd, acc) n = let (rdone, res) = sortUsedDefsTopologicalRecurive allDefs nd n in (rdone, acc ++ res)
        processDef : (Name, CairoDef) -> (SortedSet Name, List (Name, CairoDef))
        processDef curDef = foldl processDep (insert cur done, []) (dependencies curDef)

export
orderUsedDefs : Name -> List (Name, CairoDef) -> List (Name, CairoDef)
orderUsedDefs entry cairocode = snd (sortUsedDefsTopologicalRecurive (fromList cairocode) empty entry)
