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

%hide Prelude.toList

-- Todo: Have a pass at the end that finds cycles in Closure Call Graph and introduces Wrappers with normal backwards call to resolve it
--       Otherwise cycles in MkClosure Graph can not be resolved
sortUsedDefsTopologicalRecursive : SortedMap Name CairoDef -> SortedSet Name -> Name -> (SortedSet Name, List (Name, CairoDef))
sortUsedDefsTopologicalRecursive allDefs done cur = if contains cur done
    then (done, [])
    else case lookup cur allDefs of
      Nothing => (done, [])
      Just curDef => let (newDone, orderedDefs) = processDef (cur, curDef) in (newDone, orderedDefs ++ [(cur, curDef)])
  where dependencyCollector : Bool -> InstVisit CairoReg -> SortedSet Name
        dependencyCollector True (VisitMkClosure _ name _ _) = singleton name
        dependencyCollector False (VisitCall _ _ name _) = singleton name
        dependencyCollector _ _ = empty
        deps : Bool -> (Name, CairoDef) -> List Name
        deps closuresOnly def = toList $ snd $ runVisitConcatCairoDef (pureTraversal (dependencyCollector closuresOnly)) def
        dependencies : (Name, CairoDef) -> List Name
        dependencies def = (deps True def) ++ (deps False def) -- make closures higher priority (as cairo does not allow backrefs for them -- sadly not enough)
        processDep : (SortedSet Name, List (Name, CairoDef)) -> Name -> (SortedSet Name, List (Name, CairoDef))
        processDep (nd, acc) n = let (rdone, res) = sortUsedDefsTopologicalRecursive allDefs nd n in (rdone, acc ++ res)
        processDef : (Name, CairoDef) -> (SortedSet Name, List (Name, CairoDef))
        processDef curDef = foldl processDep (insert cur done, []) (dependencies curDef)

sortUsedDefsTopologicalFromEntryPoints : SortedMap Name CairoDef -> SortedSet Name -> (SortedSet Name, List (Name, CairoDef))
sortUsedDefsTopologicalFromEntryPoints allDefs entries = foldl process (empty, Nil) entries
    where process : (SortedSet Name, List (Name, CairoDef)) -> Name -> (SortedSet Name, List (Name, CairoDef))
          process (done,acc) cur = let (rdone,res) = sortUsedDefsTopologicalRecursive allDefs done cur in (rdone, acc ++ res)

export
orderUsedDefs : List (Name, CairoDef) -> List (Name, CairoDef)
orderUsedDefs cairocode = snd (sortUsedDefsTopologicalFromEntryPoints (fromList cairocode) entries)
    where isEntry : (Name, CairoDef) -> Bool
          isEntry (_, ExtFunDef _ _ _ _ _) = True
          isEntry _ = False
          entries : SortedSet Name
          entries = fromList $ map fst (filter isEntry cairocode)
