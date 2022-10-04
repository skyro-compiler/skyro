module Optimisation.OrderAndEliminateDefinitions

-- import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap

import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Utils.Helpers
import CairoCode.Traversal.Base
import Primitives.Primitives

%hide Prelude.toList

-- Todo: Have a pass at the end that finds cycles in Closure Call Graph and introduces Wrappers with normal backwards call to resolve it
--       Otherwise cycles in MkClosure Graph can not be resolved
sortUsedDefsTopologicalRecursive : SortedMap CairoName CairoDef -> SortedSet CairoName -> CairoName -> (SortedSet CairoName, List (CairoName, CairoDef))
sortUsedDefsTopologicalRecursive allDefs done cur = if contains cur done
    then (done, [])
    else case lookup cur allDefs of
      Nothing => (done, [])
      Just curDef => let (newDone, orderedDefs) = processDef (cur, curDef) in (newDone, orderedDefs ++ [(cur, curDef)])
  where dependencyCollector : Bool -> InstVisit CairoReg -> SortedSet CairoName
        dependencyCollector True (VisitMkClosure _ name _ _) = singleton name
        dependencyCollector False (VisitCall _ _ name _) = singleton name
        dependencyCollector _ _ = empty
        -- Note: The Idris default implementation is slow, this is faster in the cases where it matters
        Semigroup (SortedSet CairoName) where
            (<+>) a b = if a == b
                then a
                else foldl (\acc, e => insert e acc) a b
        deps : Bool -> (CairoName, CairoDef) -> List CairoName
        deps closuresOnly def = toList $ snd $ runVisitConcatCairoDef (pureTraversal (dependencyCollector closuresOnly)) def
        dependencies : (CairoName, CairoDef) -> List CairoName
        dependencies def = (deps True def) ++ (deps False def) -- make closures higher priority (as cairo does not allow backrefs for them -- sadly not enough)
        processDep : (SortedSet CairoName, List (CairoName, CairoDef)) -> CairoName -> (SortedSet CairoName, List (CairoName, CairoDef))
        processDep (nd, acc) n = let (rdone, res) = sortUsedDefsTopologicalRecursive allDefs nd n in (rdone, acc ++ res)
        processDef : (CairoName, CairoDef) -> (SortedSet CairoName, List (CairoName, CairoDef))
        processDef curDef = foldl processDep (insert cur done, []) (dependencies curDef)

sortUsedDefsTopologicalFromEntryPoints : SortedMap CairoName CairoDef -> SortedSet CairoName -> (SortedSet CairoName, List (CairoName, CairoDef))
sortUsedDefsTopologicalFromEntryPoints allDefs entries = foldl process (empty, Nil) entries
    where process : (SortedSet CairoName, List (CairoName, CairoDef)) -> CairoName -> (SortedSet CairoName, List (CairoName, CairoDef))
          process (done,acc) cur = let (rdone,res) = sortUsedDefsTopologicalRecursive allDefs done cur in (rdone, acc ++ res)

export
orderUsedDefs : List (CairoName, CairoDef) -> List (CairoName, CairoDef)
orderUsedDefs cairocode = snd (sortUsedDefsTopologicalFromEntryPoints (fromList cairocode) entries)
    where isEntry : (CairoName, CairoDef) -> Bool
          isEntry (_, ExtFunDef _ _ _ _ _) = True
          isEntry _ = False
          entries : SortedSet CairoName
          entries = fromList $ map fst (filter isEntry cairocode)
