module Optimisation.GlobalStaticOptimizer

import Data.SortedSet
import Data.SortedMap
import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Utils.Helpers
import CairoCode.Traversal.Base
import Optimisation.StaticProcessing.IterativeBaseTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.StaticProcessing.StaticTransformer

%hide Prelude.toList

export
globalStaticOptimize : List (Name, CairoDef) -> List (Name, CairoDef)
globalStaticOptimize = iterativeCallTransform @{config} ()
    where [config] IterativeTransformerConf () where
    -- we use all default impls --


