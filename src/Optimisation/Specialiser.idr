module Optimisation.Specialiser

import Data.SortedMap
import Data.SortedSet
import Data.String

import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
import Utils.Helpers

import Optimisation.StaticProcessing.IterativeBaseTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.StaticProcessing.StaticTransformer

import Optimisation.Inliner
import CommonDef

import Debug.Trace

%hide Prelude.toList

-- Todo: Shall we spezialise known tags in addition to known closure names?
--      It may be usefull in specialising dependently typed functions based on context, eliminating whole branches
--      Note: we already implicitly do this in case we have a record holding a closure

mutual
    -- Only use Locally
    Eq StaticValue where
       (==) (Constructed c1) (Constructed c2) = assert_total (c1 == c2)
       (==) (Constructed _) _ = False
       (==) _ (Constructed _) = False
       (==) (Closure n1 a1) (Closure n2 a2) = n1 == n2 && (assert_total (a1 == a2))
       (==) (Closure _ _) _ = False
       (==) _ (Closure _ _) = False
       (==) _ _ = True

    -- Only use Locally
    Eq StaticInfo where
       (==) (MKStaticInfo _ v1) (MKStaticInfo _ v2) = v1 == v2

    -- Only use Locally
    Ord StaticValue where
       compare (Constructed c1) (Constructed c2) = assert_total $ compare (toList c1) (toList c2)
       compare (Constructed _) _ = GT
       compare _ (Constructed _) = LT
       compare (Closure n1 a1) (Closure n2 a2) = thenCompare (compare n1 n2) (assert_total $ compare a1 a2)
       compare (Closure _ _) _ = GT
       compare _ (Closure _ _) = LT
       compare _ _ = EQ

    -- Only use Locally
    Ord StaticInfo where
        compare (MKStaticInfo _ v1) (MKStaticInfo _ v2) = compare v1 v2

specName : CairoName -> Int -> CairoName
specName name num = extendName "specialized" num name

specDepth : CairoName -> Int
specDepth (Extension "specialized" (Just num) _) = num+1
specDepth _ = 0

-- todo: just closures for now, no other statics
containsKnownClosure : StaticInfo -> Bool
containsKnownClosure (MKStaticInfo _ (Constructed ctrs)) = any (any containsKnownClosure) (values ctrs)
containsKnownClosure (MKStaticInfo _ (Closure (Just _) _)) = True
containsKnownClosure _ = False


isKnown : StaticInfo -> Bool
isKnown (MKStaticInfo _ (Closure (Just _) _)) = True
isKnown (MKStaticInfo _ (Closure Nothing args)) = any isKnown args
isKnown (MKStaticInfo _ (Constructed ctrs)) = any (any isKnown) (values ctrs)
isKnown _ = False

mutual
    reduceStaticValToEssential : StaticValue -> StaticValue
    reduceStaticValToEssential (Constructed ctrs) = let essentialCtrs = valueFilter (any isKnown) (mapValueMap (map reduceInfoToEssential) ctrs) in
        if isNil $ toList essentialCtrs then Unknown else Constructed essentialCtrs
    reduceStaticValToEssential (Closure (Just nm) args) = Closure (Just nm) (map reduceInfoToEssential args)
    reduceStaticValToEssential (Closure Nothing args) = let rArgs = (map reduceInfoToEssential args) in
        if any isKnown rArgs
            then Closure Nothing rArgs
            else Unknown
    reduceStaticValToEssential _ = Unknown

    reduceInfoToEssential : StaticInfo -> StaticInfo
    reduceInfoToEssential (MKStaticInfo _ val) = MKStaticInfo empty (reduceStaticValToEssential val)

reduceInfos : List StaticInfo -> List StaticInfo
reduceInfos infos = map reduceInfoToEssential infos

-- Todo make Configurable
specDepthLimit : Int
specDepthLimit = 5

specialisationDecider : CairoName -> List StaticInfo -> Bool
specialisationDecider name args = specDepth name < specDepthLimit && any containsKnownClosure args

SpecInfo : Type
SpecInfo = (SortedMap CairoName (SortedMap (List StaticInfo) Int), SortedMap CairoName (List StaticInfo))

specialise : SpecInfo -> CairoName -> List StaticInfo -> (SpecInfo, CairoName, Bool)
specialise state@(index,specs) name infos = case lookup name index of
               Nothing => specialise (insert name empty index, specs) name infos
               (Just inner) => case lookup infos inner of
                    (Just n) => (state, specName name n, False)
                    Nothing => let n = cast $ length $ toList inner in
                               let sname = specName name n in
                               ((insert name (insert infos n inner) index, insert sname infos specs), sname, True)

extendWithUnknown : Nat -> List StaticInfo -> List StaticInfo
extendWithUnknown n infos = infos ++ (unknown n)
    where unknown : Nat -> List StaticInfo
          unknown Z = Nil
          unknown (S n) = (MKStaticInfo empty Unknown)::(unknown n)


specialiseDefsPass : SpecInfo -> List (CairoName, CairoDef) -> (SpecInfo, List (CairoName, CairoDef))
specialiseDefsPass specs allDefs = rawIterativeCallTransform @{config} specs allDefs
    where paramInit : CairoReg -> StaticInfo
          paramInit reg = MKStaticInfo (singleton reg) Unknown
          paramBind : CairoReg -> StaticInfo -> StaticInfo
          paramBind reg (MKStaticInfo regs val) = (MKStaticInfo (insert reg regs) val)
          [config] IterativeTransformerConf SpecInfo where
                ctxBinder (_,specs) (name, _) (args, impls) = case lookup name specs of
                    (Just binds) => (zipWith paramBind args binds, mapValueMap paramInit impls)
                    Nothing => (map paramInit args, mapValueMap paramInit impls)
                cloTransformer specs _ _ _ cd@(MKCloData name target@(FunDef _ _ _ _) args miss _) = if not (specialisationDecider name args)
                    then (specs, (Nothing,Nil))
                    else case lookup name (snd specs) of
                        (Just _) => (specs, (Nothing,Nil)) -- is already specialized
                        Nothing => case specialise specs name (reduceInfos (extendWithUnknown miss args)) of
                            (nSpecs, sName, True) => (nSpecs, (Just (genMkClo ({function := sName} cd))), [(sName, target)])
                            (nSpecs, sName, False) => (nSpecs, (Just (genMkClo ({function := sName} cd))), Nil)
                cloTransformer specs _ _ _ _ = (specs, (Nothing,Nil))
                funTransformer specs _ _ _ fd@(MKFunData name target@(FunDef _ _ _ _) _ _ args _) = if not (specialisationDecider name args)
                    then (specs, (Nothing,Nil))
                    else case lookup name (snd specs) of
                        (Just _) => (specs, (Nothing,Nil)) -- is already specialized
                        Nothing => case specialise specs name (reduceInfos args) of
                            (nSpecs, sName, True) => (nSpecs, (Just (genFunCall ({function := sName} fd))), [(sName, target)])
                            (nSpecs, sName, False) => (nSpecs, (Just (genFunCall ({function := sName} fd))), Nil)
                funTransformer specs _ _ _ _ = (specs, (Nothing,Nil))


specialiseDefsIter : Maybe Nat -> Bool -> Nat -> SpecInfo -> List (CairoName, CairoDef) -> (SpecInfo, List (CairoName, CairoDef))
specialiseDefsIter _ _ Z specs allDefs = trace "Specialisation with Zero Iters does Nothing" (specs, allDefs)
specialiseDefsIter inlineSizeLimit tailBranchingActive (S n) specs allDefs = processRes $ specialiseDefsPass specs allDefs
   where processRes: (SpecInfo, List (CairoName, CairoDef)) -> (SpecInfo, List (CairoName, CairoDef))
         processRes (newSpecs, newDefs) = if (length $ keys $ snd specs) /= (length $ keys $ snd newSpecs)
            then if n == Z
                then (newSpecs, newDefs)
                else specialiseDefsIter inlineSizeLimit tailBranchingActive n newSpecs (inlineDefs inlineSizeLimit tailBranchingActive newDefs)
            else (newSpecs, newDefs)

--  We have a specDepth limit beacause otherwise
--  something stupid like: fun : List (a->b) -> c
--                         fun fs = if .. then fun ((\id -> id)::fs) else ..
--      will lead to an endless specification
export
specialiseDefs : List (CairoName, CairoDef) -> List (CairoName, CairoDef)
specialiseDefs allDefs = snd $ specialiseDefsPass initialSpecs allDefs
    where initialSpecs : SpecInfo
          initialSpecs = (empty, empty) -- we start with none

-- Makes an Inline Pass after each Specialising and repeat until nothing is specialized anymore
export
specialiseAndInlineDefs : Maybe Nat -> Bool -> Nat -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
specialiseAndInlineDefs inlineSizeLimit tailBranchingActive maxSpecIter allDefs = snd $ specialiseDefsIter inlineSizeLimit tailBranchingActive maxSpecIter initialSpecs allDefs
    where initialSpecs : SpecInfo
          initialSpecs = (empty, empty) -- we start with none
