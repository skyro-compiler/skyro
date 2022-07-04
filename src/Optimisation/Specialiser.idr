module Optimisation.Specialiser

import Data.SortedMap
import Data.SortedSet
import Data.String

import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
import Utils.Helpers

import Optimisation.StaticProcessing.IterativeBaseTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.StaticProcessing.StaticTransformer
import CommonDef

import Debug.Trace

%hide Prelude.toList

-- Todo: Shall we spezialise known tags in addition to known closure names?
--      It may be usefull in specialising dependently typed functions based on context, eliminating whole branches
--      Note: we already implicitly do this in case we have a record holding a closure

mutual
    -- todo: should only be used locally as it ignores many cases that can not appear in a spec form
    Eq StaticValue where
       (==) (Constructed c1) (Constructed c2) = assert_total (c1 == c2)
       (==) (Constructed _) _ = False
       (==) _ (Constructed _) = False
       (==) (Closure n1 a1) (Closure n2 a2) = n1 == n2 && (assert_total (a1 == a2))
       (==) (Closure _ _) _ = False
       (==) _ (Closure _ _) = False
       (==) _ _ = True

    -- todo: should only be used locally as it ignores the registers
    Eq StaticInfo where
       (==) (MKStaticInfo _ v1) (MKStaticInfo _ v2) = v1 == v2

    -- todo: should only be used locally as it ignores many cases that can not appear in a spec form
    Ord StaticValue where
       compare (Constructed c1) (Constructed c2) = assert_total $ compare (toList c1) (toList c2)
       compare (Constructed _) _ = GT
       compare _ (Constructed _) = LT
       compare (Closure n1 a1) (Closure n2 a2) = thenCompare (compare n1 n2) (assert_total $ compare a1 a2)
       compare (Closure _ _) _ = GT
       compare _ (Closure _ _) = LT
       compare _ _ = EQ

    -- todo: should only be used locally as it ignores the registers
    Ord StaticInfo where
        compare (MKStaticInfo _ v1) (MKStaticInfo _ v2) = compare v1 v2

specName : Name -> Int -> Name
specName name num = MN ("specialized__"++(cairoName name)) num

specDepth : Name -> Int
specDepth (MN innerName num) = if "specialized__" `isPrefixOf` innerName then 0 else num+1
specDepth _ = 0

-- todo: just closures for now, no other statics
containsKnownClosure : StaticInfo -> Bool
containsKnownClosure (MKStaticInfo _ (Constructed ctrs)) = any (any containsKnownClosure) (values ctrs)
containsKnownClosure (MKStaticInfo _ (Closure (Just _) _)) = True
containsKnownClosure _ = False

mutual
    reduceStaticValToEssential : StaticValue -> StaticValue
    reduceStaticValToEssential (Constructed ctrs) = let essentialCtrs = valueFilter (any isKnown) (mapValueMap (map reduceInfoToEssential) ctrs) in
            if isNil $ toList essentialCtrs then Unknown else Constructed essentialCtrs
        where isKnown : StaticInfo -> Bool
              isKnown (MKStaticInfo _ (Closure _ _)) = True
              isKnown (MKStaticInfo _ (Constructed ctrs)) = any (any isKnown) (values ctrs)
              isKnown _ = False

    reduceStaticValToEssential (Closure (Just nm) args) = Closure (Just nm) (map reduceInfoToEssential args)
    reduceStaticValToEssential _ = Unknown

    reduceInfoToEssential : StaticInfo -> StaticInfo
    reduceInfoToEssential (MKStaticInfo _ val) = MKStaticInfo empty (reduceStaticValToEssential val)

reduceInfos : List StaticInfo -> List StaticInfo
reduceInfos infos = map reduceInfoToEssential infos

-- Todo make Configurable
specDepthLimit : Int
specDepthLimit = 5

specialisationDecider : Name -> List StaticInfo -> Bool
specialisationDecider name args = specDepth name < specDepthLimit && any containsKnownClosure args

SpecInfo : Type
SpecInfo = (SortedMap Name (SortedMap (List StaticInfo) Int), SortedMap Name (List StaticInfo))

specialise : SpecInfo -> Name -> List StaticInfo -> (SpecInfo, Name, Bool)
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

--  We have a specDepth limit beacause otherwise
--  something stupid like: fun : List (a->b) -> c
--                         fun fs = if .. then fun ((\id -> id)::fs) else ..
--      will lead to an endless specification
export
specialiseDefs : List (Name, CairoDef) -> List (Name, CairoDef)
specialiseDefs allDefs = iterativeCallTransform @{config} initialSpecs allDefs
    where initialSpecs : SpecInfo
          initialSpecs = (empty, empty) -- we start with none
          paramInit : CairoReg -> StaticInfo
          paramInit reg = MKStaticInfo (singleton reg) Unknown
          paramBind : CairoReg -> StaticInfo -> StaticInfo
          paramBind reg (MKStaticInfo regs val) = (MKStaticInfo (insert reg regs) val)
          [config] IterativeTransformerConf SpecInfo where
                ctxBinder (_,specs) (name, _) (args, impls) = case lookup name specs of
                    (Just binds) => (zipWith paramBind args binds, mapValueMap paramInit impls)
                    Nothing => (map paramInit args, mapValueMap paramInit impls)
                cloTransformer specs _ _ cd@(MKCloData name target@(FunDef _ _ _ _) args miss _) = if not (specialisationDecider name args)
                    then (specs, (Nothing,Nil))
                    else case lookup name (snd specs) of
                        (Just _) => (specs, (Nothing,Nil)) -- is already specialized
                        Nothing => case specialise specs name (reduceInfos (extendWithUnknown miss args)) of
                            (nSpecs, sName, True) => (nSpecs, (Just (genMkClo ({function := sName} cd))), [(sName, target)])
                            (nSpecs, sName, False) => (nSpecs, (Just (genMkClo ({function := sName} cd))), Nil)
                cloTransformer specs _ _ _ = (specs, (Nothing,Nil))
                funTransformer specs _ _ fd@(MKFunData name target@(FunDef _ _ _ _) _ _ args _) = if not (specialisationDecider name args)
                    then (specs, (Nothing,Nil))
                    else case lookup name (snd specs) of
                        (Just _) => (specs, (Nothing,Nil)) -- is already specialized
                        Nothing => case specialise specs name (reduceInfos args) of
                            (nSpecs, sName, True) => (nSpecs, (Just (genFunCall ({function := sName} fd))), [(sName, target)])
                            (nSpecs, sName, False) => (nSpecs, (Just (genFunCall ({function := sName} fd))), Nil)
                funTransformer specs _ _ _ = (specs, (Nothing,Nil))
