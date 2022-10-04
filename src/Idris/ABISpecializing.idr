module Idris.ABISpecializing

import CairoCode.Name
import Data.SortedSet
import Data.SortedMap
import Data.List
import Utils.Helpers
import CairoCode.CairoCode

import Idris.ABI as Idris
import ABI.Definitions as Skyro

import Debug.Trace

%hide Prelude.toList

resolveType : SortedMap String Idris.ABIType -> Idris.ABIType -> Idris.ABIType
resolveType bindings (Variable name) = case lookup name bindings of
    Nothing => assert_total $ idris_crash ("Can not generate names containing open variables: " ++ name)
    (Just t) => t
resolveType bindings (NamedType name args) = NamedType name (map (resolveType bindings) args)
resolveType _ t = t

-- Todo: Find a better solution now here (similar to other spezialiser with a number)
specializedStringName : SortedMap String Idris.ABIType -> Bool -> Idris.ABIType -> String
specializedStringName _ _ (PrimType cct) = case cct of
    IntType => "$Prim_Int"
    Int8Type => "$Prim_Int8"
    Int16Type => "$Prim_Int16"
    Int32Type => "$Prim_Int32"
    Int64Type => "$Prim_Int64"
    FeltType => "$Prim_Felt"
    IntegerType => "$Prim_Integer"
    Bits8Type => "$Prim_UInt8"
    Bits16Type => "$Prim_UInt16"
    Bits32Type => "$Prim_UInt32"
    StringType => "$Prim_String"
    CharType => "$Prim_Char"
    _ => assert_total $ idris_crash ("Unsupported ABI primitive type: " ++ (show cct))
specializedStringName _ _ SegmentType = "$Prim_Segment"
specializedStringName _ _ (NamedType name []) = show name
specializedStringName binds True (NamedType name args) = show name ++ "_" ++ (separate "_" (map (specializedStringName binds False) args))
specializedStringName binds False (NamedType name args) = "("++ show name ++ "_" ++ (separate "_" (map (specializedStringName binds False) args)) ++ ")"
specializedStringName binds top (Variable name) = case lookup name binds of
    Nothing => assert_total $ idris_crash "Can not generate names containing open variables: " ++ name
    (Just t) => specializedStringName binds top t
specializedStringName binds _ (TupleType args) = "$("++ (separate "_" (map (specializedStringName binds False) args)) ++ ")"

-- Todo: I do not like: can we just increment an apply counter instead and remember in a map?
specializedName : SortedMap String Idris.ABIType -> Bool -> Idris.ABIType -> CairoName
specializedName binds top type = extendNamePlain "applied" (nameFromString (specializedStringName binds top type))

indexTypeEntries: List Idris.ABIEntry -> SortedMap CairoName Idris.ABIEntry
indexTypeEntries entries = fromList $ map extractName (filter isType entries)
    where extractName : Idris.ABIEntry -> (CairoName, Idris.ABIEntry)
          extractName e@(Struct name _ _) = (name,e)
          extractName e@(Variant name _ _) = (name,e)
          extractName _ = assert_total $ idris_crash "Can not happen"
          isType : Idris.ABIEntry -> Bool
          isType (Struct _ _ _) = True
          isType (Variant _ _ _) = True
          isType _ = False

integrateDataArgs : Idris.ABIData -> Idris.ABIData
integrateDataArgs (MkField fName t@(NamedType name args)) = MkField fName (NamedType (specializedName empty True t) Nil)
integrateDataArgs t = t

integrateTypeArgs : Idris.ABIType -> Idris.ABIType
integrateTypeArgs t@(NamedType name args) = NamedType (specializedName empty True t) Nil
integrateTypeArgs t = t

isNamedType : Idris.ABIType -> Bool
isNamedType (NamedType name args) = True
isNamedType _ = False

resolveAbiData : SortedMap String Idris.ABIType -> Idris.ABIData -> Idris.ABIData
resolveAbiData bindings (MkField name type) = MkField name (resolveType bindings type)

specialize : List Idris.ABIType -> Idris.ABIEntry -> (Idris.ABIEntry, List Idris.ABIType)
specialize applies (Struct name tvars args) = let resolvedArgs = map (resolveAbiData bindings) args in
        let dependencies = filter isNamedType (map type resolvedArgs) in
        (Struct rName empty (map specAbiData resolvedArgs), dependencies)
    where rName : CairoName
          rName = specializedName empty True (NamedType name applies)
          bindings : SortedMap String Idris.ABIType
          bindings = fromList (zip tvars applies)
          specAbiData : Idris.ABIData -> Idris.ABIData
          specAbiData (MkField name type) = MkField name (integrateTypeArgs type)

specialize applies (Variant name tvars ctrs) = let resolvedCtrs = map (map (resolveAbiData bindings)) ctrs in
        let dependencies = foldl (\acc,es => acc ++ (filter isNamedType (map type es))) (the (List Idris.ABIType) Nil) resolvedCtrs in
        (Variant rName empty (map (map specAbiData) resolvedCtrs), dependencies)
    where rName : CairoName
          rName = specializedName empty True (NamedType name applies)
          bindings : SortedMap String Idris.ABIType
          bindings = fromList (zip tvars applies)
          specAbiData : Idris.ABIData -> Idris.ABIData
          specAbiData (MkField name type) = MkField name (integrateTypeArgs type)
specialize _ _ = assert_total $ idris_crash "Can not spezialize ABI entries that are not types"

specializeType : SortedMap CairoName Idris.ABIEntry -> Idris.ABIType -> (Idris.ABIEntry, List Idris.ABIType)
specializeType index (NamedType name args) = case lookup name index of
    Nothing => assert_total $ idris_crash ("Can not spezialize ABI types that have no corresponding type entry: " ++ show name)
    (Just entry) => specialize args entry
specializeType index _ = assert_total $ idris_crash "Can not spezialize ABI entries that are not named types"

-- Todo: this is the endless one
spezializeTypes : SortedMap CairoName Idris.ABIEntry -> List Idris.ABIType -> List Idris.ABIEntry
spezializeTypes index deps = values $ recSpezializeTypes empty deps
    where recSpezializeTypes : SortedMap Idris.ABIType Idris.ABIEntry -> List Idris.ABIType -> SortedMap Idris.ABIType Idris.ABIEntry
          recSpezializeTypes processed Nil = processed
          recSpezializeTypes processed (cur::rest) = case lookup cur processed of
            (Just _) => recSpezializeTypes processed rest
            Nothing => let (res, newDeps) = specializeType index cur in
                recSpezializeTypes (insert cur res processed) (rest ++ newDeps)

toSkyroABIType: Idris.ABIType -> Skyro.ABIType
toSkyroABIType (PrimType const) = Skyro.PrimType const
toSkyroABIType (NamedType name []) = Skyro.NamedType name
toSkyroABIType (TupleType types) = Skyro.TupleType (map toSkyroABIType types)
toSkyroABIType SegmentType = Skyro.SegmentType
toSkyroABIType _ = assert_total $ idris_crash "Should have been eliminated"

toSkyroABIData: Idris.ABIData -> Skyro.ABIData
toSkyroABIData (MkField name type) = Skyro.MkField name (toSkyroABIType type)

toSkyroABIEntry: Idris.ABIEntry -> Skyro.ABIEntry
toSkyroABIEntry (Struct name [] fields) = Skyro.Struct name (map toSkyroABIData fields)
toSkyroABIEntry (Variant name [] ctrs) = Skyro.Variant name (map (map toSkyroABIData) ctrs)
toSkyroABIEntry (ExternalFunction name False args ret) = Skyro.ExternalFunction name (map toSkyroABIData args) (maybeMap toSkyroABIData ret)
toSkyroABIEntry (ExternalFunction name True args ret) = Skyro.AbstractFunction name (map toSkyroABIData args) (maybeMap toSkyroABIData ret)
toSkyroABIEntry (ViewFunction name False args ret) = Skyro.ViewFunction name (map toSkyroABIData args) (maybeMap toSkyroABIData ret)
toSkyroABIEntry (ViewFunction name True args ret) = Skyro.AbstractFunction name (map toSkyroABIData args) (maybeMap toSkyroABIData ret)
toSkyroABIEntry (Constructor name args) = Skyro.Constructor name (map toSkyroABIData args)
toSkyroABIEntry (Event name) = Skyro.Event name
toSkyroABIEntry (L1Handler name args) = Skyro.L1Handler name (map toSkyroABIData args)
toSkyroABIEntry (StorageVar name) = Skyro.StorageVar name
toSkyroABIEntry _ = assert_total $ idris_crash "Should have been eliminated"

export
spezializeEntries : List Idris.ABIEntry -> List Skyro.ABIEntry
spezializeEntries entries = let (transformed, deps) = transformAndCollect entries empty in
    map toSkyroABIEntry (transformed ++ (spezializeTypes (indexTypeEntries entries) (toList deps)))
    where transformAndCollect : List Idris.ABIEntry -> SortedSet Idris.ABIType -> (List Idris.ABIEntry, SortedSet Idris.ABIType)
          transformAndCollect Nil deps = (Nil, deps)
          transformAndCollect (x::xs) deps = let rest = transformAndCollect xs deps in case x of
                    (ExternalFunction name abstract params ret) => let (rArgs, rRet) = (resolveArgs params, resolveRet ret) in
                        ((ExternalFunction name abstract (integratedArgs rArgs) (integratedRet rRet))::(fst rest), union (depsFromArgsAndRet rArgs rRet) (snd rest))
                    (ViewFunction name abstract params ret) => let (rArgs, rRet) = (resolveArgs params, resolveRet ret) in
                        ((ViewFunction name abstract (integratedArgs rArgs) (integratedRet rRet))::(fst rest), union (depsFromArgsAndRet rArgs rRet) (snd rest))
                    (Constructor name params) => let rArgs = resolveArgs params in
                        ((Constructor name (integratedArgs rArgs))::(fst rest), union (depsFromArgs rArgs) (snd rest))
                    (L1Handler name params) => let rArgs = resolveArgs params in
                        ((L1Handler name (integratedArgs rArgs))::(fst rest), union (depsFromArgs rArgs) (snd rest))
                    (Struct _ _ _) => rest
                    (Variant _ _ _) => rest
                    (Event name) => mapFst (Event name ::) rest
                    (StorageVar name) => mapFst (StorageVar name ::) rest
            where resolveArgs : List Idris.ABIData -> List Idris.ABIData
                  resolveArgs params = map (resolveAbiData empty) params
                  integratedArgs : List Idris.ABIData -> List Idris.ABIData
                  integratedArgs params = map integrateDataArgs params
                  resolveRet : Maybe Idris.ABIData -> Maybe Idris.ABIData
                  resolveRet ret = maybeMap (resolveAbiData empty) ret
                  integratedRet : Maybe Idris.ABIData -> Maybe Idris.ABIData
                  integratedRet ret = maybeMap integrateDataArgs ret
                  depsFromArgs : List Idris.ABIData -> SortedSet Idris.ABIType
                  depsFromArgs rArgs = fromList $ filter isNamedType (map type rArgs)
                  depsFromArgsAndRet : List Idris.ABIData -> Maybe Idris.ABIData -> SortedSet Idris.ABIType
                  depsFromArgsAndRet rArgs Nothing = depsFromArgs rArgs
                  depsFromArgsAndRet rArgs (Just r) = if isNamedType (type r)
                    then insert (type r) (depsFromArgs rArgs)
                    else depsFromArgs rArgs
