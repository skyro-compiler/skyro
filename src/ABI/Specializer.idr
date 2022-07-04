module ABI.Specializer

import Core.Context
import ABI.Definitions
import Data.SortedSet
import Data.SortedMap
import Utils.Helpers
import CairoCode.CairoCode

import Debug.Trace

%hide Prelude.toList

resolveType : SortedMap String ABIType -> ABIType -> ABIType
resolveType bindings (Variable name) = case lookup name bindings of
    Nothing => assert_total $ idris_crash ("Can not generate names containing open variables: " ++ name)
    (Just t) => t
resolveType bindings (NamedType name args) = NamedType name (map (resolveType bindings) args)
resolveType _ t = t

specializedStringName : SortedMap String ABIType -> Bool -> ABIType -> String
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
-- Todo: is this the bad guy?
specializedStringName binds top (Variable name) = case lookup name binds of
    Nothing => assert_total $ idris_crash "Can not generate names containing open variables: " ++ name
    (Just t) => specializedStringName binds top t
specializedStringName binds _ (TupleType args) = "$("++ (separate "_" (map (specializedStringName binds False) args)) ++ ")"


specializedName : SortedMap String ABIType -> Bool -> ABIType -> Name
specializedName binds top type = MN (specializedStringName binds top type) 0


indexTypeEntries: List ABIEntry -> SortedMap Name ABIEntry
indexTypeEntries entries = fromList $ map extractName (filter isType entries)
    where extractName : ABIEntry -> (Name, ABIEntry)
          extractName e@(Struct name _ _) = (name,e)
          extractName e@(Variant name _ _) = (name,e)
          extractName _ = assert_total $ idris_crash "Can not happen"
          isType : ABIEntry -> Bool
          isType (Struct _ _ _) = True
          isType (Variant _ _ _) = True
          isType _ = False

integrateDataArgs : ABIData -> ABIData
integrateDataArgs (MkField fName t@(NamedType name args)) = MkField fName (NamedType (specializedName empty True t) Nil)
integrateDataArgs t = t

integrateTypeArgs : ABIType -> ABIType
integrateTypeArgs t@(NamedType name args) = NamedType (specializedName empty True t) Nil
integrateTypeArgs t = t

isNamedType : ABIType -> Bool
isNamedType (NamedType name args) = True
isNamedType _ = False

resolveAbiData : SortedMap String ABIType -> ABIData -> ABIData
resolveAbiData bindings (MkField name type) = MkField name (resolveType bindings type)

specialize : List ABIType -> ABIEntry -> (ABIEntry, List ABIType)
specialize applies (Struct name tvars args) = let resolvedArgs = map (resolveAbiData bindings) args in
        let dependencies = filter isNamedType (map type resolvedArgs) in
        (Struct rName empty (map specAbiData resolvedArgs), dependencies)
    where rName : Name
          rName = specializedName empty True (NamedType name applies)
          bindings : SortedMap String ABIType
          bindings = fromList (zip tvars applies)
          specAbiData : ABIData -> ABIData
          specAbiData (MkField name type) = MkField name (integrateTypeArgs type)

specialize applies (Variant name tvars ctrs) = let resolvedCtrs = map (map (resolveAbiData bindings)) ctrs in
        let dependencies = foldl (\acc,es => acc ++ (filter isNamedType (map type es))) Nil resolvedCtrs in
        (Variant rName empty (map (map specAbiData) resolvedCtrs), dependencies)
    where rName : Name
          rName = specializedName empty True (NamedType name applies)
          bindings : SortedMap String ABIType
          bindings = fromList (zip tvars applies)
          specAbiData : ABIData -> ABIData
          specAbiData (MkField name type) = MkField name (integrateTypeArgs type)
specialize _ _ = assert_total $ idris_crash "Can not spezialize ABI entries that are not types"

specializeType : SortedMap Name ABIEntry -> ABIType -> (ABIEntry, List ABIType)
specializeType index (NamedType name args) = case lookup name index of
    Nothing => assert_total $ idris_crash ("Can not spezialize ABI types that have no corresponding type entry: " ++ show name)
    (Just entry) => specialize args entry
specializeType index _ = assert_total $ idris_crash "Can not spezialize ABI entries that are not named types"

-- Todo: this is the endless one
spezializeTypes : SortedMap Name ABIEntry -> List ABIType -> List ABIEntry
spezializeTypes index deps = values $ recSpezializeTypes empty deps
    where recSpezializeTypes : SortedMap ABIType ABIEntry -> List ABIType -> SortedMap ABIType ABIEntry
          recSpezializeTypes processed Nil = processed
          recSpezializeTypes processed (cur::rest) = case lookup cur processed of
            (Just _) => recSpezializeTypes processed rest
            Nothing => let (res, newDeps) = specializeType index cur in
                recSpezializeTypes (insert cur res processed) (rest ++ newDeps)

export
spezializeEntries : List ABIEntry -> List ABIEntry
spezializeEntries entries = let (transformed, deps) = transformAndCollect entries empty in
    transformed ++ (spezializeTypes (indexTypeEntries entries) (toList deps))
    where transformAndCollect : List ABIEntry -> SortedSet ABIType -> (List ABIEntry, SortedSet ABIType)
          transformAndCollect Nil deps = (Nil, deps)
          transformAndCollect (x::xs) deps = let rest = transformAndCollect xs deps in case x of
                    (ExternalFunction name params ret) => let (rArgs, rRet) = (resolveArgs params, resolveRet ret) in
                        ((ExternalFunction name (integratedArgs rArgs) (integratedRet rRet))::(fst rest), union (depsFromArgsAndRet rArgs rRet) (snd rest))
                    (ViewFunction name params ret) => let (rArgs, rRet) = (resolveArgs params, resolveRet ret) in
                        ((ViewFunction name (integratedArgs rArgs) (integratedRet rRet))::(fst rest), union (depsFromArgsAndRet rArgs rRet) (snd rest))
                    (Constructor name params) => let rArgs = resolveArgs params in
                        ((Constructor name (integratedArgs rArgs))::(fst rest), union (depsFromArgs rArgs) (snd rest))
                    (L1Handler name params) => let rArgs = resolveArgs params in
                        ((L1Handler name (integratedArgs rArgs))::(fst rest), union (depsFromArgs rArgs) (snd rest))
                    (Struct _ _ _) => rest
                    (Variant _ _ _) => rest
                    (Event name) => mapFst (Event name ::) rest
                    (StorageVar name) => mapFst (StorageVar name ::) rest
            where resolveArgs : List ABIData -> List ABIData
                  resolveArgs params = map (resolveAbiData empty) params
                  integratedArgs : List ABIData -> List ABIData
                  integratedArgs params = map integrateDataArgs params
                  resolveRet : Maybe ABIData -> Maybe ABIData
                  resolveRet ret = maybeMap (resolveAbiData empty) ret
                  integratedRet : Maybe ABIData -> Maybe ABIData
                  integratedRet ret = maybeMap integrateDataArgs ret
                  depsFromArgs : List ABIData -> SortedSet ABIType
                  depsFromArgs rArgs = fromList $ filter isNamedType (map type rArgs)
                  depsFromArgsAndRet : List ABIData -> Maybe ABIData -> SortedSet ABIType
                  depsFromArgsAndRet rArgs Nothing = depsFromArgs rArgs
                  depsFromArgsAndRet rArgs (Just r) = if isNamedType (type r)
                    then insert (type r) (depsFromArgs rArgs)
                    else depsFromArgs rArgs
