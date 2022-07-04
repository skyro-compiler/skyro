module ABI.Generator

import ABI.Definitions
import Core.Context
import Data.List
import Data.SortedSet
import Data.SortedMap
import Core.Name.Namespace

import CommonDef
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import ABI.Specializer

import Debug.Trace

-- Todo: do the newtype and enum optimisation before this code otherwise it is idris specific

readExternal : Name
readExternal = NS (mkNamespace "ABI.Helper") (UN $ Basic "cairoreadptr")

writeExternal : Name
writeExternal = NS (mkNamespace "ABI.Helper") (UN $ Basic "cairowriteptr")

readTag : Name
readTag = NS (mkNamespace "ABI.Helper") (UN $ Basic "readtag")

makeTagless : Name
makeTagless = NS (mkNamespace "ABI.Helper") (UN $ Basic "maketagless")

tagBoundCheck : Name
tagBoundCheck = NS (mkNamespace "ABI.Helper") (UN $ Basic "boundedtag")

memCopy : Name
memCopy = NS (mkNamespace "ABI.Helper") (UN $ Basic "cairomemcopy")

segmentExternal : Name
segmentExternal = NS (mkNamespace "ABI.Helper") (UN $ Basic "cairocreateptr")

capturePtrExternal : Name
capturePtrExternal = NS (mkNamespace "ABI.Helper") (UN $ Basic "cairocaptureptr")

writeSegment : CairoReg -> CairoReg -> CairoReg -> List CairoInst
writeSegment ptrAfter ptrBefore value = [
        EXTPRIM [lengthReg] empty readTag [value],
        EXTPRIM [memPtr] empty writeExternal [ptrBefore, lengthReg],
        PROJECT memReg value 0,
        EXTPRIM [ptrAfter] empty memCopy [memReg, memPtr, lengthReg]
    ]
    where memReg : CairoReg
          memReg = prefixedReg ("mem_") value
          memPtr : CairoReg
          memPtr = prefixedReg ("ptr_mem_") value
          lengthReg : CairoReg
          lengthReg = prefixedReg ("len_") value
mutual
    writeComposite : CairoReg -> CairoReg -> CairoReg -> List ABIType -> List CairoInst
    writeComposite ptrAfter ptrBefore value fields =
            let (afterWriteReg, allWrites) = snd $ foldl (\(pos,(inPtr,acc)),typ => (pos+1,ptrReg pos,acc ++ (extractField inPtr (ptrReg pos) typ pos))) (0, (ptrBefore, Nil)) fields in
            allWrites ++ [ASSIGN ptrAfter afterWriteReg]
        where fieldReg : Nat -> CairoReg
              fieldReg pos = prefixedReg ("field_" ++ (show pos)) value
              ptrReg : Nat -> CairoReg
              ptrReg pos = prefixedReg ("ptr_" ++ (show pos)) ptrBefore
              extractField : CairoReg -> CairoReg -> ABIType -> Nat -> List CairoInst
              extractField inPtr outPtr typ pos = (PROJECT (fieldReg pos) value pos)::(writeValue outPtr inPtr (fieldReg pos) typ)

    writeValue : CairoReg -> CairoReg -> CairoReg -> ABIType -> List CairoInst
    writeValue ptrAfter ptrBefore value (NamedType name _) = [CALL [ptrAfter] empty (genEncoderName name) [ptrBefore, value]]
    writeValue ptrAfter ptrBefore value SegmentType = writeSegment ptrAfter ptrBefore value
    writeValue ptrAfter ptrBefore value (Variable name) = assert_total $ idris_crash "Spezialiser Should have removed this case"
    -- Idris has a newtype optimisation omits the wrapper
    writeValue ptrAfter ptrBefore value (TupleType [field]) = writeValue ptrAfter ptrBefore value field
    writeValue ptrAfter ptrBefore value (TupleType fields) = writeComposite ptrAfter ptrBefore value fields
    writeValue ptrAfter ptrBefore value (PrimType typ) = [OP castReg empty (Cast typ FeltType) [value], EXTPRIM [ptrAfter] empty writeExternal [ptrBefore, castReg]]
        where castReg : CairoReg
              castReg = prefixedReg "casted" value

genVariantEncoder : Name -> List (List ABIData) -> List (Name, CairoDef)
genVariantEncoder name ctrs = (genEncoderName name, FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] body)::ctrDefs
    where ctrBody : Int -> List ABIData -> List CairoInst
          ctrBody t fields = (EXTPRIM [Unassigned Nothing 0 0] empty writeExternal [CustomReg "retdata" Nothing, Const (I t)])::(writeComposite (Unassigned Nothing 1 0) (Unassigned Nothing 0 0) (Param 0) (map type fields)) ++ [RETURN [Unassigned Nothing 1 0] empty]
          ctrDef : Int -> List ABIData -> CairoDef
          ctrDef t fields = FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] (ctrBody t fields)
          ctrDefs : List (Name, CairoDef)
          ctrDefs = snd $ foldl (\(t,acc),fields => (t+1, acc ++ [(genCtrEncoderName t name, ctrDef t fields)])) (0, empty) ctrs
          ctrCalls : List (Int, List CairoInst)
          ctrCalls = snd $ foldl (\(t,acc), _ => (t+1, acc ++ [(t, [CALL [Unassigned Nothing 0 0] empty (genCtrEncoderName t name) [CustomReg "retdata" Nothing, Param 0]])])) (0, empty) ctrs
          body : List CairoInst
          body = (CASE (Param 0) ctrCalls Nothing)::[RETURN [Unassigned Nothing 0 0] empty]

-- Idris has an enum optimisation (makes it an Int)
-- Todo: shall we check it is in range?
--       in current compiler no problem as the last if in a case cascade is a catch all
--       however if passed in and out then a return processor could be surprised
genEnumEncoder : Name -> List (Name, CairoDef)
genEnumEncoder name = [(genEncoderName name, FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] body)]
    where body : List CairoInst
          body = writeValue (Unassigned Nothing 0 0) (CustomReg "retdata" Nothing) (Param 0) (PrimType IntType) ++ [RETURN [Unassigned Nothing 0 0] empty]

-- Todo: Generate A top level wrapper to be used from intrinsics: Any -> Felt*
--       Can be used in %runElab Derive to implement Serializer
--       just a wrapper that: let ptr = alloc() in let _ = encode ptr input in ptr (but dead code elim save)
-- Signature : (Felt*, Any) -> Felt*
--              Start, Input -> End
genEncoderDef : ABIEntry -> List (Name, CairoDef)
genEncoderDef (Struct name [] fields) = [(genEncoderName name, FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] body)]
    where body : List CairoInst
          body = writeValue (Unassigned Nothing 0 0) (CustomReg "retdata" Nothing) (Param 0) (TupleType (map type fields)) ++ [RETURN [Unassigned Nothing 0 0] empty]
-- Idris has an enum optimisation (makes it an Int)
genEncoderDef (Variant name [] ctrs) = if all isNil ctrs
    then genEnumEncoder name
    else genVariantEncoder name ctrs
genEncoderDef (Struct _ _ _) = assert_total $ idris_crash "Type arguments should have been removed by spezialiser"
genEncoderDef (Variant _ _ _) = assert_total $ idris_crash "Type arguments should have been removed by spezialiser"
genEncoderDef _ = assert_total $ idris_crash "Encoder is only supported for structs and variants"

readSegment : CairoReg -> CairoReg -> CairoReg -> List CairoInst
readSegment ptrAfter ptrBefore value = [
        EXTPRIM [memReg, lengthReg] empty readExternal [ptrBefore],
        EXTPRIM [value] empty makeTagless [lengthReg, memReg],
        OP ptrAfter empty (Add FeltType) [memReg, lengthReg]
    ]
    where memReg : CairoReg
          memReg = prefixedReg ("mem_") value
          lengthReg : CairoReg
          lengthReg = prefixedReg ("len_") value
mutual
    readComposite : CairoReg -> CairoReg -> CairoReg -> Maybe Int -> List ABIType -> List CairoInst
    readComposite ptrAfter ptrBefore value tag fields =
            let (ptrReg,(extractRegs, extractCode)) = foldl readField (ptrBefore, ([], [])) fields in
            extractCode ++ [ASSIGN ptrAfter ptrReg, MKCON value tag extractRegs]
        where genRegs : Nat -> (CairoReg,CairoReg)
              genRegs pos = (prefixedReg ("ptr_" ++ (show pos)) ptrBefore, prefixedReg ("field_" ++ (show pos)) value)
              readField : (CairoReg, (List CairoReg, List CairoInst)) -> ABIType -> (CairoReg, (List CairoReg, List CairoInst))
              readField (ptrReg, (vRegs,code)) typ = let (aReg, vReg) = genRegs (length vRegs) in (aReg, (vRegs ++ [vReg], code ++ (readValue aReg ptrReg vReg typ)))

    readValue : CairoReg -> CairoReg -> CairoReg -> ABIType -> List CairoInst
    readValue ptrAfter ptrBefore value (NamedType name _ ) = [CALL [ptrAfter, value] empty (genDecoderName name) [ptrBefore]]
    readValue ptrAfter ptrBefore value SegmentType = readSegment ptrAfter ptrBefore value
    readValue ptrAfter ptrBefore value (Variable name) = assert_total $ idris_crash "Spezialiser Should have removed this case"
    -- Idris has a newtype optimisation omits the wrapper
    readValue ptrAfter ptrBefore value (TupleType [field]) = readValue ptrAfter ptrBefore value field
    readValue ptrAfter ptrBefore value (TupleType fields) = readComposite ptrAfter ptrBefore value Nothing fields
    readValue ptrAfter ptrBefore value (PrimType typ) = [EXTPRIM [ptrAfter, rawReg] empty readExternal [ptrBefore], OP value empty (Cast FeltType typ) [rawReg]]
        where rawReg : CairoReg
              rawReg = prefixedReg "raw" value

genVariantDecoder : Name -> List (List ABIData) -> List (Name, CairoDef)
genVariantDecoder name ctrs = (genDecoderName name, FunDef [CustomReg "calldata" Nothing] empty [CustomReg "ptr" Nothing, CustomReg "value" Nothing] body)::ctrDefs
    where ptrAfterValueReg : CairoReg
          ptrAfterValueReg  = Unassigned Nothing 0 0
          valueReg : CairoReg
          valueReg = Unassigned Nothing 1 0
          tagReg : CairoReg
          tagReg = Unassigned Nothing 2 0
          ptrAfterTagReg : CairoReg
          ptrAfterTagReg  = Unassigned Nothing 3 0
          ctrBody : Int -> List ABIData -> List CairoInst
          ctrBody t fields = (readComposite ptrAfterValueReg (CustomReg "calldata" Nothing) valueReg (Just t) (map type fields)) ++ [RETURN [ptrAfterValueReg, valueReg] empty]
          ctrDef : Int -> List ABIData -> CairoDef
          ctrDef t fields = FunDef [CustomReg "calldata" Nothing] empty [CustomReg "ptr" Nothing, CustomReg "value" Nothing] (ctrBody t fields)
          ctrDefs : List (Name, CairoDef)
          ctrDefs = snd $ foldl (\(t,acc),fields => (t+1, acc ++ [(genCtrDecoderName t name, ctrDef t fields)])) (0, empty) ctrs
          ctrCalls : List (CairoConst, List CairoInst)
          ctrCalls = snd $ foldl (\(t,acc), _ => (t+1, acc ++ [(I t, [CALL [ptrAfterValueReg, valueReg] empty (genCtrDecoderName t name) [ptrAfterTagReg]])])) (0, empty) ctrs
          errorCase :  List CairoInst
          errorCase = [ASSIGN ptrAfterValueReg ptrAfterTagReg, ERROR valueReg ("Unexpected tag when deserializing value of type: "++(show name))]
          body : List CairoInst
          body = (EXTPRIM [ptrAfterTagReg, tagReg] empty readExternal [(CustomReg "calldata" Nothing)])::(CONSTCASE tagReg ctrCalls (Just errorCase))::[RETURN [ptrAfterValueReg, valueReg] empty]

-- Idris has an enum optimisation (makes it an Int)
-- Todo: check that it is in range or error
--       in current compiler no problem as the last if in a case cascade is a catch all
genEnumDecoder : Name -> Nat -> List (Name, CairoDef)
genEnumDecoder name numCtr = [(genDecoderName name, FunDef [CustomReg "calldata" Nothing] empty [CustomReg "ptr" Nothing, CustomReg "value" Nothing] body)]
    where body : List CairoInst
          body = readValue (Unassigned Nothing 0 0) (CustomReg "calldata" Nothing) (Unassigned Nothing 1 0) (PrimType FeltType) ++  [
            EXTPRIM [Unassigned Nothing 2 0] empty tagBoundCheck [Unassigned Nothing 1 0, Const (I $ cast numCtr)],
            RETURN [Unassigned Nothing 0 0, Unassigned Nothing 2 0] empty
          ]

-- Signature : Felt* -> (Felt*, Any)
--             Start -> End, Output
genDecoderDef : ABIEntry -> List (Name, CairoDef)
genDecoderDef (Struct name [] fields) = [(genDecoderName name, FunDef [CustomReg "calldata" Nothing] empty [CustomReg "ptr" Nothing, CustomReg "value" Nothing] body)]
   where body : List CairoInst
         body = readValue (Unassigned Nothing 0 0) (CustomReg "calldata" Nothing) (Unassigned Nothing 1 0) (TupleType (map type fields)) ++ [RETURN [Unassigned Nothing 0 0, Unassigned Nothing 1 0] empty]
-- Idris has an enum optimisation
genDecoderDef (Variant name [] ctrs) = if all isNil ctrs
    then genEnumDecoder name (length ctrs)
    else genVariantDecoder name ctrs

genDecoderDef (Struct _ _ _) = assert_total $ idris_crash "Type arguments should have been removed by spezialiser"
genDecoderDef (Variant _ _ _) = assert_total $ idris_crash "Type arguments should have been removed by spezialiser"
genDecoderDef _ = assert_total $ idris_crash "Decoder is only supported for structs"


genEntryPointBody : (ABIType -> Maybe Int) -> Name -> List ABIData -> Maybe ABIData -> List CairoInst
genEntryPointBody sizeF target params return = deserializationCode ++ callCode ++ serializationCode ++ retCode
    where deserializeRegs: List (CairoReg, CairoReg)
          deserializeRegs = snd $ foldl (\(cnt, acc), _ => (cnt+1,(Unassigned (Just "param") cnt 0, Unassigned (Just "param_ptr") cnt 0)::acc)) (0, []) params
          resultPtrReg : CairoReg
          resultPtrReg = Unassigned (Just "res_ptr") 0 0
          afterSerializePtr : CairoReg
          afterSerializePtr = Unassigned (Just "return_ptr") 0 0
          deserializationCode : List CairoInst
          deserializationCode = snd $ foldl (\(ptrBefore, code), (param, (value, ptrAfter)) => (ptrAfter, code ++ (readValue ptrAfter ptrBefore value param.type)) ) (CustomReg "calldata" Nothing, []) (zip params deserializeRegs)
          resultReg : CairoReg
          resultReg = Unassigned (Just "return") 0 0
          cairoCompReg : CairoReg
          cairoCompReg = Unassigned (Just "return") 1 0
          stateResReg : CairoReg
          stateResReg = Unassigned (Just "return") 2 0
          valueResReg : CairoReg
          valueResReg = Unassigned (Just "return") 3 0
          callCode : List CairoInst
          callCode = [
            CALL [cairoCompReg] empty target (map fst deserializeRegs),
            APPLY resultReg empty cairoCompReg (implicitReg syscall_builtin),
            PROJECT stateResReg resultReg 0,
            PROJECT valueResReg resultReg 1,
            EXTPRIM [resultPtrReg] empty segmentExternal []
          ]
          serializationCode : List CairoInst
          serializationCode = case return of
             Nothing => []
             (Just r) => writeValue afterSerializePtr resultPtrReg valueResReg r.type
          resSizePtrReg : CairoReg
          resSizePtrReg = Unassigned (Just "res_size") 0 0
          retCode : List CairoInst
          retCode = case return of
            Nothing => [RETURN [] (singleton syscall_builtin stateResReg)]
            -- (Just r) => [OP resSizePtrReg empty (Sub FeltType) [afterSerializePtr,resultPtrReg] ,RETURN [resSizePtrReg, resultPtrReg] (singleton syscall_builtin stateResReg)]
            (Just r) => case sizeF r.type of
                Nothing => [OP resSizePtrReg empty (Sub FeltType) [afterSerializePtr,resultPtrReg], RETURN [resSizePtrReg, resultPtrReg] (singleton syscall_builtin stateResReg)]
                (Just s) => [EXTPRIM [resSizePtrReg] empty capturePtrExternal [afterSerializePtr, Const $ F $ cast s], RETURN [resSizePtrReg, resultPtrReg] (singleton syscall_builtin stateResReg)]

sysPtrBuiltin : SortedMap LinearImplicit CairoReg
sysPtrBuiltin = singleton syscall_builtin (implicitReg syscall_builtin)

genEntryPoint : (ABIType -> Maybe Int) -> ABIEntry -> (Name, CairoDef)
genEntryPoint sizeF (StorageVar name) = (name, ExtFunDef ["@storage_var"] [] empty [CustomReg "res" (Just "felt")] [])
genEntryPoint sizeF (Event name) = (name, ExtFunDef ["@event"] [] empty [] [])
genEntryPoint sizeF (ExternalFunction name args rets) = (genEntryName name "Function", ExtFunDef ["@external", "@raw_input", "@raw_output"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [CustomReg "retdata_size" (Just "felt"), CustomReg "retdata" (Just "felt*")] (genEntryPointBody sizeF name args rets))
genEntryPoint sizeF (ViewFunction name args rets) = (genEntryName name "Function", ExtFunDef ["@view", "@raw_input", "@raw_output"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [CustomReg "retdata_size" (Just "felt"), CustomReg "retdata" (Just "felt*")] (genEntryPointBody sizeF name args rets))
genEntryPoint sizeF (Constructor name args) = (constructorName, ExtFunDef ["@constructor", "@raw_input"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [] (genEntryPointBody sizeF name args Nothing))
genEntryPoint sizeF (L1Handler name args) = (genEntryName name "L1Handler", ExtFunDef ["@l1_handler", "@raw_input"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [] (genEntryPointBody sizeF name args Nothing))
genEntryPoint _ _ = assert_total $ idris_crash "Entry point is only supported for functions"


indexedTopLevelTypes : List ABIEntry -> SortedMap Name ABIEntry
indexedTopLevelTypes [] = empty
indexedTopLevelTypes (e@(Struct name _ _)::xs) = insert name e (indexedTopLevelTypes xs)
indexedTopLevelTypes (e@(Variant name _ _)::xs) = insert name e (indexedTopLevelTypes xs)
indexedTopLevelTypes (_::xs) = indexedTopLevelTypes xs

maybeAdd : Maybe Int -> Maybe Int -> Maybe Int
maybeAdd (Just s1) (Just s2) = Just (s1+s2)
maybeAdd _ _ = Nothing

sizeMap : SortedMap Name ABIEntry -> SortedMap Name (Maybe Int)
sizeMap indexedEntries = foldl (\res, abi => snd $ sizeMapRec abi res) empty (values indexedEntries)
    where mutual
              typSizeRec : ABIType -> SortedMap Name (Maybe Int) -> (Maybe Int, SortedMap Name (Maybe Int))
              typSizeRec (PrimType IntegerType) processed = (Nothing, processed)
              typSizeRec (PrimType StringType) processed = (Nothing, processed)
              typSizeRec (PrimType _) processed = (Just 1, processed)
              typSizeRec SegmentType processed = (Nothing, processed)
              typSizeRec (Variable _) _ = assert_total $ idris_crash "Should have been eliminated by type spezialiser"
              typSizeRec (TupleType fields) processed = foldr (\t,(acc,p) => let (r,p2) = typSizeRec t p in (maybeAdd acc r,p2)) (Just 0, processed) fields
              typSizeRec (NamedType name []) processed = case lookup name indexedEntries of
                Nothing => (Nothing, processed)
                (Just e) => sizeMapRec e processed
              typSizeRec (NamedType _ _) _ = assert_total $ idris_crash "Should have been eliminated by type spezialiser"

              sizeMapRec : ABIEntry -> SortedMap Name (Maybe Int) -> (Maybe Int, SortedMap Name (Maybe Int))
              --       intermediary if all have zero args <-- for enums
              sizeMapRec (Variant name _ ctrs) processed =  case lookup name processed of
                -- Add Nothing first to terminate recursion of infinite variants
                Nothing => let recGuardedProcessed = insert name Nothing processed in
                           let (r,p) = if all isNil ctrs -- Todo: extend to all ctrs have same size
                                then (Just 1, processed)
                                else (Nothing, processed)
                           -- insert real value
                           in (r, insert name r p)
                (Just r) => (r, processed)
              sizeMapRec (Struct name [] fields) processed = case lookup name processed of
                -- Add Nothing first to terminate recursion of infinite records
                Nothing => let recGuardedProcessed = insert name Nothing processed in
                           let (r,p) = typSizeRec (TupleType (map type fields)) recGuardedProcessed in
                           -- insert real value
                           (r, insert name r p)
                (Just r) => (r, processed)
              sizeMapRec _ processed = (Nothing, processed)

getSize : SortedMap Name (Maybe Int) -> ABIType -> Maybe Int
getSize _ (PrimType IntegerType) = Nothing
getSize _ (PrimType StringType) = Nothing
getSize _ (PrimType _) = Just 1
getSize _ SegmentType = Nothing
getSize _ (Variable _) = assert_total $ idris_crash "Should have been eliminated by type spezialiser"
getSize sizeMapping (TupleType fields) = foldl maybeAdd (Just 0) (map (getSize sizeMapping) fields)
getSize sizeMapping (NamedType name _) = case lookup name sizeMapping of
    Nothing => Nothing
    (Just res) => res

generateAbiFunction : (ABIType -> Maybe Int) -> ABIEntry -> List (Name, CairoDef)
generateAbiFunction _ abi@(Struct _ _ _) = (genEncoderDef abi) ++ (genDecoderDef abi)
generateAbiFunction _ abi@(Variant _ _ _) = (genEncoderDef abi) ++ (genDecoderDef abi)
generateAbiFunction sizeF abi = [genEntryPoint sizeF abi]

generateSpecialisedAbiFunctions : List ABIEntry -> List (Name, CairoDef)
generateSpecialisedAbiFunctions entries = foldl (\acc, e => (generateAbiFunction sizeF e) ++ acc) [] entries
    where sizeF : ABIType -> Maybe Int
          sizeF = getSize (sizeMap (indexedTopLevelTypes entries))

public export
generateAbiFunctions : List ABIEntry -> List (Name, CairoDef)
generateAbiFunctions entries = generateSpecialisedAbiFunctions (spezializeEntries entries)
