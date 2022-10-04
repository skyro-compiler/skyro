module ABI.Generator

import ABI.Definitions
import CairoCode.Name
import Data.List
import Data.SortedSet
import Data.SortedMap

import CommonDef
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils

import Debug.Trace

-- Todo: do the newtype and enum optimisation before this code otherwise it is idris specific
-- Todo: alt - we can have it turn on and off over a parameter

readExternal : CairoName
readExternal = Extension "external" Nothing (fullName ["ABI", "Helper"] "cairoreadptr")

writeExternal : CairoName
writeExternal = Extension "external" Nothing (fullName ["ABI", "Helper"] "cairowriteptr")

readTag : CairoName
readTag = Extension "external" Nothing (fullName ["ABI", "Helper"] "readtag")

makeTagless : CairoName
makeTagless = Extension "external" Nothing (fullName ["ABI", "Helper"] "maketagless")

tagBoundCheck : CairoName
tagBoundCheck = Extension "external" Nothing (fullName ["ABI", "Helper"] "boundedtag")

memCopy : CairoName
memCopy = Extension "external" Nothing (fullName ["ABI", "Helper"] "cairomemcopy")

bigintLen : CairoName
bigintLen = Extension "external" Nothing (fullName ["ABI", "Helper"] "bigintlength")

bigintSign : CairoName
bigintSign = Extension "external" Nothing (fullName ["ABI", "Helper"] "bigintsign")

segmentExternal : CairoName
segmentExternal = Extension "external" Nothing (fullName ["ABI", "Helper"] "cairocreateptr")

capturePtrExternal : CairoName
capturePtrExternal = Extension "external" Nothing (fullName ["ABI", "Helper"] "cairocaptureptr")

arrayEncoder : CairoName
arrayEncoder = extendNamePlain "encoder" (extendNamePlain "generated" (fullName ["ABI", "Helper"] "writeMany"))

arrayDecoder : CairoName
arrayDecoder = extendNamePlain "encoder" (extendNamePlain "generated" (fullName ["ABI", "Helper"] "readMany"))

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

writeBigInt : CairoReg -> CairoReg -> CairoReg -> List CairoInst
writeBigInt ptrAfter ptrBefore value = [
            EXTPRIM [signReg] empty readTag [value],
            EXTPRIM [ptrAfterSign] empty writeExternal [ptrBefore, signReg],
            EXTPRIM [lenReg] empty bigintLen [value],
            EXTPRIM [ptrAfterLen] empty writeExternal [ptrAfterSign, lenReg],
            PROJECT bigPtr value 0,
            EXTPRIM [ptrAfter] empty memCopy [bigPtr, ptrAfterLen, lenReg]
        ]
    where signReg : CairoReg
          signReg = prefixedReg ("sign_") value
          lenReg : CairoReg
          lenReg = prefixedReg ("len_") value
          bigPtr : CairoReg
          bigPtr = prefixedReg ("big_") value
          ptrAfterSign : CairoReg
          ptrAfterSign = prefixedReg ("sign_") ptrAfter
          ptrAfterLen : CairoReg
          ptrAfterLen = prefixedReg ("len_") ptrAfter

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
    writeValue ptrAfter ptrBefore value (NamedType name) = [CALL [ptrAfter] empty (genEncoderName name) [ptrBefore, value]]
    writeValue ptrAfter ptrBefore value SegmentType = writeSegment ptrAfter ptrBefore value
    -- Idris has a newtype optimisation omits the wrapper
    writeValue ptrAfter ptrBefore value (TupleType [field]) = writeValue ptrAfter ptrBefore value field
    writeValue ptrAfter ptrBefore value (TupleType fields) = writeComposite ptrAfter ptrBefore value fields
    writeValue ptrAfter ptrBefore value (PrimType IntegerType) = writeBigInt ptrAfter ptrBefore value
    writeValue ptrAfter ptrBefore value (PrimType typ) = [OP castReg empty (Cast typ FeltType) [value], EXTPRIM [ptrAfter] empty writeExternal [ptrBefore, castReg]]
        where castReg : CairoReg
              castReg = prefixedReg "casted" value

genVariantEncoder : CairoName -> List (List ABIData) -> List (CairoName, CairoDef)
genVariantEncoder name ctrs = (genEncoderName name, FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] body)::ctrDefs
    where ctrBody : Int -> List ABIData -> List CairoInst
          ctrBody t fields = (EXTPRIM [Unassigned Nothing 0 0] empty writeExternal [CustomReg "retdata" Nothing, Const (I t)])::(writeComposite (Unassigned Nothing 1 0) (Unassigned Nothing 0 0) (Param 0) (map type fields)) ++ [RETURN [Unassigned Nothing 1 0] empty]
          ctrDef : Int -> List ABIData -> CairoDef
          ctrDef t fields = FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] (ctrBody t fields)
          ctrDefs : List (CairoName, CairoDef)
          ctrDefs = snd $ foldl (\(t,acc),fields => (t+1, acc ++ [(genCtrEncoderName t name, ctrDef t fields)])) (0, empty) ctrs
          ctrCalls : List (Int, List CairoInst)
          ctrCalls = snd $ foldl (\(t,acc), _ => (t+1, acc ++ [(t, [CALL [Unassigned Nothing 0 0] empty (genCtrEncoderName t name) [CustomReg "retdata" Nothing, Param 0]])])) (0, empty) ctrs
          body : List CairoInst
          body = (CASE (Param 0) ctrCalls Nothing)::[RETURN [Unassigned Nothing 0 0] empty]

-- Idris has an enum optimisation (makes it an Int)
-- Todo: shall we check it is in range?
--       in current compiler no problem as the last if in a case cascade is a catch all
--       however if passed in and out then a return processor could be surprised
genEnumEncoder : CairoName -> List (CairoName, CairoDef)
genEnumEncoder name = [(genEncoderName name, FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] body)]
    where body : List CairoInst
          body = writeValue (Unassigned Nothing 0 0) (CustomReg "retdata" Nothing) (Param 0) (PrimType IntType) ++ [RETURN [Unassigned Nothing 0 0] empty]

-- Todo: Generate A top level wrapper to be used from intrinsics: Any -> Felt*
--       Can be used in %runElab Derive to implement Serializer
--       just a wrapper that: let ptr = alloc() in let _ = encode ptr input in ptr (but dead code elim save)
-- Signature : (Felt*, Any) -> Felt*
--              Start, Input -> End
genEncoderDef : ABIEntry -> List (CairoName, CairoDef)
genEncoderDef (Struct name fields) = [(genEncoderName name, FunDef [CustomReg "retdata" Nothing, Param 0] empty [CustomReg "ptr" Nothing] body)]
    where body : List CairoInst
          body = writeValue (Unassigned Nothing 0 0) (CustomReg "retdata" Nothing) (Param 0) (TupleType (map type fields)) ++ [RETURN [Unassigned Nothing 0 0] empty]
-- Idris has an enum optimisation (makes it an Int)
genEncoderDef (Variant name ctrs) = if all isNil ctrs
    then genEnumEncoder name
    else genVariantEncoder name ctrs
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

readBigInt : CairoReg -> CairoReg -> CairoReg -> List CairoInst
readBigInt ptrAfter ptrBefore value = [
            EXTPRIM [ptrAfterSign, signReg] empty readExternal [ptrBefore],
            -- Todo: check sign is valid
            EXTPRIM [ptrAfterLen, lenReg] empty readExternal [ptrAfterSign],
            EXTPRIM [segPtr] empty segmentExternal [],
            EXTPRIM [newSegPtr] empty memCopy [ptrAfterLen, segPtr, lenReg],
            EXTPRIM [finSegPtr] empty writeExternal [newSegPtr, Const (F (-1))],
            OP ptrAfter empty (Add FeltType) [ptrAfterLen, lenReg],
            EXTPRIM [bigPtr] empty capturePtrExternal [finSegPtr, segPtr], -- ensures the two writes are not eliminated
            EXTPRIM [value] empty makeTagless [signReg,bigPtr]
        ]
    where ptrAfterSign : CairoReg
          ptrAfterSign = prefixedReg ("sign_") ptrAfter
          ptrAfterLen : CairoReg
          ptrAfterLen = prefixedReg ("len_") ptrAfter
          signReg : CairoReg
          signReg = prefixedReg ("sign_") value
          lenReg : CairoReg
          lenReg = prefixedReg ("len_") value
          segPtr : CairoReg
          segPtr = prefixedReg ("seg_") value
          bigPtr : CairoReg
          bigPtr = prefixedReg ("big_") value
          newSegPtr : CairoReg
          newSegPtr = prefixedReg ("new_") segPtr
          finSegPtr : CairoReg
          finSegPtr = prefixedReg ("fin_") segPtr

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
    readValue ptrAfter ptrBefore value (NamedType name) = [CALL [ptrAfter, value] empty (genDecoderName name) [ptrBefore]]
    readValue ptrAfter ptrBefore value SegmentType = readSegment ptrAfter ptrBefore value
    -- Idris has a newtype optimisation omits the wrapper -- Todo: move into idris have an ApplyIdrisOptimizer pass
    readValue ptrAfter ptrBefore value (TupleType [field]) = readValue ptrAfter ptrBefore value field
    readValue ptrAfter ptrBefore value (TupleType fields) = readComposite ptrAfter ptrBefore value Nothing fields
    readValue ptrAfter ptrBefore value (PrimType IntegerType) = readBigInt ptrAfter ptrBefore value
    readValue ptrAfter ptrBefore value (PrimType typ) = [EXTPRIM [ptrAfter, rawReg] empty readExternal [ptrBefore], OP value empty (Cast FeltType typ) [rawReg]]
        where rawReg : CairoReg
              rawReg = prefixedReg "raw" value

genVariantDecoder : CairoName -> List (List ABIData) -> List (CairoName, CairoDef)
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
          ctrDefs : List (CairoName, CairoDef)
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
genEnumDecoder : CairoName -> Nat -> List (CairoName, CairoDef)
genEnumDecoder name numCtr = [(genDecoderName name, FunDef [CustomReg "calldata" Nothing] empty [CustomReg "ptr" Nothing, CustomReg "value" Nothing] body)]
    where body : List CairoInst
          body = readValue (Unassigned Nothing 0 0) (CustomReg "calldata" Nothing) (Unassigned Nothing 1 0) (PrimType FeltType) ++  [
            EXTPRIM [Unassigned Nothing 2 0] empty tagBoundCheck [Unassigned Nothing 1 0, Const (I $ cast numCtr)],
            RETURN [Unassigned Nothing 0 0, Unassigned Nothing 2 0] empty
          ]

-- Signature : Felt* -> (Felt*, Any)
--             Start -> End, Output
genDecoderDef : ABIEntry -> List (CairoName, CairoDef)
genDecoderDef (Struct name fields) = [(genDecoderName name, FunDef [CustomReg "calldata" Nothing] empty [CustomReg "ptr" Nothing, CustomReg "value" Nothing] body)]
   where body : List CairoInst
         body = readValue (Unassigned Nothing 0 0) (CustomReg "calldata" Nothing) (Unassigned Nothing 1 0) (TupleType (map type fields)) ++ [RETURN [Unassigned Nothing 0 0, Unassigned Nothing 1 0] empty]
-- Idris has an enum optimisation
genDecoderDef (Variant name ctrs) = if all isNil ctrs
    then genEnumDecoder name (length ctrs)
    else genVariantDecoder name ctrs
genDecoderDef _ = assert_total $ idris_crash "Decoder is only supported for structs"


genEntryPointBody : (ABIType -> Maybe Int) -> CairoName -> List ABIData -> Maybe ABIData -> List CairoInst
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

genEntryPoint : (ABIType -> Maybe Int) -> ABIEntry -> (CairoName, CairoDef)
genEntryPoint sizeF (StorageVar name) = (name, ExtFunDef ["@storage_var"] [] empty [CustomReg "res" (Just "felt")] [])
genEntryPoint sizeF (Event name) = (name, ExtFunDef ["@event"] [] empty [] [])
genEntryPoint sizeF (ExternalFunction name args rets) = (genEntryName name "Function", ExtFunDef ["@external", "@raw_input", "@raw_output"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [CustomReg "retdata_size" (Just "felt"), CustomReg "retdata" (Just "felt*")] (genEntryPointBody sizeF name args rets))
genEntryPoint sizeF (ViewFunction name args rets) = (genEntryName name "Function", ExtFunDef ["@view", "@raw_input", "@raw_output"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [CustomReg "retdata_size" (Just "felt"), CustomReg "retdata" (Just "felt*")] (genEntryPointBody sizeF name args rets))
genEntryPoint sizeF (Constructor name args) = (constructorName, ExtFunDef ["@constructor", "@raw_input"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [] (genEntryPointBody sizeF name args Nothing))
genEntryPoint sizeF (AbstractFunction name args rets) = (name, ExtFunDef ["@contract_interface"] [] empty [] [])
genEntryPoint sizeF (L1Handler name args) = (genEntryName name "L1Handler", ExtFunDef ["@l1_handler", "@raw_input"] [CustomReg "selector" (Just "felt"), CustomReg "calldata_size" (Just "felt"), CustomReg "calldata" (Just "felt*")] sysPtrBuiltin [] (genEntryPointBody sizeF name args Nothing))
genEntryPoint _ _ = assert_total $ idris_crash "Entry point is only supported for functions"


indexedTopLevelTypes : List ABIEntry -> SortedMap CairoName ABIEntry
indexedTopLevelTypes [] = empty
indexedTopLevelTypes (e@(Struct name _)::xs) = insert name e (indexedTopLevelTypes xs)
indexedTopLevelTypes (e@(Variant name _)::xs) = insert name e (indexedTopLevelTypes xs)
indexedTopLevelTypes (_::xs) = indexedTopLevelTypes xs

maybeAdd : Maybe Int -> Maybe Int -> Maybe Int
maybeAdd (Just s1) (Just s2) = Just (s1+s2)
maybeAdd _ _ = Nothing

sizeMap : SortedMap CairoName ABIEntry -> SortedMap CairoName (Maybe Int)
sizeMap indexedEntries = foldl (\res, abi => snd $ sizeMapRec abi res) empty (values indexedEntries)
    where mutual
              typSizeRec : ABIType -> SortedMap CairoName (Maybe Int) -> (Maybe Int, SortedMap CairoName (Maybe Int))
              typSizeRec (PrimType IntegerType) processed = (Nothing, processed)
              typSizeRec (PrimType StringType) processed = (Nothing, processed)
              typSizeRec (PrimType _) processed = (Just 1, processed)
              typSizeRec SegmentType processed = (Nothing, processed)
              typSizeRec (TupleType fields) processed = foldr (\t,(acc,p) => let (r,p2) = typSizeRec t p in (maybeAdd acc r,p2)) (Just 0, processed) fields
              typSizeRec (NamedType name) processed = case lookup name indexedEntries of
                Nothing => (Nothing, processed)
                (Just e) => sizeMapRec e processed

              sizeMapRec : ABIEntry -> SortedMap CairoName (Maybe Int) -> (Maybe Int, SortedMap CairoName (Maybe Int))
              --       intermediary if all have zero args <-- for enums
              sizeMapRec (Variant name ctrs) processed =  case lookup name processed of
                -- Add Nothing first to terminate recursion of infinite variants
                Nothing => let recGuardedProcessed = insert name Nothing processed in
                           let (r,p) = if all isNil ctrs -- Todo: extend to all ctrs have same size
                                then (Just 1, processed)
                                else (Nothing, processed)
                           -- insert real value
                           in (r, insert name r p)
                (Just r) => (r, processed)
              sizeMapRec (Struct name fields) processed = case lookup name processed of
                -- Add Nothing first to terminate recursion of infinite records
                Nothing => let recGuardedProcessed = insert name Nothing processed in
                           let (r,p) = typSizeRec (TupleType (map type fields)) recGuardedProcessed in
                           -- insert real value
                           (r, insert name r p)
                (Just r) => (r, processed)
              sizeMapRec _ processed = (Nothing, processed)

getSize : SortedMap CairoName (Maybe Int) -> ABIType -> Maybe Int
getSize _ (PrimType IntegerType) = Nothing
getSize _ (PrimType StringType) = Nothing
getSize _ (PrimType _) = Just 1
getSize _ SegmentType = Nothing
getSize sizeMapping (TupleType fields) = foldl maybeAdd (Just 0) (map (getSize sizeMapping) fields)
getSize sizeMapping (NamedType name) = case lookup name sizeMapping of
    Nothing => Nothing
    (Just res) => res

generateSegmentEncoder : List ABIType -> CairoDef
generateSegmentEncoder typs = FunDef params empty [CustomReg "val" Nothing] body
    where params : List CairoReg
          params = reverse $ snd $ foldl (\(n,ps),_ => (n+1, (Param n)::ps)) (0, Nil) typs
          beforePtr : CairoReg
          beforePtr = Unassigned Nothing 0 0
          segLenReg : CairoReg
          segLenReg = Unassigned Nothing 1 0
          segReg : CairoReg
          segReg = Unassigned Nothing 2 0
          updatedPtrs : List CairoReg
          updatedPtrs = reverse $ snd $ foldl (\(n,ps),_ => (n+1, (Unassigned Nothing n 0)::ps)) (3, Nil) typs
          write : (CairoReg, List CairoInst) -> (ABIType, (CairoReg, CairoReg)) -> (CairoReg, List CairoInst)
          write (activePtr, acc) (typ, (paramPtr, resPtr)) = (resPtr, acc ++ writeValue resPtr activePtr paramPtr typ)
          writes : (CairoReg, List CairoInst)
          writes = foldl write (beforePtr, Nil) (zip typs (zip params updatedPtrs))
          body : List CairoInst
          body = let (afterPtr, allWrites) = writes in (EXTPRIM [beforePtr] empty segmentExternal [])::allWrites ++ [
             OP segLenReg empty (Sub FeltType) [afterPtr, beforePtr],
             EXTPRIM [segReg] empty makeTagless [segLenReg, beforePtr],
             RETURN [segReg] empty
          ]

generateSegmentDecoder : ABIType -> CairoDef
generateSegmentDecoder typ = FunDef [Param 0] empty [CustomReg "val" Nothing] body
    where memReg : CairoReg
          memReg = Unassigned Nothing 0 0
          valReg : CairoReg
          valReg = Unassigned Nothing 1 0
          afterPtr : CairoReg
          afterPtr = Unassigned Nothing 2 0
          decLenReg : CairoReg
          decLenReg = Unassigned Nothing 3 0
          segLenReg : CairoReg
          segLenReg = Unassigned Nothing 4 0
          lenDiffReg : CairoReg
          lenDiffReg = Unassigned Nothing 5 0
          errorReg : CairoReg
          errorReg = Unassigned Nothing 6 1
          error : List CairoInst
          error = [ERROR errorReg "Decoding Error", RETURN [errorReg] empty]
          success : List CairoInst
          success = [RETURN [valReg] empty]
          body : List CairoInst
          body = (PROJECT memReg (Param 0) 0)::(readValue afterPtr memReg valReg typ) ++ [
            OP decLenReg empty (Sub FeltType) [afterPtr, memReg],
            EXTPRIM [segLenReg] empty readTag [Param 0],
            OP lenDiffReg empty (Sub FeltType) [segLenReg, decLenReg],
            CASE lenDiffReg [(0, success)] (Just error)
          ]

generateSegmentCodecs : CairoName -> List ABIData -> Maybe ABIData -> List (CairoName, CairoDef)
generateSegmentCodecs name args (Just ret) = [
    (genAbstractFunctionParamEncoderName name, generateSegmentEncoder (map type args)),
    (genAbstractFunctionResultDecoderName name, generateSegmentDecoder (type ret))
]
generateSegmentCodecs name args Nothing = (genAbstractFunctionParamEncoderName name,generateSegmentEncoder (map type args))::Nil

generateAbiFunction : (ABIType -> Maybe Int) -> ABIEntry -> List (CairoName, CairoDef)
generateAbiFunction _ abi@(Struct _ _) = (genEncoderDef abi) ++ (genDecoderDef abi)
generateAbiFunction _ abi@(Variant _ _) = (genEncoderDef abi) ++ (genDecoderDef abi)
generateAbiFunction sizeF abi@(AbstractFunction name args rets) = (genEntryPoint sizeF abi)::(generateSegmentCodecs name args rets)
generateAbiFunction sizeF abi = [genEntryPoint sizeF abi]

public export
generateAbiFunctions : List ABIEntry -> List (CairoName, CairoDef)
generateAbiFunctions entries = foldl (\acc, e => (generateAbiFunction sizeF e) ++ acc) [] entries
    where sizeF : ABIType -> Maybe Int
          sizeF = getSize (sizeMap (indexedTopLevelTypes entries))


