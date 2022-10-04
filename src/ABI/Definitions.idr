module ABI.Definitions

import CairoCode.Name
import Data.List
import Data.SortedSet
import CairoCode.CairoCode
import CommonDef

public export
data ABIType : Type where
    PrimType : CairoConst -> ABIType
    NamedType : CairoName -> ABIType
    TupleType : List ABIType -> ABIType
    SegmentType : ABIType -- Used for Segments has the form (size : felt, data : felt*)

public export
Eq ABIType where
    (==) (PrimType cc1) (PrimType cc2) = cc1 == cc2
    (==) (NamedType n1) (NamedType n2) = n1 == n2
    (==) (TupleType ts1) (TupleType ts2) = assert_total (ts1 == ts2)
    (==) SegmentType SegmentType = True
    (==) _ _ = False

public export
Ord ABIType where
    compare (PrimType cc1) (PrimType cc2) = compare cc1 cc2
    compare (NamedType n1) (NamedType n2) = compare n1 n2
    compare (TupleType ts1) (TupleType ts2) = assert_total (compare ts1 ts2)
    compare SegmentType SegmentType = EQ
    compare at1 at2 = compare (dataOrder at1) (dataOrder at2)
        where dataOrder : ABIType -> Int
              dataOrder (PrimType _) = 0
              dataOrder (NamedType _) = 1
              dataOrder (TupleType _) = 2
              dataOrder SegmentType = 3


public export
Show ABIType where
    show (PrimType c) = "PrimType "++ show c
    show (NamedType n) = assert_total ("NamedType "++ show n)
    show (TupleType ts) =  assert_total ("TupleType ("++ show ts++")")
    show SegmentType = "SegmentType"

public export
record ABIData where
    constructor MkField
    name : String
    type : ABIType

public export
data ABIEntry : Type where
    Struct : CairoName -> List ABIData -> ABIEntry
    Variant : CairoName -> List (List ABIData) -> ABIEntry
    -- CustomType : CairoName -> CairoName -> CairoName -> ABIEntry -- First: EntryIdentifier, Second: SerializerName, Third: DeserializerName
    ExternalFunction : CairoName -> List ABIData -> Maybe ABIData -> ABIEntry
    ViewFunction : CairoName -> List ABIData -> Maybe ABIData -> ABIEntry
    Constructor : CairoName -> List ABIData -> ABIEntry
    AbstractFunction : CairoName -> List ABIData -> Maybe ABIData -> ABIEntry
    Event : CairoName -> ABIEntry
    L1Handler : CairoName -> List ABIData -> ABIEntry
    -- Contract : CairoName -> List ABIEntry
    StorageVar : CairoName -> ABIEntry

public export
entryName : ABIEntry -> CairoName
entryName (Struct name _) = name
entryName (Variant name _) = name
entryName (ExternalFunction name _ _) = name
entryName (ViewFunction name _ _) = name
entryName (Constructor name _) = name
entryName (AbstractFunction name _ _) = name
entryName (Event name) = name
entryName (L1Handler name _) = name
entryName (StorageVar name) = name

public export
genEncoderName : CairoName -> CairoName
genEncoderName name = extendNamePlain "encoder" (extendNamePlain "generated" name)

public export
genDecoderName : CairoName -> CairoName
genDecoderName name = extendNamePlain "decoder" (extendNamePlain "generated" name)

public export
genCtrEncoderName : Int -> CairoName -> CairoName
genCtrEncoderName tag name = extendName "encoder" tag (extendNamePlain "generated" name)

public export
genCtrDecoderName : Int -> CairoName -> CairoName
genCtrDecoderName tag name = extendName "decoder" tag (extendNamePlain "generated" name)

public export
genAbstractFunctionResultDecoderName : CairoName -> CairoName
genAbstractFunctionResultDecoderName name = extendNamePlain "resultdecoder" (extendNamePlain "generated" name)

public export
genAbstractFunctionParamEncoderName : CairoName -> CairoName
genAbstractFunctionParamEncoderName name = extendNamePlain "paramencoder" (extendNamePlain "generated" name)

public export
genEntryName : CairoName -> String -> CairoName
genEntryName n _ = externalName $ extractName n

public export
constructorName : CairoName
constructorName = externalName "constructor"
