module ABI.Definitions

import Core.Context
import Data.List
import Data.SortedSet
import Core.Name.Namespace
import CairoCode.CairoCode
import CommonDef

public export
data ABIType : Type where
    PrimType : CairoConst -> ABIType
    -- BigIntType : ABIType // Just PrimType IntegerType
    NamedType : Name -> List ABIType -> ABIType
    Variable : String -> ABIType
    TupleType : List ABIType -> ABIType
    SegmentType : ABIType -- Used for Segments has the form (size : felt, data : felt*)

public export
Eq ABIType where
    (==) (PrimType cc1) (PrimType cc2) = cc1 == cc2
    (==) (NamedType n1 ts1) (NamedType n2 ts2) = n1 == n2 && assert_total (ts1 == ts2)
    (==) (Variable v1) (Variable v2) = v1 == v2
    (==) (TupleType ts1) (TupleType ts2) = assert_total (ts1 == ts2)
    (==) SegmentType SegmentType = True
    (==) _ _ = False

public export
Ord ABIType where
    compare (PrimType cc1) (PrimType cc2) = compare cc1 cc2
    compare (NamedType n1 ts1) (NamedType n2 ts2) = thenCompare (compare n1 n2) (assert_total (compare ts1 ts2))
    compare (Variable v1) (Variable v2) = compare v1 v2
    compare (TupleType ts1) (TupleType ts2) = assert_total (compare ts1 ts2)
    compare SegmentType SegmentType = EQ
    compare at1 at2 = compare (dataOrder at1) (dataOrder at2)
        where dataOrder : ABIType -> Int
              dataOrder (PrimType _) = 0
              dataOrder (NamedType _ _) = 1
              dataOrder (TupleType _) = 2
              dataOrder (Variable _ ) = 3
              dataOrder SegmentType = 4


public export
Show ABIType where
    show (PrimType c) = "PrimType "++ show c
    show (NamedType n args) = assert_total ("NamedType "++ show n++"("++show args++")")
    show (Variable s) = "Variable "++ show s
    show (TupleType ts) =  assert_total ("TupleType ("++ show ts++")")
    show SegmentType = "SegmentType"

public export
record ABIData where
    constructor MkField
    name : String
    type : ABIType

public export
data ABIEntry : Type where
    -- Struct : Name -> List ABIData -> ABIEntry
    Struct : Name -> List String -> List ABIData -> ABIEntry
    -- Variant : Name -> List (List ABIData) -> ABIEntry
    Variant : Name -> List String -> List (List ABIData) -> ABIEntry
    ExternalFunction : Name -> List ABIData -> Maybe ABIData -> ABIEntry
    ViewFunction : Name -> List ABIData -> Maybe ABIData -> ABIEntry
    Constructor : Name -> List ABIData -> ABIEntry
    -- Event : Name -> List ABIData -> List ABIData -> ABIEntry
    Event : Name -> ABIEntry
    L1Handler : Name -> List ABIData -> ABIEntry
    -- Contract : Name -> List ABIEntry
    StorageVar : Name -> ABIEntry

topLevelName : Name -> Name
topLevelName (NS _ innerName) = topLevelName innerName
topLevelName (MN n _) = UN $ Basic n
topLevelName n = n

-- to help the inliner
makeMachineName : Name -> Name
makeMachineName (NS ns innerName) = NS ns (makeMachineName innerName)
makeMachineName (PV innerName v) = PV (makeMachineName innerName) v
makeMachineName (Nested idx innerName) = Nested idx (makeMachineName innerName)
makeMachineName (UN (Basic name)) = MN name 0
makeMachineName (UN (Field name)) = MN name 0
makeMachineName (DN str name) = DN str (makeMachineName name)
makeMachineName name = name

nestName : (Int, Int) -> Name -> Name
nestName n (NS ns innerName) = NS ns (nestName n innerName)
nestName n name = Nested n name

public export
genEncoderName : Name -> Name
genEncoderName name = NS (mkNamespace "ABI.Encode") (makeMachineName name)

public export
genDecoderName : Name -> Name
genDecoderName name = NS (mkNamespace "ABI.Decode") (makeMachineName name)

public export
genCtrEncoderName : Int -> Name -> Name
genCtrEncoderName tag name = NS (mkNamespace "ABI.Encode") (makeMachineName (nestName (tag,0) name))

public export
genCtrDecoderName : Int -> Name -> Name
genCtrDecoderName tag name = NS (mkNamespace "ABI.Decode") (makeMachineName (nestName (tag,0) name))

public export
genEntryName : Name -> String -> Name
genEntryName (NS _ n) kind = topLevelName n
genEntryName n kind = topLevelName n

public export
constructorName : Name
constructorName = UN $ Basic ("constructor")
