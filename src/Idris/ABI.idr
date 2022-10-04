module Idris.ABI

import CairoCode.Name
import Data.List
import CairoCode.CairoCode
import CommonDef

public export
data ABIType : Type where
    PrimType : CairoConst -> ABIType                    -- Same as Skyro
    NamedType : CairoName -> List ABIType -> ABIType    -- As Skyro but extra type params
    Variable : String -> ABIType                        -- Idris only
    TupleType : List ABIType -> ABIType                 -- Same as Skyro
    SegmentType : ABIType                               -- Same as Skyro

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

-- Same as Skyro (but using Idris ABIType)
public export
record ABIData where
    constructor MkField
    name : String
    type : ABIType

-- Same as Skyro (but using Idris ABIData)
public export
data ABIEntry : Type where
    Struct : CairoName -> List String -> List ABIData -> ABIEntry           -- As Skyro but with type params
    Variant : CairoName -> List String -> List (List ABIData) -> ABIEntry   -- As Skyro but with type params
    -- CustomType : CairoName -> CairoName -> CairoName -> ABIEntry
    ExternalFunction : CairoName -> (abstract: Bool) -> List ABIData -> Maybe ABIData -> ABIEntry
    ViewFunction : CairoName -> (abstract: Bool) -> List ABIData -> Maybe ABIData -> ABIEntry
    Constructor : CairoName -> List ABIData -> ABIEntry
    Event : CairoName -> ABIEntry
    L1Handler : CairoName -> List ABIData -> ABIEntry
    -- Contract : CairoName -> List ABIEntry
    StorageVar : CairoName -> ABIEntry
