module Primitives.BigInt

import Primitives.Common
import Core.Context
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import CodeGen.CodeGenHelper
import CommonDef


export
[add_integer] PrimFn where
    eval [_, ConstValue (BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI 0), _] = Just $ ArgValue 1
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a+b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "add_integer"

export
[sub_integer] PrimFn where
    eval [_, ConstValue (BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a-b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "sub_integer"

export
[mul_integer] PrimFn where
    eval [_, ConstValue (BI 1)] = Just $ ArgValue 0
    eval [ConstValue (BI 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (BI 0)] = Just $ NewValue $ ConstValue $ BI 0
    eval [ConstValue (BI 0), _] = Just $ NewValue $ ConstValue $ BI 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a*b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "mul_integer"

export
[div_integer] PrimFn where
    eval [_, ConstValue (BI 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (BI 1)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a `div` b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "div_integer"

export
[mod_integer] PrimFn where
    eval [_, ConstValue (BI 1)] = Just $ NewValue $ ConstValue $ BI 0
    eval [_, ConstValue (BI 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a `mod` b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "mod_integer"

export
[neg_integer] PrimFn where
    eval [ConstValue (BI a)] = Just $ NewValue $ ConstValue $ BI (-a)
    eval _ = Nothing

    generateCode = generateMissingCodeError "neg_integer"

export
[shl_integer] PrimFn where
    eval [_, ConstValue(BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__shl_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shl_integer"

export
[shr_integer] PrimFn where
    eval [_, ConstValue(BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__shr_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shr_integer"

export
[and_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__and_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "and_integer"

export
[or_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__or_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "or_integer"

export
[xor_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__xor_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "xor_integer"

export
[lt_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "lt_integer"

export
[lte_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "lte_integer"

export
[eq_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "eq_integer"

export
[gte_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "gte_integer"

export
[gt_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    generateCode = generateMissingCodeError "gt_integer"

export
[cast_to_integer] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ BI r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_to_integer"


export
[cast_integer_to_int] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_int"

export
[cast_integer_to_int8] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I8 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_int8"

export
[cast_integer_to_int16] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I16 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_int16"

export
[cast_integer_to_int32] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I32 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_int32"

export
[cast_integer_to_int64] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I64 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_int64"

export
[cast_integer_to_felt] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ F $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode r [_] _ = Instructions [ERROR r "cast_integer_to_felt is currently not supported"]
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode cast_integer_to_felt"


export
[cast_integer_to_uint8] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B8 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_uint8"

export
[cast_integer_to_uint16] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B16 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_uint16"

export
[cast_integer_to_uint32] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B32 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_uint32"

export
[cast_integer_to_uint64] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B64 $ cast r) (constToInteger c)
    eval _ = Nothing

    generateCode _ _ _ = generateMissingCodeError "cast_integer_to_uint64"
