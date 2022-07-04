module Primitives.BigInt

import Primitives.Common
import Core.Context
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import CodeGen.CodeGenHelper
import CommonDef
import Utils.Helpers
import Data.Bits

bigint_name : String-> Name
bigint_name op = makeBuiltinName "\{op}_bigint"

bigint_import : String -> Import
bigint_import op = MkImport "skyro.bigint" op (Just "\{op}_bigint")

entry_bit_length : Integer
entry_bit_length = 125

entry_shift : Integer
entry_shift = 2 `shiftL` 125

export
[add_integer] PrimFn where
    eval [_, ConstValue (BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI 0), _] = Just $ ArgValue 1
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "add"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "add") args]

export
[sub_integer] PrimFn where
    eval [_, ConstValue (BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "sub"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "sub") args]

export
[mul_integer] PrimFn where
    eval [_, ConstValue (BI 1)] = Just $ ArgValue 0
    eval [ConstValue (BI 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (BI 0)] = Just $ NewValue $ ConstValue $ BI 0
    eval [ConstValue (BI 0), _] = Just $ NewValue $ ConstValue $ BI 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "mul"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "mul") args]

export
[div_integer] PrimFn where
    eval [_, ConstValue (BI 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (BI 1)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "div"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "div") args]

export
[mod_integer] PrimFn where
    eval [_, ConstValue (BI 1)] = Just $ NewValue $ ConstValue $ BI 0
    eval [_, ConstValue (BI 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "mod"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "mod") args]

export
[neg_integer] PrimFn where
    eval [ConstValue (BI a)] = Just $ NewValue $ ConstValue $ BI (-a)
    eval _ = Nothing

    imports = fromList [bigint_import "neg"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "neg") args]

export
[shl_integer] PrimFn where
    eval [_, ConstValue(BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__shl_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode _ = generateMissingCodeError "shl_integer" genRuntimeNote

export
[shr_integer] PrimFn where
    eval [_, ConstValue(BI 0)] = Just $ ArgValue 0
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__shr_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode _ = generateMissingCodeError "shr_integer" genRuntimeNote

export
[and_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__and_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode _ = generateMissingCodeError "and_integer" genRuntimeNote

export
[or_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__or_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode _ = generateMissingCodeError "or_integer" genRuntimeNote

export
[xor_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ BI (prim__xor_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode _ = generateMissingCodeError "xor_integer" genRuntimeNote

export
[lt_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "lt"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "lt") args]

export
[lte_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "lte"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "lte") args]

export
[eq_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    imports = fromList [bigint_import "eq"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "eq") args]

export
[gte_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "lte"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "lte") (reverse args)]

export
[gt_integer] PrimFn where
    eval [ConstValue (BI a), ConstValue (BI b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "lt"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "lt") (reverse args)]


export
[cast_unsigned_to_integer] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ BI r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [MkImport "skyro.bigint" "BigInt" Nothing]
    generateCode _ r [b] implicits = Raw """
        tempvar cast_abs_tmp_ = new(\{ compileReg b }, -1)
        \{ compileRegDecl r } = BigInt(1, cast(cast_abs_tmp_,felt))
    """

    generateCode _ _ _ _ = assert_total $ idris_crash "wrong number of arguments and returns for cast"

export
[cast_signed_to_integer] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ BI r) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "from_small_felt"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "from_small_felt") args]

-- Note we have separate as the others do not need any shifting (because < entry_shift)
export
[cast_felt_to_integer] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ BI r) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [bigint_import "from_felt"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "from_felt") args]

generateCast : (target: CairoConst) -> String -> (res:CairoReg) -> (args:List CairoReg) -> LinearImplicitArgs -> PrimFnCode
generateCast target unique res args implicits = if implicits == empty
        then Instructions [
               CALL [tmpReg] empty (bigint_name "signed_lsf") args,
               OP res empty (Cast FeltType target) [tmpReg]
             ]
        else assert_total $ idris_crash "no implicits expected for cast"
    where tmpReg : CairoReg
          tmpReg = CustomReg unique Nothing
export
[cast_integer_to_int] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast IntType


export
[cast_integer_to_int8] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I8 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Int8Type

export
[cast_integer_to_int16] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I16 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Int16Type

export
[cast_integer_to_int32] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I32 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Int32Type

export
[cast_integer_to_int64] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ I64 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Int64Type

export
[cast_integer_to_felt] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ F $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "to_felt"]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (bigint_name "to_felt") args]

export
[cast_integer_to_uint8] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B8 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Bits8Type

export
[cast_integer_to_uint16] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B16 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Bits16Type

export
[cast_integer_to_uint32] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B32 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Bits32Type

export
[cast_integer_to_uint64] PrimFn where
    eval [ConstValue c] = map (\r => NewValue $ ConstValue $ B64 $ cast r) (constToInteger c)
    eval _ = Nothing

    imports = fromList [bigint_import "signed_lsf"]
    generateCode = generateCast Bits64Type

public export
[manifestBigInteger] ConstReg where
    assignConstantReg resReg (BI bi) = """
      tempvar uncasted_big_int_tmp_ = new(\{ sign }, new(\{ separate ", " splitted }, -1))
      \{ compileRegDecl resReg } = cast(uncasted_big_int_tmp_,felt)
    """
    where split : Integer -> List String
          split bi = if bi < entry_shift
             then (show bi)::Nil
             else (show (bi `mod` entry_shift))::(split (bi `div` entry_shift))
          splitted : List String
          splitted = if bi < 0
            then split ((-1)*bi)
            else split bi
          sign : String
          sign = if bi < 0 then "-1" else "1"
    assignConstantReg _ c = assert_total $ idris_crash $ "Not a big integer constant: " ++ (show c)

    manifestConstantReg unique (Const c) = (Just (assignConstantReg resReg c), resReg)
        where resReg : CairoReg
              resReg = CustomReg unique Nothing
    manifestConstantReg _ r = assert_total $ idris_crash $ "Not a constant: " ++ (show r)
