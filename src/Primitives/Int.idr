||| Primitive operations for fixed size, signed integers. 
module Primitives.Int

import Primitives.Common
import Core.Context
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import CommonDef
import CodeGen.CodeGenHelper

---------------------------------------------------------------------------------------------------
-- UINT General
---------------------------------------------------------------------------------------------------
intX_name : String-> Nat -> Name
intX_name op nBits = makeBuiltinName "\{op}_int\{show nBits}"

intX_import : String -> Nat -> Import
intX_import op nBits = MkImport "skyro.int\{show nBits}" "int_\{op}" (Just "\{op}_int\{show nBits}")

---------------------------------------------------------------------------------------------------
-- UINT ADD
---------------------------------------------------------------------------------------------------
add_intX_name : Nat -> Name
add_intX_name = intX_name "add"

add_intX_import : Nat -> Import
add_intX_import = intX_import "add"

-- Implements
export
[add_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I 0), _] = Just $ ArgValue 1
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_intX_name 64) args]

export
[add_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 0), _] = Just $ ArgValue 1
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_intX_name 8) args]

export
[add_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 0), _] = Just $ ArgValue 1
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_intX_name 16) args]

export
[add_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 0), _] = Just $ ArgValue 1
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_intX_name 32) args]

export
[add_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 0), _] = Just $ ArgValue 1
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_intX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT SUB
---------------------------------------------------------------------------------------------------
sub_intX_name : Nat -> Name
sub_intX_name = intX_name "sub"

sub_intX_import : Nat -> Import
sub_intX_import = intX_import "sub"

export
[sub_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_intX_name 64) args]

export
[sub_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_intX_name 8) args]

export
[sub_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_intX_name 16) args]

export
[sub_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_intX_name 32) args]

export
[sub_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_intX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT MUL
---------------------------------------------------------------------------------------------------
mul_intX_name : Nat -> Name
mul_intX_name = intX_name "mul"

mul_intX_import : Nat -> Import
mul_intX_import = intX_import "mul"

export
[mul_int] PrimFn where
    eval [_, ConstValue (I 1)] = Just $ ArgValue 0
    eval [ConstValue (I 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I 0)] = Just $ NewValue $ ConstValue $ I 0
    eval [ConstValue (I 0), _] = Just $ NewValue $ ConstValue $ I 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_intX_name 64) args]

export
[mul_int8] PrimFn where
    eval [_, ConstValue (I8 1)] = Just $ ArgValue 0
    eval [ConstValue (I8 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I8 0)] = Just $ NewValue $ ConstValue $ I8 0
    eval [ConstValue (I8 0), _] = Just $ NewValue $ ConstValue $ I8 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_intX_name 8) args]

export
[mul_int16] PrimFn where
    eval [_, ConstValue (I16 1)] = Just $ ArgValue 0
    eval [ConstValue (I16 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I16 0)] = Just $ NewValue $ ConstValue $ I16 0
    eval [ConstValue (I16 0), _] = Just $ NewValue $ ConstValue $ I16 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_intX_name 16) args]

export
[mul_int32] PrimFn where
    eval [_, ConstValue (I32 1)] = Just $ ArgValue 0
    eval [ConstValue (I32 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I32 0)] = Just $ NewValue $ ConstValue $ I32 0
    eval [ConstValue (I32 0), _] = Just $ NewValue $ ConstValue $ I32 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_intX_name 32) args]

export
[mul_int64] PrimFn where
    eval [_, ConstValue (I64 1)] = Just $ ArgValue 0
    eval [ConstValue (I64 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I64 0)] = Just $ NewValue $ ConstValue $ I64 0
    eval [ConstValue (I64 0), _] = Just $ NewValue $ ConstValue $ I64 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- UINT DIV
---------------------------------------------------------------------------------------------------
div_intX_name : Nat -> Name
div_intX_name = intX_name "div"

div_intX_import : Nat -> Import
div_intX_import = intX_import "div"

export
[div_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I 1)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_intX_name 64) args]

export
[div_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I8 1)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_intX_name 8) args]

export
[div_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I16 1)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_intX_name 16) args]

export
[div_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I32 1)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_intX_name 32) args]

export
[div_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I64 1)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- UINT MOD
---------------------------------------------------------------------------------------------------
mod_intX_name : Nat -> Name
mod_intX_name = intX_name "mod"

mod_intX_import : Nat -> Import
mod_intX_import = intX_import "mod"

export
[mod_int] PrimFn where
    eval [_, ConstValue (I 1)] = Just $ NewValue $ ConstValue $ I 0
    eval [_, ConstValue (I 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_intX_name 64) args]

export
[mod_int8] PrimFn where
    eval [_, ConstValue (I8 1)] = Just $ NewValue $ ConstValue $ I8 0
    eval [_, ConstValue (I8 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_intX_name 8) args]

export
[mod_int16] PrimFn where
    eval [_, ConstValue (I16 1)] = Just $ NewValue $ ConstValue $ I16 0
    eval [_, ConstValue (I16 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_intX_name 16) args]

export
[mod_int32] PrimFn where
    eval [_, ConstValue (I32 1)] = Just $ NewValue $ ConstValue $ I32 0
    eval [_, ConstValue (I32 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_intX_name 32) args]

export
[mod_int64] PrimFn where
    eval [_, ConstValue (I64 1)] = Just $ NewValue $ ConstValue $ I64 0
    eval [_, ConstValue (I64 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT NEG:
---------------------------------------------------------------------------------------------------
neg_intX_name : Nat -> Name
neg_intX_name = intX_name "neg"

neg_intX_import : Nat -> Import
neg_intX_import = intX_import "neg"

export
[neg_int] PrimFn where
    eval [ConstValue (I a)] = Just $ NewValue $ ConstValue $ I (-a)
    eval _ = Nothing

    imports = fromList [neg_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_intX_name 64) args]

export
[neg_int8] PrimFn where
    eval [ConstValue (I8 a)] = Just $ NewValue $ ConstValue $ I8 (-a)
    eval _ = Nothing

    imports = fromList [neg_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_intX_name 8) args]

export
[neg_int16] PrimFn where
    eval [ConstValue (I16 a)] = Just $ NewValue $ ConstValue $ I16 (-a)
    eval _ = Nothing

    imports = fromList [neg_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_intX_name 16) args]

export
[neg_int32] PrimFn where
    eval [ConstValue (I32 a)] = Just $ NewValue $ ConstValue $ I32 (-a)
    eval _ = Nothing

    imports = fromList [neg_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_intX_name 16) args]

export
[neg_int64] PrimFn where
    eval [ConstValue (I64 a)] = Just $ NewValue $ ConstValue $ I64 (-a)
    eval _ = Nothing

    imports = fromList [neg_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT SHL:
---------------------------------------------------------------------------------------------------
shl_intX_name : Nat -> Name
shl_intX_name = intX_name "shl"

shl_intX_import : Nat -> Import
shl_intX_import = intX_import "shl"

export
[shl_int] PrimFn where
    apStable = False

    eval [_, ConstValue(I 0)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__shl_Int a b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_intX_name 64) args]


export
[shl_int8] PrimFn where
    apStable = False

    eval [_, ConstValue(I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__shl_Int8 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_intX_name 8) args]

export
[shl_int16] PrimFn where
    apStable = False

    eval [_, ConstValue(I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__shl_Int16 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_intX_name 16) args]

export
[shl_int32] PrimFn where
    apStable = False

    eval [_, ConstValue(I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__shl_Int32 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_intX_name 32) args]

export
[shl_int64] PrimFn where
    apStable = False

    eval [_, ConstValue(I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__shl_Int64 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT SHR:
---------------------------------------------------------------------------------------------------
shr_intX_name : Nat -> Name
shr_intX_name = intX_name "shr"

shr_intX_import : Nat -> Import
shr_intX_import = intX_import "shr"

export
[shr_int] PrimFn where
    apStable = False

    eval [_, ConstValue(I 0)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__shr_Int a b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_intX_name 64) args]

export
[shr_int8] PrimFn where
    apStable = False

    eval [_, ConstValue(I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__shr_Int8 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_intX_name 8) args]

export
[shr_int16] PrimFn where
    apStable = False

    eval [_, ConstValue(I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__shr_Int16 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_intX_name 16) args]

export
[shr_int32] PrimFn where
    apStable = False

    eval [_, ConstValue(I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__shr_Int32 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_intX_name 32) args]

export
[shr_int64] PrimFn where
    apStable = False

    eval [_, ConstValue(I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__shr_Int64 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT AND:
---------------------------------------------------------------------------------------------------
and_intX_name : Nat -> Name
and_intX_name = intX_name "and"

and_intX_import : Nat -> Import
and_intX_import = intX_import "and"

export
[and_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ NewValue $ ConstValue $ I 0
    eval [ConstValue (I 0), _] = Just $ NewValue $ ConstValue $ I 0
    eval [_, ConstValue (I (-1))] = Just $ ArgValue 0
    eval [ConstValue (I (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__and_Int a b)
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [and_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (and_intX_name 64) args]

export
[and_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ NewValue $ ConstValue $ I8 0
    eval [ConstValue (I8 0), _] = Just $ NewValue $ ConstValue $ I8 0
    eval [_, ConstValue (I8 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I8 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__and_Int8 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [and_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (and_intX_name 8) args]

export
[and_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ NewValue $ ConstValue $ I16 0
    eval [ConstValue (I16 0), _] = Just $ NewValue $ ConstValue $ I16 0
    eval [_, ConstValue (I16 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I16 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__and_Int16 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [and_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (and_intX_name 16) args]

export
[and_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ NewValue $ ConstValue $ I32 0
    eval [ConstValue (I32 0), _] = Just $ NewValue $ ConstValue $ I32 0
    eval [_, ConstValue (I32 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I32 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__and_Int32 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [and_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (and_intX_name 32) args]

export
[and_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ NewValue $ ConstValue $ I64 0
    eval [ConstValue (I64 0), _] = Just $ NewValue $ ConstValue $ I64 0
    eval [_, ConstValue (I64 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I64 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__and_Int64 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [and_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (and_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT OR:
---------------------------------------------------------------------------------------------------
or_intX_name : Nat -> Name
or_intX_name = intX_name "or"

or_intX_import : Nat -> Import
or_intX_import = intX_import "or"

export
[or_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I  (-1))] = Just $ NewValue $ ConstValue $ I (-1)
    eval [ConstValue (I  (-1)), _] = Just $ NewValue $ ConstValue $ I (-1)
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__or_Int a b)
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [or_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (or_intX_name 64) args]

export
[or_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I8 (-1))] = Just $ NewValue $ ConstValue $ I8 (-1)
    eval [ConstValue (I8 (-1)), _] = Just $ NewValue $ ConstValue $ I8 (-1)
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__or_Int8 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [or_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (or_intX_name 8) args]

export
[or_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I16 (-1))] = Just $ NewValue $ ConstValue $ I16 (-1)
    eval [ConstValue (I16 (-1)), _] = Just $ NewValue $ ConstValue $ I16 (-1)
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__or_Int16 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [or_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (or_intX_name 16) args]

export
[or_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I32 (-1))] = Just $ NewValue $ ConstValue $ I32 (-1)
    eval [ConstValue (I32 (-1)), _] = Just $ NewValue $ ConstValue $ I32 (-1)
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__or_Int32 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [or_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (or_intX_name 32) args]

export
[or_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I64 (-1))] = Just $ NewValue $ ConstValue $ I64 (-1)
    eval [ConstValue (I64 (-1)), _] = Just $ NewValue $ ConstValue $ I64 (-1)
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__or_Int64 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [or_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (or_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT XOR:
---------------------------------------------------------------------------------------------------
xor_intX_name : Nat -> Name
xor_intX_name = intX_name "xor"

xor_intX_import : Nat -> Import
xor_intX_import = intX_import "xor"

export
[xor_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I 0), _] = Just $ ArgValue 1
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__xor_Int a b)
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [xor_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (xor_intX_name 64) args]

export
[xor_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 0), _] = Just $ ArgValue 1
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__xor_Int8 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [xor_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (xor_intX_name 8) args]

export
[xor_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 0), _] = Just $ ArgValue 1
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__xor_Int16 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [xor_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (xor_intX_name 16) args]

export
[xor_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 0), _] = Just $ ArgValue 1
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__xor_Int32 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [xor_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (xor_intX_name 32) args]

export
[xor_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 0), _] = Just $ ArgValue 1
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__xor_Int64 (cast a) (cast b))
    eval _ = Nothing

    implicits = fromList [range_check_builtin, bitwise_builtin]
    imports = fromList [xor_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (xor_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT LT
---------------------------------------------------------------------------------------------------
lt_intX_name : Name
lt_intX_name = makeBuiltinName "lt_int"

lt_intX_import : Import
lt_intX_import = MkImport "skyro.int" "int_lt" (Just "lt_int")

export
[lt_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name args]

export
[lt_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name args]

export
[lt_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name args]

export
[lt_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name args]

export
[lt_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name args]

---------------------------------------------------------------------------------------------------
-- INT LTE
---------------------------------------------------------------------------------------------------
lte_intX_name : Name
lte_intX_name = makeBuiltinName "lte_int"

lte_intX_import : Import
lte_intX_import = MkImport "skyro.int" "int_lte" (Just "lte_int")

export
[lte_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name args]

export
[lte_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name args]

export
[lte_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name args]

export
[lte_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name args]

export
[lte_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name args]

---------------------------------------------------------------------------------------------------
-- INT EQ
---------------------------------------------------------------------------------------------------
export
[eq_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_int" r a i

export
[eq_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_int8" r a i

export
[eq_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_int16" r a i

export
[eq_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_int32" r a i

export
[eq_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_int64" r a i

---------------------------------------------------------------------------------------------------
-- INT GTE
-- Implementation uses flipped arguments to lte
---------------------------------------------------------------------------------------------------

export
[gte_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name (reverse args)]

export
[gte_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name (reverse args)]

export
[gte_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name (reverse args)]

export
[gte_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name (reverse args)]

export
[gte_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_intX_name (reverse args)]

---------------------------------------------------------------------------------------------------
-- INT GT
-- Implementation uses flipped arguments to lt
---------------------------------------------------------------------------------------------------

export
[gt_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name (reverse args)]

export
[gt_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name (reverse args)]

export
[gt_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name (reverse args)]

export
[gt_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name (reverse args)]

export
[gt_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_intX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_intX_name (reverse args)]

---------------------------------------------------------------------------------------------------
-- INT CASTS
---------------------------------------------------------------------------------------------------
cast_intX_name : Nat -> Name
cast_intX_name = intX_name "cast"

cast_intX_import : Nat -> Import
cast_intX_import = intX_import "cast"

export
[cast_to_int] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_intX_name 64) args]

export
[cast_to_int8] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I8 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_intX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_intX_name 8) args]

export
[cast_to_int16] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I16 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_intX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_intX_name 16) args]

export
[cast_to_int32] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I32 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_intX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_intX_name 32) args]

export
[cast_to_int64] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I64 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_intX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_intX_name 64) args]
