||| Primitive operations for fixed size, unsigned integers. 
module Primitives.UInt

import Primitives.Common
-- import Core.Context
import CairoCode.Name
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import CommonDef
import CodeGen.CodeGenHelper

---------------------------------------------------------------------------------------------------
-- UINT General
---------------------------------------------------------------------------------------------------
uintX_name : String-> Nat -> CairoName
uintX_name op nBits = makeBuiltinName "\{op}_uint\{show nBits}"

uintX_import : String -> Nat -> Import
uintX_import op nBits = MkImport "skyro.uint\{show nBits}" "uint_\{op}" (Just "\{op}_uint\{show nBits}")

---------------------------------------------------------------------------------------------------
-- UINT ADD
---------------------------------------------------------------------------------------------------
add_uintX_name : Nat -> CairoName
add_uintX_name = uintX_name "add"

add_uintX_import : Nat -> Import
add_uintX_import = uintX_import "add"

export
[add_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 0), _] = Just $ ArgValue 1
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_uintX_name 8) args]

export
[add_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 0), _] = Just $ ArgValue 1
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_uintX_name 16) args]

export
[add_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 0), _] = Just $ ArgValue 1
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_uintX_name 32) args]

export
[add_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 0), _] = Just $ ArgValue 1
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [add_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (add_uintX_name 64) args]

---------------------------------------------------------------------------------------------------
-- UINT SUB
---------------------------------------------------------------------------------------------------
sub_uintX_name : Nat -> CairoName
sub_uintX_name = uintX_name "sub"

sub_uintX_import : Nat -> Import
sub_uintX_import = uintX_import "sub"

export
[sub_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 8) args]

export
[sub_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 16) args]

export
[sub_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 32) args]

export
[sub_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [sub_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT MUL
---------------------------------------------------------------------------------------------------
mul_uintX_name : Nat -> CairoName
mul_uintX_name = uintX_name "mul"

mul_uintX_import : Nat -> Import
mul_uintX_import = uintX_import "mul"

export
[mul_uint8] PrimFn where
    eval [_, ConstValue (B8 1)] = Just $ ArgValue 0
    eval [ConstValue (B8 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B8 0)] = Just $ NewValue $ ConstValue $ B8 0
    eval [ConstValue (B8 0), _] = Just $ NewValue $ ConstValue $ B8 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 8) args]

export
[mul_uint16] PrimFn where
    eval [_, ConstValue (B16 1)] = Just $ ArgValue 0
    eval [ConstValue (B16 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B16 0)] = Just $ NewValue $ ConstValue $ B16 0
    eval [ConstValue (B16 0), _] = Just $ NewValue $ ConstValue $ B16 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 16) args]

export
[mul_uint32] PrimFn where
    eval [_, ConstValue (B32 1)] = Just $ ArgValue 0
    eval [ConstValue (B32 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B32 0)] = Just $ NewValue $ ConstValue $ B32 0
    eval [ConstValue (B32 0), _] = Just $ NewValue $ ConstValue $ B32 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 32) args]

export
[mul_uint64] PrimFn where
    eval [_, ConstValue (B64 1)] = Just $ ArgValue 0
    eval [ConstValue (B64 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B64 0)] = Just $ NewValue $ ConstValue $ B64 0
    eval [ConstValue (B64 0), _] = Just $ NewValue $ ConstValue $ B64 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mul_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 64) args]



---------------------------------------------------------------------------------------------------
-- UINT DIV
---------------------------------------------------------------------------------------------------
div_uintX_name : Nat -> CairoName
div_uintX_name = uintX_name "div"

div_uintX_import : Nat -> Import
div_uintX_import = uintX_import "div"

export
[div_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B8 1)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_uintX_name 8) args]

export
[div_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B16 1)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_uintX_name 16) args]

export
[div_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B32 1)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_uintX_name 32) args]

export
[div_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B64 1)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [div_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (div_uintX_name 64) args] 

---------------------------------------------------------------------------------------------------
-- UINT MOD
---------------------------------------------------------------------------------------------------
mod_uintX_name : Nat -> CairoName
mod_uintX_name = uintX_name "mod"

mod_uintX_import : Nat -> Import
mod_uintX_import = uintX_import "mod"

export
[mod_uint8] PrimFn where
    eval [_, ConstValue (B8 1)] = Just $ NewValue $ ConstValue $ B8 0
    eval [_, ConstValue (B8 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 8) args]

export
[mod_uint16] PrimFn where
    eval [_, ConstValue (B16 1)] = Just $ NewValue $ ConstValue $ B16 0
    eval [_, ConstValue (B16 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 16) args]

export
[mod_uint32] PrimFn where
    eval [_, ConstValue (B32 1)] = Just $ NewValue $ ConstValue $ B32 0
    eval [_, ConstValue (B32 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 32) args]

export
[mod_uint64] PrimFn where
    eval [_, ConstValue (B64 1)] = Just $ NewValue $ ConstValue $ B64 0
    eval [_, ConstValue (B64 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [mod_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT NEG:
---------------------------------------------------------------------------------------------------
neg_uintX_name : Nat -> CairoName
neg_uintX_name = uintX_name "neg"

neg_uintX_import : Nat -> Import
neg_uintX_import = uintX_import "neg"

export
[neg_uint8] PrimFn where
    eval [ConstValue (B8 a)] = Just $ NewValue $ ConstValue $ B8 (-a)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [neg_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 8) args]

export
[neg_uint16] PrimFn where
    eval [ConstValue (B16 a)] = Just $ NewValue $ ConstValue $ B16 (-a)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [neg_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 16) args]

export
[neg_uint32] PrimFn where
    eval [ConstValue (B32 a)] = Just $ NewValue $ ConstValue $ B32 (-a)
    eval _ = Nothing
    
    implicits = singleton range_check_builtin
    imports = fromList [neg_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 32) args]

export
[neg_uint64] PrimFn where
    eval [ConstValue (B64 a)] = Just $ NewValue $ ConstValue $ B64 (-a)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [neg_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT SHL
---------------------------------------------------------------------------------------------------
shl_uintX_name : Nat -> CairoName
shl_uintX_name = uintX_name "shl"

shl_uintX_import : Nat -> Import
shl_uintX_import = uintX_import "shl"

export
[shl_uint8] PrimFn where
    apStable = False

    eval [_, ConstValue(B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue(B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__shl_Bits8 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 8) args]

export
[shl_uint16] PrimFn where
    apStable = False

    eval [_, ConstValue(B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__shl_Bits16 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 16) args]

export
[shl_uint32] PrimFn where
    apStable = False

    eval [_, ConstValue(B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__shl_Bits32 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 32) args]

export
[shl_uint64] PrimFn where
    apStable = False

    eval [_, ConstValue(B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__shl_Bits64 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shl_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 64) args] 


---------------------------------------------------------------------------------------------------
-- UINT SHR
---------------------------------------------------------------------------------------------------
shr_uintX_name : Nat -> CairoName
shr_uintX_name = uintX_name "shr"

shr_uintX_import : Nat -> Import
shr_uintX_import = uintX_import "shr"

export
[shr_uint8] PrimFn where
    apStable = False

    eval [_, ConstValue(B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__shr_Bits8 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 8) args]

export
[shr_uint16] PrimFn where
    apStable = False

    eval [_, ConstValue(B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__shr_Bits16 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 16) args]

export
[shr_uint32] PrimFn where
    apStable = False

    eval [_, ConstValue(B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__shr_Bits32 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 32) args]

export
[shr_uint64] PrimFn where
    apStable = False

    eval [_, ConstValue(B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__shr_Bits64 (cast a) (cast b))
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [shr_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 64) args]  


---------------------------------------------------------------------------------------------------
-- UINT AND
---------------------------------------------------------------------------------------------------

and_uintX_code : CairoReg -> CairoReg -> CairoReg -> CairoReg -> CairoReg -> String
and_uintX_code r bitwise_ptr_in bitwise_ptr_out x y = """
    assert [\{compileReg bitwise_ptr_in}] = \{compileReg x}  
    assert [\{compileReg bitwise_ptr_in}+1] = \{compileReg y}
    \{ compileRegDecl bitwise_ptr_out} = \{compileReg bitwise_ptr_in} + BitwiseBuiltin.SIZE
    \{ compileRegDecl r } = [\{compileReg bitwise_ptr_in}+2]

"""

and_uintX : Nat -> CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
and_uintX _ res [a,b] implicits = 
  case lookup bitwise_builtin implicits of
        Just (bw_in, bw_out) => Raw $ and_uintX_code res bw_in bw_out a b
        Nothing => assert_total $ idris_crash "bitwise_ptr not found"
and_uintX nBits _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode and_uint\{show nBits}"

export
[and_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ NewValue $ ConstValue $ B8 0
    eval [ConstValue (B8 0), _] = Just $ NewValue $ ConstValue $ B8 0
    eval [_, ConstValue (B8 255)] = Just $ ArgValue 0
    eval [ConstValue (B8 255), _] = Just $ ArgValue 1
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__and_Bits8 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = and_uintX 8

export
[and_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ NewValue $ ConstValue $ B16 0
    eval [ConstValue (B16 0), _] = Just $ NewValue $ ConstValue $ B16 0
    eval [_, ConstValue (B16 65535)] = Just $ ArgValue 0
    eval [ConstValue (B16 65535), _] = Just $ ArgValue 1
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__and_Bits16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = and_uintX 16

export
[and_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ NewValue $ ConstValue $ B32 0
    eval [ConstValue (B32 0), _] = Just $ NewValue $ ConstValue $ B32 0
    eval [_, ConstValue (B32 4294967295)] = Just $ ArgValue 0
    eval [ConstValue (B32 4294967295), _] = Just $ ArgValue 1
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__and_Bits32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = and_uintX 32

export
[and_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ NewValue $ ConstValue $ B64 0
    eval [ConstValue (B64 0), _] = Just $ NewValue $ ConstValue $ B64 0
    eval [_, ConstValue (B64 18446744073709551615)] = Just $ ArgValue 0
    eval [ConstValue (B64 18446744073709551615), _] = Just $ ArgValue 1
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__and_Bits64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = and_uintX 64


---------------------------------------------------------------------------------------------------
-- UINT OR
---------------------------------------------------------------------------------------------------
or_uintX_code : CairoReg -> CairoReg -> CairoReg -> CairoReg -> CairoReg -> String
or_uintX_code r bitwise_ptr_in bitwise_ptr_out x y = """
    assert [\{compileReg bitwise_ptr_in}] = \{compileReg x}  
    assert [\{compileReg bitwise_ptr_in}+1] = \{compileReg y}
    \{ compileRegDecl bitwise_ptr_out} = \{compileReg bitwise_ptr_in} + BitwiseBuiltin.SIZE
    \{ compileRegDecl r } = [\{compileReg bitwise_ptr_in}+4]

"""

or_uintX : Nat -> CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
or_uintX _ res [a,b] implicits = 
  case lookup bitwise_builtin implicits of
        Just (bw_in, bw_out) => Raw $ or_uintX_code res bw_in bw_out a b
        Nothing => assert_total $ idris_crash "bitwise_ptr not found"
or_uintX nBits _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode or_uint\{show nBits}"


export
[or_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (B8 255)] = Just $ NewValue $ ConstValue $ B8 255
    eval [ConstValue (B8 255), _] = Just $ NewValue $ ConstValue $ B8 255
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__or_Bits8 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = or_uintX 8

export
[or_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (B16 65535)] = Just $ NewValue $ ConstValue $ B16 65535
    eval [ConstValue (B16 65535), _] = Just $ NewValue $ ConstValue $ B16 65535
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__or_Bits16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = or_uintX 16

export
[or_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (B32 4294967295)] = Just $ NewValue $ ConstValue $ B32 4294967295
    eval [ConstValue (B32 4294967295), _] = Just $ NewValue $ ConstValue $ B32 4294967295
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__or_Bits32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = or_uintX 32

export
[or_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (B64 18446744073709551615)] = Just $ NewValue $ ConstValue $ B64 18446744073709551615
    eval [ConstValue (B64 18446744073709551615), _] = Just $ NewValue $ ConstValue $ B64 18446744073709551615
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__or_Bits64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = or_uintX 64

---------------------------------------------------------------------------------------------------
-- UINT XOR
---------------------------------------------------------------------------------------------------
xor_uintX_code : CairoReg -> CairoReg -> CairoReg -> CairoReg -> CairoReg -> String
xor_uintX_code r bitwise_ptr_in bitwise_ptr_out x y = """
    assert [\{compileReg bitwise_ptr_in}] = \{compileReg x}  
    assert [\{compileReg bitwise_ptr_in}+1] = \{compileReg y}
    \{ compileRegDecl bitwise_ptr_out} = \{compileReg bitwise_ptr_in} + BitwiseBuiltin.SIZE
    \{ compileRegDecl r } = [\{compileReg bitwise_ptr_in}+3]

"""

xor_uintX : Nat -> CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
xor_uintX _ res [a,b] implicits = 
  case lookup bitwise_builtin implicits of
        Just (bw_in, bw_out) => Raw $ xor_uintX_code res bw_in bw_out a b
        Nothing => assert_total $ idris_crash "bitwise_ptr not found"
xor_uintX nBits _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode xor_uint\{show nBits}"

export
[xor_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 0), _] = Just $ ArgValue 1
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__xor_Bits8 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = xor_uintX 8

export
[xor_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 0), _] = Just $ ArgValue 1
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__xor_Bits16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = xor_uintX 16

export
[xor_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 0), _] = Just $ ArgValue 1
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__xor_Bits32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = xor_uintX 32

export
[xor_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 0), _] = Just $ ArgValue 1
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__xor_Bits64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode _ = xor_uintX 64


---------------------------------------------------------------------------------------------------
-- UINT LT
---------------------------------------------------------------------------------------------------
lt_uintX_name : CairoName
lt_uintX_name = makeBuiltinName "lt_uint"

lt_uintX_import : Import
lt_uintX_import = MkImport "skyro.uint" "uint_lt" (Just "lt_uint")

export
[lt_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name args]

export
[lt_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name args]

export
[lt_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name args]

export
[lt_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name args]

---------------------------------------------------------------------------------------------------
-- UINT LTE
---------------------------------------------------------------------------------------------------
lte_uintX_name : CairoName
lte_uintX_name = makeBuiltinName "lte_uint"

lte_uintX_import : Import
lte_uintX_import = MkImport "skyro.uint" "uint_lte" (Just "lte_uint")


export
[lte_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name args]

export
[lte_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name args]

export
[lte_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name args]

export
[lte_uint64] PrimFn where
    eval [ ConstValue (B64 a),  ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name args]

---------------------------------------------------------------------------------------------------
-- UINT EQ
---------------------------------------------------------------------------------------------------
export
[eq_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_uint8" r a i

export
[eq_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_uint16" r a i

export
[eq_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_uint32" r a i

export
[eq_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode _ r a i = Raw $ compileEqOp "eq_uint64" r a i

---------------------------------------------------------------------------------------------------
-- UINT GTE
-- Implementation uses flipped arguments to lte
---------------------------------------------------------------------------------------------------

export
[gte_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name (reverse args)]

export
[gte_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name (reverse args)]

export
[gte_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name (reverse args)]

export
[gte_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lte_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lte_uintX_name (reverse args)]

---------------------------------------------------------------------------------------------------
-- UINT GT
-- Implementation uses flipped arguments to lt
---------------------------------------------------------------------------------------------------

export
[gt_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] =Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name (reverse args)]

export
[gt_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name (reverse args)]

export
[gt_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name (reverse args)]

export
[gt_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [lt_uintX_import]
    generateCode _ res args implicits = Instructions [CALL [res] implicits lt_uintX_name (reverse args)]

---------------------------------------------------------------------------------------------------
-- UINT CAST
---------------------------------------------------------------------------------------------------
cast_uintX_name : Nat -> CairoName
cast_uintX_name = uintX_name "cast"

cast_uintX_import : Nat -> Import
cast_uintX_import = uintX_import "cast"

export
[cast_to_uint8] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B8 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_uintX_import 8]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 8) args]

export
[cast_to_uint16] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B16 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_uintX_import 16]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 16) args]

export
[cast_to_uint32] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B32 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_uintX_import 32]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 32) args]

export
[cast_to_uint64] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B64 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    imports = fromList [cast_uintX_import 64]
    generateCode _ res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 64) args]
