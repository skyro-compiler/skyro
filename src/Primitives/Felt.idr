||| Primitive operations for the Felt data type.
module Primitives.Felt

import Core.Context
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import Primitives.Common
import CommonDef
import CodeGen.CodeGenHelper


-- https://github.com/starkware-libs/cairo-lang/blob/cf8266fd5d1ff66962579ff7967ac5cdcf699f77/src/starkware/cairo/lang/cairo_constants.py
-- 2^251 + 17 * 2^192 + 1
public export
PRIME : Integer
PRIME = 3618502788666131213697322783095070105623107215331596699973092056135872020481

public export
HALF_PRIME : Integer
HALF_PRIME = PRIME `div` 2
-- 1809251394333065606848661391547535052811553607665798349986546028067936010240

-- Converts i to an integer in the range (-prime/2, prime/2) which is equivalent to val modulo prime.
-- https://github.com/starkware-libs/cairo-lang/blob/3d33c4e829a87bc3d88cf04ed6a489e788918b8b/src/starkware/cairo/lang/compiler/expression_simplifier.py#L147
export
integerToFelt : Integer -> Integer 
integerToFelt i = (i + HALF_PRIME) `mod` PRIME - HALF_PRIME

-- Extended Euclidian Algorithm
-- extendedEu a PRIME computes (a^(-1),_)
extendedEu : Integer -> Integer -> (Integer, Integer)
extendedEu a 0 = (1, 0)
extendedEu a b = 
  let q = a `div` b
      r = a `mod` b
      (s, t) = extendedEu b r
   in (t, s - q * t)

-- a / b
export
feltDiv : Integer -> Integer -> Integer
feltDiv a b = let (invB, _) = extendedEu b PRIME -- computes b^(-1)
                  res = (a * invB) `mod` PRIME
               in integerToFelt res

---------------------------------------------------------------------

feltBinOp : (op: String) -> CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
feltBinOp op r [a,b] impls = 
  if impls == empty
    then Raw "\{ compileRegDecl r } = \{ compileReg a } \{op} \{ compileReg b }\n"
    else assert_total $ idris_crash "no implicits expected for generateCodeBinOp: \{op}"
feltBinOp op _ _ _ = assert_total $ idris_crash "Bad arguments to feltBinOp: \{op}"


export
[add_felt] PrimFn where
    eval [_, ConstValue (F 0)] = Just $ ArgValue 0
    eval [ConstValue (F 0), _] = Just $ ArgValue 1
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (a+b)
    eval _ = Nothing

    generateCode = feltBinOp "+"

export
[sub_felt] PrimFn where
    eval [_, ConstValue (F 0)] = Just $ ArgValue 0
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (a-b)
    eval _ = Nothing

    generateCode = feltBinOp "-"

export
[mul_felt] PrimFn where
    eval [_, ConstValue (F 1)] = Just $ ArgValue 0
    eval [ConstValue (F 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (F 0)] = Just $ NewValue $ ConstValue $ F 0
    eval [ConstValue (F 0), _] = Just $ NewValue $ ConstValue $ F 0
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (a*b)
    eval _ = Nothing

    generateCode = feltBinOp "*"

export
[div_felt] PrimFn where
    eval [_, ConstValue (F 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (F 1)] = Just $ ArgValue 0
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F (feltDiv a b)
    eval _ = Nothing

    generateCode = feltBinOp "/"

export
[neg_felt] PrimFn where
    eval [ConstValue (F a)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (-a)
    eval _ = Nothing

    generateCode r [a] _ = Raw "\{ compileRegDecl r } = -\{ compileReg a }\n"
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode neg_felt"

--Todo: should we even allow this (should we have shifts in general)
export
[shl_felt] PrimFn where
    eval [_, ConstValue(F 0)] = Just $ ArgValue 0
    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (prim__shl_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shl_felt"


--Todo: should we even allow this (should we have shifts in general)
export
[shr_felt] PrimFn where
    eval [_, ConstValue(F 0)] = Just $ ArgValue 0
    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (prim__shr_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shr_felt"

-- Duplicate of UInt.and_uintX_code
and_felt_code : CairoReg -> CairoReg -> CairoReg -> CairoReg -> CairoReg -> String
and_felt_code r bitwise_ptr_in bitwise_ptr_out x y = """
    assert [\{compileReg bitwise_ptr_in}] = \{compileReg x}  
    assert [\{compileReg bitwise_ptr_in}+1] = \{compileReg y}
    \{ compileRegDecl bitwise_ptr_out} = \{compileReg bitwise_ptr_in} + BitwiseBuiltin.SIZE
    \{ compileRegDecl r } = [\{compileReg bitwise_ptr_in}+2]

"""
export
[and_felt] PrimFn where
    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (prim__and_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode res [a,b] implicits = 
        case lookup bitwise_builtin implicits of
            Just (bw_in, bw_out) => Raw $ and_felt_code res bw_in bw_out a b
            Nothing => assert_total $ idris_crash "bitwise_ptr not found"
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode and_felt"


-- Duplicate of UInt.or_uintX_code
or_felt_code : CairoReg -> CairoReg -> CairoReg -> CairoReg -> CairoReg -> String
or_felt_code r bitwise_ptr_in bitwise_ptr_out x y = """
    assert [\{compileReg bitwise_ptr_in}] = \{compileReg x}  
    assert [\{compileReg bitwise_ptr_in}+1] = \{compileReg y}
    \{ compileRegDecl bitwise_ptr_out} = \{compileReg bitwise_ptr_in} + BitwiseBuiltin.SIZE
    \{ compileRegDecl r } = [\{compileReg bitwise_ptr_in}+4]

"""

export
[or_felt] PrimFn where
    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a),ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (prim__or_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode res [a,b] implicits = 
        case lookup bitwise_builtin implicits of
                Just (bw_in, bw_out) => Raw $ or_felt_code res bw_in bw_out a b
                Nothing => assert_total $ idris_crash "bitwise_ptr not found"
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode or_felt_code"


-- Duplicate of UInt.xor_uintX_code
xor_felt_code : CairoReg -> CairoReg -> CairoReg -> CairoReg -> CairoReg -> String
xor_felt_code r bitwise_ptr_in bitwise_ptr_out x y = """
    assert [\{compileReg bitwise_ptr_in}] = \{compileReg x}  
    assert [\{compileReg bitwise_ptr_in}+1] = \{compileReg y}
    \{ compileRegDecl bitwise_ptr_out} = \{compileReg bitwise_ptr_in} + BitwiseBuiltin.SIZE
    \{ compileRegDecl r } = [\{compileReg bitwise_ptr_in}+3]

"""

export
[xor_felt] PrimFn where
    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ F $ integerToFelt (prim__xor_Integer (cast a) (cast b))
    eval _ = Nothing

    generateCode res [a,b] implicits = 
        case lookup bitwise_builtin implicits of
                Just (bw_in, bw_out) => Raw $ xor_felt_code res bw_in bw_out a b
                Nothing => assert_total $ idris_crash "bitwise_ptr not found"
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode xor_felt"


---------------------------------------------------------------------------------------------------
-- Felt LT
---------------------------------------------------------------------------------------------------
lt_felt_name : Name
lt_felt_name = makeBuiltinName "is_lt_felt"

lt_felt_code : String
lt_felt_code = """
# Checks if the unsigned integer lift (as a number in the range [0, PRIME)) of a is lower than
# that of b.
# See split_felt() for more details.
# Returns 1 if true, 0 otherwise.
func \{cairoName lt_felt_name}(range_check_ptr,a, b) -> (res, range_check_ptr):
    %{ memory[ap] = 0 if (ids.a % PRIME) < (ids.b % PRIME) else 1 %}
    jmp not_lt if [ap] != 0; ap++
    assert_lt_felt{range_check_ptr=range_check_ptr}(a, b)
    return (1, range_check_ptr)

    not_lt:
    assert_le_felt{range_check_ptr=range_check_ptr}(b, a)
    return (0, range_check_ptr)
end

"""


export
[lt_felt] PrimFn where
    apStable = False

    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    imports = fromList [
        MkImport "starkware.cairo.common.math_cmp" "assert_lt_felt",
        MkImport "starkware.cairo.common.math_cmp" "assert_le_felt"]
    implicits = singleton range_check_builtin
    dependencies = fromList [(lt_felt_name, ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty lt_felt_code) 2 1)]
    generateCode res args implicits = Instructions [CALL [res] implicits lt_felt_name args]

---------------------------------------------------------------------------------------------------
-- Felt LTE
---------------------------------------------------------------------------------------------------
lte_felt_name : Name
lte_felt_name = makeBuiltinName "is_lte_felt"

lte_felt_code : String
lte_felt_code = """
    # Checks if the unsigned integer lift (as a number in the range [0, PRIME)) of a is lower than
    # or equal to that of b.
    # See split_felt() for more details.
    # Returns 1 if true, 0 otherwise.
    func \{cairoName lte_felt_name}(range_check_ptr, a, b) -> (res, range_check_ptr):
        %{ memory[ap] = 0 if (ids.a % PRIME) <= (ids.b % PRIME) else 1 %}
        jmp not_le if [ap] != 0; ap++
        assert_le_felt{range_check_ptr=range_check_ptr}(a, b)
        return (1, range_check_ptr)

        not_le:
        assert_lt_felt{range_check_ptr=range_check_ptr}(b, a)
        return (0, range_check_ptr)
    end

"""

export
[lte_felt] PrimFn where
    apStable = False

    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    imports = fromList [
        MkImport "starkware.cairo.common.math_cmp" "assert_lt_felt",
        MkImport "starkware.cairo.common.math_cmp" "assert_le_felt"]
    implicits = singleton range_check_builtin
    dependencies = fromList [(lte_felt_name, ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty lte_felt_code) 2 1)]
    generateCode res args implicits = Instructions [CALL [res] implicits lte_felt_name args]


---------------------------------------------------------------------------------------------------
-- Felt EQ
---------------------------------------------------------------------------------------------------
export
[eq_felt] PrimFn where
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_felt" r a i

---------------------------------------------------------------------------------------------------
-- Felt GTE 
-- Implementation uses flipped arguments to lte
---------------------------------------------------------------------------------------------------
export
[gte_felt] PrimFn where
    apStable = False

    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    imports = fromList [
        MkImport "starkware.cairo.common.math_cmp" "assert_lt_felt",
        MkImport "starkware.cairo.common.math_cmp" "assert_le_felt"]
    implicits = singleton range_check_builtin
    dependencies = fromList [(lte_felt_name, ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty lte_felt_code) 2 1)]
    generateCode res [a,b] implicits = Instructions [CALL [res] implicits lte_felt_name [b,a]] -- Flipped arguments
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode gte_felt"


---------------------------------------------------------------------------------------------------
-- Felt GT
-- Implementation uses flipped arguments to lt
---------------------------------------------------------------------------------------------------
export
[gt_felt] PrimFn where
    apStable = False

    -- Todo: Just an incorrect quick hack add real felt impl in idris2
    eval [ConstValue (F a), ConstValue (F b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    imports = fromList [
        MkImport "starkware.cairo.common.math_cmp" "assert_lt_felt",
        MkImport "starkware.cairo.common.math_cmp" "assert_le_felt"]
    implicits = singleton range_check_builtin
    dependencies = fromList [(lt_felt_name, ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty lt_felt_code) 2 1)]
    generateCode res [a,b] implicits = Instructions [CALL [res] implicits lt_felt_name [b,a]] -- Flipped arguments
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode gt_felt"

-- Todo: How to treat Integers which are larger or smaller than Felt
export
[cast_to_felt] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ F $ integerToFelt i) (constToInteger c)
    eval _ = Nothing

    generateCode r [a] _ = Raw "\{ compileRegDecl r } = \{ compileReg a } #Cast to felt\n"
    generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode cast_to_felt"
