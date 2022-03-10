||| Primitive operations for fixed size, unsigned integers. 
module Primitives.UInt

import Primitives.Common
import Core.Context
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import CommonDef
import CodeGen.CodeGenHelper

---------------------------------------------------------------------------------------------------
-- UINT ADD
---------------------------------------------------------------------------------------------------
add_uintX_name : Nat -> Name
add_uintX_name nBits = makeBuiltinName "add_uint\{show nBits}"

add_uintX_code : Name -> Nat -> String
add_uintX_code name nBits = """
    # Adds two uints
    # Returns the result as a uint
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local carry : felt
        %{ (ids.carry, ids.res) = divmod(ids.a + ids.b, \{show shift}) %}

        assert carry * carry = carry  # carry is 0 or 1
        assert res = a + b - carry * \{show shift}
        
        # inlined uint_check(res)
        assert [range_check_ptr] = res
        assert [range_check_ptr+1] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+2
        
        return (res, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

add_uintX : Nat -> (Name, Lazy CairoDef)
add_uintX nBits = (name, def)
  where name : Name
        name = add_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (add_uintX_code name nBits)) 2 1

export
[add_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 0), _] = Just $ ArgValue 1
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_uintX_name 8) args]

export
[add_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 0), _] = Just $ ArgValue 1
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_uintX_name 16) args]

export
[add_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 0), _] = Just $ ArgValue 1
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_uintX_name 32) args]

export
[add_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 0), _] = Just $ ArgValue 1
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_uintX_name 64) args]

---------------------------------------------------------------------------------------------------
-- UINT SUB
---------------------------------------------------------------------------------------------------
sub_uintX_name : Nat -> Name
sub_uintX_name nBits = makeBuiltinName "sub_uint\{show nBits}"

sub_uintX_code : Name -> Nat -> String
sub_uintX_code name nBits = """
    # Subtracts two integers.
    # Returns the result as a uint.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local borrow : felt
        %{
            (carry, ids.res) = divmod(ids.a - ids.b, \{show shift}) 
            ids.borrow = -carry  # if b > a then carry is -1
        %}

        assert borrow * borrow = borrow  # borrow is 0 or 1
        assert res = a - b + borrow * \{show shift}
        # inlined uint_check(res)
        assert [range_check_ptr] = res
        assert [range_check_ptr+1] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+2
        
        return (res, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

sub_uintX : Nat -> (Name, Lazy CairoDef)
sub_uintX nBits = (name, def)
  where name : Name
        name = sub_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (sub_uintX_code name nBits)) 2 1

export
[sub_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 8) args]

export
[sub_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 16) args]

export
[sub_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 32) args]

export
[sub_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_uintX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT MUL
---------------------------------------------------------------------------------------------------
mul_uintX_name : Nat -> Name
mul_uintX_name nBits = makeBuiltinName "mul_uint\{show nBits}"

mul_uintX_code : Name -> Nat -> String
mul_uintX_code name nBits = """
    # Multiplies two uint.
    # Returns the result
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local offset : felt
        %{ (ids.offset, ids.res) = divmod(ids.a * ids.b, \{show shift}) %}

        # Check offset can not trigger overflow / underflow
        #  to trigger overflow offset*SHIFT must be negative
        #  to trigger underflow offset*SHIFT must be > PRIME - (SHIFT-1)**2
        #    Note: 2**128 (rangecheck) < PRIME - (SHIFT-1)**2 (e.g: 64 => approx 2**128 < 2**192? - 2**128) 
        #    Note: Max needed offset*SHIFT = (SHIFT-1)*(SHIFT-1)- SHIFT = (SHIFT-2)*(SHIFT-1) < SHIFT**2
        #	 Note: for SHIFT = 2 ** 64 => offset*SHIFT < 2**128 ((2**64)**2)
        tempvar realOffset = offset * \{show shift}
        assert [range_check_ptr] = realOffset # is positive & smaller 2**128 (this is exactly range_check semantic)
        assert res = a * b - realOffset
        
        # inlined uint_check(res)
        assert [range_check_ptr+1] = res
        assert [range_check_ptr+2] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+3
        
        return (res, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

mul_uintX : Nat -> (Name, Lazy CairoDef)
mul_uintX nBits = (name, def)
  where name : Name
        name = mul_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (mul_uintX_code name nBits)) 2 1

export
[mul_uint8] PrimFn where
    eval [_, ConstValue (B8 1)] = Just $ ArgValue 0
    eval [ConstValue (B8 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B8 0)] = Just $ NewValue $ ConstValue $ B8 0
    eval [ConstValue (B8 0), _] = Just $ NewValue $ ConstValue $ B8 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 8) args]

export
[mul_uint16] PrimFn where
    eval [_, ConstValue (B16 1)] = Just $ ArgValue 0
    eval [ConstValue (B16 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B16 0)] = Just $ NewValue $ ConstValue $ B16 0
    eval [ConstValue (B16 0), _] = Just $ NewValue $ ConstValue $ B16 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 16) args]

export
[mul_uint32] PrimFn where
    eval [_, ConstValue (B32 1)] = Just $ ArgValue 0
    eval [ConstValue (B32 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B32 0)] = Just $ NewValue $ ConstValue $ B32 0
    eval [ConstValue (B32 0), _] = Just $ NewValue $ ConstValue $ B32 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 32) args]

export
[mul_uint64] PrimFn where
    eval [_, ConstValue (B64 1)] = Just $ ArgValue 0
    eval [ConstValue (B64 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (B64 0)] = Just $ NewValue $ ConstValue $ B64 0
    eval [ConstValue (B64 0), _] = Just $ NewValue $ ConstValue $ B64 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_uintX_name 64) args]



---------------------------------------------------------------------------------------------------
-- UINT DIV
---------------------------------------------------------------------------------------------------
div_uintX_name : Nat -> Name
div_uintX_name nBits = makeBuiltinName "div_uint\{show nBits}"

div_uintX_code : Name -> Nat -> String
div_uintX_code name nBits = """
    # Division between uint.
    # Returns the quotient.
    # Conforms to Idris specifications: division by 0 yields error.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (quotient : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local rem : felt
        #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
        # Question: is it ok to fail in hint or is a check with assert 0 =  1 needed
        %{ (ids.res, ids.rem) = divmod(ids.a, ids.b) %}

        # Check res * b + rem can not trigger overflow / underflow
        #  Note: 0 < b < 2**64 -- given by semantics
        #  Note: 0 <= res < 2**64 -- checked by uint_check
        #  Implies: 0 <= res * b < 2**128
        #  Note: 0 < rem < 2**64 -- (must be checked -- as hint can lie)
        #  If we weaken to: 0 < rem < 2**128 (rangecheck)
        #  then still: 0 < res * b + rem < 2**129 < PRIME / 2 (positive numbers)
        
        assert [range_check_ptr] = rem 				# is positive & smaller 2**128 (this is exactly range_check semantic)
        # Note: will fail if b = 0 which is the expected behaviour
        assert [range_check_ptr+1] = b - rem - 1	# rem < b 
        assert res * b + rem = a
        
        # inlined uint_check(res) -- implied as res must be between 0 and a to pass the checks & a is valid (input)
        # assert [range_check_ptr+2] = res
        # assert [range_check_ptr+3] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+2
        
        return (res, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

div_uintX : Nat -> (Name, Lazy CairoDef)
div_uintX nBits = (name, def)
  where name : Name
        name = div_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (div_uintX_code name nBits)) 2 1

export
[div_uint8] PrimFn where
    eval [_, ConstValue (B8 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B8 1)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_uintX_name 8) args]

export
[div_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B16 1)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_uintX_name 16) args]

export
[div_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B32 1)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_uintX_name 32) args]

export
[div_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (B64 1)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_uintX_name 64) args] 

---------------------------------------------------------------------------------------------------
-- UINT MOD
---------------------------------------------------------------------------------------------------
mod_uintX_name : Nat -> Name
mod_uintX_name nBits = makeBuiltinName "mod_uint\{show nBits}"

mod_uintX_code : Name -> Nat -> String
mod_uintX_code name nBits = """
    # Division between uint.
    # Returns the remainder.
    # Conforms to Idris specifications: division by 0 yields error.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (remainder : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local rem : felt
        #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
        # Question: is it ok to fail in hint or is a check with assert 0 =  1 needed
        %{ (ids.res, ids.rem) = divmod(ids.a, ids.b) %}

        # Check res * b + rem can not trigger overflow / underflow
        #  Note: 0 < b < 2**64 -- given by semantics
        #  Note: 0 <= res < 2**64 -- checked by uint_check
        #  Implies: 0 <= res * b < 2**128
        #  Note: 0 < rem < 2**64 -- (must be checked -- as hint can lie)
        #  If we weaken to: 0 < rem < 2**128 (rangecheck)
        #  then still: 0 < res * b + rem < 2**129 < PRIME / 2 (positive numbers)
        
        assert [range_check_ptr] = rem 				# is positive & smaller 2**128 (this is exactly range_check semantic)
        # Note: will fail if b = 0 which is the expected behaviour
        assert [range_check_ptr+1] = b - rem - 1	# rem < b 
        assert res * b + rem = a
        
        # inlined uint_check(res) -- implied as res must be between 0 and a to pass the checks & a is valid (input)
        # assert [range_check_ptr+2] = res
        # assert [range_check_ptr+3] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+2
        
        return (rem, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

mod_uintX : Nat -> (Name, Lazy CairoDef)
mod_uintX nBits = (name, def)
  where name : Name
        name = mod_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (mod_uintX_code name nBits)) 2 1

export
[mod_uint8] PrimFn where
    eval [_, ConstValue (B8 1)] = Just $ NewValue $ ConstValue $ B8 0
    eval [_, ConstValue (B8 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 8) args]

export
[mod_uint16] PrimFn where
    eval [_, ConstValue (B16 1)] = Just $ NewValue $ ConstValue $ B16 0
    eval [_, ConstValue (B16 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 16) args]

export
[mod_uint32] PrimFn where
    eval [_, ConstValue (B32 1)] = Just $ NewValue $ ConstValue $ B32 0
    eval [_, ConstValue (B32 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 32) args]

export
[mod_uint64] PrimFn where
    eval [_, ConstValue (B64 1)] = Just $ NewValue $ ConstValue $ B64 0
    eval [_, ConstValue (B64 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_uintX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT NEG:
---------------------------------------------------------------------------------------------------
neg_uintX_name : Nat -> Name
neg_uintX_name nBits = makeBuiltinName "neg_uint\{show nBits}"

neg_uintX_code : Name -> Nat -> String
neg_uintX_code name nBits = """
    # Returns -x the negation of x, in the sense that it is that number such that x + -x = 0, if addition wraps around such that 255+1=0.
    # Note that -128 is 128, since 128+128=0.
    func \{cairoName name}(range_check_ptr, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local borrow : felt
        %{
            (carry, ids.res) = divmod(0 - ids.b, \{show shift}) 
            ids.borrow = -carry  # if b > 0 then carry is -1
        %}

        assert borrow * borrow = borrow  # borrow is 0 or 1
        assert res = - b + borrow * \{show shift}
        # inlined uint_check(res)
        assert [range_check_ptr] = res
        assert [range_check_ptr+1] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+2
        
        return (res, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

neg_uintX : Nat -> (Name, Lazy CairoDef)
neg_uintX nBits = (name, def)
  where name : Name
        name = neg_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (neg_uintX_code name nBits)) 1 1

export
[neg_uint8] PrimFn where
    eval [ConstValue (B8 a)] = Just $ NewValue $ ConstValue $ B8 (-a)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [neg_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 8) args]

export
[neg_uint16] PrimFn where
    eval [ConstValue (B16 a)] = Just $ NewValue $ ConstValue $ B16 (-a)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [neg_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 16) args]

export
[neg_uint32] PrimFn where
    eval [ConstValue (B32 a)] = Just $ NewValue $ ConstValue $ B32 (-a)
    eval _ = Nothing
    
    implicits = singleton range_check_builtin
    dependencies = fromList [neg_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 32) args]

export
[neg_uint64] PrimFn where
    eval [ConstValue (B64 a)] = Just $ NewValue $ ConstValue $ B64 (-a)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [neg_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_uintX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT SHL
---------------------------------------------------------------------------------------------------
shl_uintX_name : Nat -> Name
shl_uintX_name nBits = makeBuiltinName "shl_uint\{show nBits}"

-- Todo: Analyze complexity of pow and see if a bitpattern based mult is more efficient
shl_uintX_code : Name -> Nat -> String
shl_uintX_code name nBits = """
    # Computes the logical left shift of a uint.
    #  Note: We should consider not supporting these
    #  Reason: Programmers expect them to be quick and often try to optimize by replacing some *,/ with <<, >>
    #          But in cairo these are horrendibly slow
    #		   Inconviniently these are the only one requiring imports and they are the only one that are not ap stable
    func \{cairoName name}(range_check_ptr, a : felt,  b : felt) -> (res : felt, range_check_ptr):
        
        #inlined uint_pow2
        # If b >= BIT_LENGTH, the result will be zero modulo 2**BIT_LENGTH.
        tempvar res
        %{ids.res = 1 if ids.b < \{show nBits} else 0 %}
        # b < 2**128 & a < 2**128 is given by semantics
        # BIT_LENGTH <= b
        if res == 0: 
            assert [range_check_ptr] = b - \{show nBits}
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        #b < BIT_LENGTH
        else:
            assert [range_check_ptr] = \{show (nBits `minus` 1)} - b
            let range_check_ptr = range_check_ptr + 1
            let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
            \{cairoName (mul_uintX_name nBits)}(range_check_ptr, a, c)
            ret
        end
    end
"""


shl_uintX : Nat -> (Name, Lazy CairoDef)
shl_uintX nBits = (name, def)
  where name : Name
        name = shl_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (shl_uintX_code name nBits)) 2 1

shl_uintX_imports : SortedSet Import
shl_uintX_imports = singleton (MkImport "starkware.cairo.common.pow" "pow")

export
[shl_uint8] PrimFn where
    apStable = False

    eval [_, ConstValue(B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue(B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__shl_Bits8 (cast a) (cast b))
    eval _ = Nothing

    imports = shl_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shl_uintX 8, mul_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 8) args]

export
[shl_uint16] PrimFn where
    apStable = False

    eval [_, ConstValue(B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__shl_Bits16 (cast a) (cast b))
    eval _ = Nothing

    imports = shl_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shl_uintX 16, mul_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 16) args]

export
[shl_uint32] PrimFn where
    apStable = False

    eval [_, ConstValue(B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__shl_Bits32 (cast a) (cast b))
    eval _ = Nothing

    imports = shl_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shl_uintX 32, mul_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 32) args]

export
[shl_uint64] PrimFn where
    apStable = False

    eval [_, ConstValue(B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__shl_Bits64 (cast a) (cast b))
    eval _ = Nothing

    imports = shl_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shl_uintX 64, mul_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (shl_uintX_name 64) args] 


---------------------------------------------------------------------------------------------------
-- UINT SHR
---------------------------------------------------------------------------------------------------
shr_uintX_name : Nat -> Name
shr_uintX_name nBits = makeBuiltinName "shr_uint\{show nBits}"

-- Todo: Analyze complexity of pow and see if a bitpattern based div is more efficient
shr_uintX_code : Name -> Nat -> String
shr_uintX_code name nBits = """
    # Computes the logical right shift of a uint.
    #  Reason: Programmers expect them to be quick and often try to optimize by replacing some *,/ with <<, >>
    #          But in cairo these are horrendibly slow
    #		   Inconviniently these are the only one requiring imports and they are the only one that are not ap stable
    func \{cairoName name}(range_check_ptr, a : felt,  b : felt) -> (res : felt, range_check_ptr):
        #inlined uint_pow2
        # If b >= BIT_LENGTH, the result will be zero modulo 2**BIT_LENGTH.
        tempvar res
        %{ids.res = 1 if ids.b < \{show nBits} else 0 %}
        # b < 2**128 & a < 2**128 is given by semantics
        # BIT_LENGTH <= b
        if res == 0: 
            assert [range_check_ptr] = b - \{show nBits}
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        #b < BIT_LENGTH
        else:
            assert [range_check_ptr] = \{show (nBits `minus` 1)} - b
            let range_check_ptr = range_check_ptr + 1
            let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
            \{cairoName (div_uintX_name nBits)}(range_check_ptr, a, c)
            ret
        end
    end
"""


shr_uintX : Nat -> (Name, Lazy CairoDef)
shr_uintX nBits = (name, def)
  where name : Name
        name = shr_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (shr_uintX_code name nBits)) 2 1

shr_uintX_imports : SortedSet Import
shr_uintX_imports = singleton (MkImport "starkware.cairo.common.pow" "pow")


export
[shr_uint8] PrimFn where
    apStable = False

    eval [_, ConstValue(B8 0)] = Just $ ArgValue 0
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ B8 (prim__shr_Bits8 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_uintX 8, div_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 8) args]

export
[shr_uint16] PrimFn where
    apStable = False

    eval [_, ConstValue(B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__shr_Bits16 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_uintX 16, div_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 16) args]

export
[shr_uint32] PrimFn where
    apStable = False

    eval [_, ConstValue(B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__shr_Bits32 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_uintX 32, div_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 32) args]

export
[shr_uint64] PrimFn where
    apStable = False

    eval [_, ConstValue(B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__shr_Bits64 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_uintX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_uintX 64, div_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_uintX_name 64) args]  


---------------------------------------------------------------------------------------------------
-- UINT AND
{- 
func bitwise_and{bitwise_ptr : BitwiseBuiltin*}(x : felt, y : felt) -> (x_and_y : felt):
    bitwise_ptr.x = x
    bitwise_ptr.y = y
    let x_and_y = bitwise_ptr.x_and_y
    let x_xor_y = bitwise_ptr.x_xor_y
    let x_or_y = bitwise_ptr.x_or_y
    let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE
    return (x_and_y=x_and_y)
end

struct BitwiseBuiltin:
    member x : felt
    member y : felt
    member x_and_y : felt
    member x_xor_y : felt
    member x_or_y : felt
end
-}
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
    generateCode = and_uintX 8

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
    generateCode = and_uintX 16

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
    generateCode = and_uintX 32

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
    generateCode = and_uintX 64


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
    generateCode = or_uintX 8

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
    generateCode = or_uintX 16

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
    generateCode = or_uintX 32

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
    generateCode = or_uintX 64

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
    generateCode = xor_uintX 8

export
[xor_uint16] PrimFn where
    eval [_, ConstValue (B16 0)] = Just $ ArgValue 0
    eval [ConstValue (B16 0), _] = Just $ ArgValue 1
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ B16 (prim__xor_Bits16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode = xor_uintX 16

export
[xor_uint32] PrimFn where
    eval [_, ConstValue (B32 0)] = Just $ ArgValue 0
    eval [ConstValue (B32 0), _] = Just $ ArgValue 1
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ B32 (prim__xor_Bits32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode = xor_uintX 32

export
[xor_uint64] PrimFn where
    eval [_, ConstValue (B64 0)] = Just $ ArgValue 0
    eval [ConstValue (B64 0), _] = Just $ ArgValue 1
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ B64 (prim__xor_Bits64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = singleton bitwise_builtin
    generateCode = xor_uintX 64


---------------------------------------------------------------------------------------------------
-- UINT LT
---------------------------------------------------------------------------------------------------
lt_uintX_name : Name
lt_uintX_name = makeBuiltinName "lt_uint"

lt_uintX_code : Name -> String
lt_uintX_code name = """
    # Returns 1 if the first unsigned integer is less than the second unsigned integer, otherwise returns 0.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
        tempvar res
        %{ids.res = 1 if ids.a < ids.b else 0 %}
        # b < 2**128 & a < 2**128 is given by semantics
        # b <= a
        if res == 0: 
            assert [range_check_ptr] = a - b - 0 # - 0 is for ap stability improves worse case in code gen
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        #a < b
        else:
            assert [range_check_ptr] = b - a - 1
            let range_check_ptr = range_check_ptr + 1
            return (1, range_check_ptr)
        end
    end
"""

lt_uintX : (Name, Lazy CairoDef)
lt_uintX = (lt_uintX_name, def)
  where def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (lt_uintX_code lt_uintX_name)) 2 1

generateLtCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateLtCallCode res args implicits = Instructions [CALL [res] implicits lt_uintX_name args] 

export
[lt_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateLtCallCode

export
[lt_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateLtCallCode

export
[lt_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateLtCallCode

export
[lt_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateLtCallCode

---------------------------------------------------------------------------------------------------
-- UINT LTE
---------------------------------------------------------------------------------------------------
lte_uintX_name : Name
lte_uintX_name = makeBuiltinName "lte_uint"

lte_uintX_code : Name -> String
lte_uintX_code name = """
    # Returns 1 if the first unsigned integer is less than or equal to the second unsigned integer, otherwise returns 0.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
        tempvar res
        %{ids.res = 1 if ids.a <= ids.b else 0 %}
        # b < 2**128 & a < 2**128 is given by semantics
        # b < a
        if res == 0: 
            assert [range_check_ptr] = a - b - 1	
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        #a <= b
        else:
            assert [range_check_ptr] = b - a - 0	#+0 is for ap stability improves worse case in code gen
            let range_check_ptr = range_check_ptr + 1
            return (1, range_check_ptr)
        end
    end
"""

lte_uintX : (Name, Lazy CairoDef)
lte_uintX = (lte_uintX_name, def)
  where def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (lte_uintX_code lte_uintX_name)) 2 1

generateLteCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateLteCallCode res args implicits = Instructions [CALL [res] implicits lte_uintX_name args] 


export
[lte_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateLteCallCode

export
[lte_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateLteCallCode

export
[lte_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateLteCallCode

export
[lte_uint64] PrimFn where
    eval [ ConstValue (B64 a),  ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateLteCallCode

---------------------------------------------------------------------------------------------------
-- UINT EQ
---------------------------------------------------------------------------------------------------
export
[eq_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_uint8" r a i

export
[eq_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_uint16" r a i

export
[eq_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_uint32" r a i

export
[eq_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_uint64" r a i

---------------------------------------------------------------------------------------------------
-- UINT GTE
-- Implementation uses flipped arguments to lte
---------------------------------------------------------------------------------------------------

generateGteCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateGteCallCode res [a,b] implicits = Instructions [CALL [res] implicits lte_uintX_name [b,a]] -- Flipped arguments
generateGteCallCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode gte_uintX"

export
[gte_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateGteCallCode

export
[gte_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateGteCallCode

export
[gte_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateGteCallCode

export
[gte_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_uintX]
    generateCode = generateGteCallCode

---------------------------------------------------------------------------------------------------
-- UINT GT
-- Implementation uses flipped arguments to lt
---------------------------------------------------------------------------------------------------

generateGtCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateGtCallCode res [a,b] implicits = Instructions [CALL [res] implicits lt_uintX_name [b,a]] -- Flipped arguments
generateGtCallCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode gt_uintX"

export
[gt_uint8] PrimFn where
    eval [ConstValue (B8 a), ConstValue (B8 b)] =Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateGtCallCode

export
[gt_uint16] PrimFn where
    eval [ConstValue (B16 a), ConstValue (B16 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateGtCallCode

export
[gt_uint32] PrimFn where
    eval [ConstValue (B32 a), ConstValue (B32 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateGtCallCode

export
[gt_uint64] PrimFn where
    eval [ConstValue (B64 a), ConstValue (B64 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_uintX]
    generateCode = generateGtCallCode

---------------------------------------------------------------------------------------------------
-- UINT CAST
---------------------------------------------------------------------------------------------------
cast_uintX_name : Nat -> Name
cast_uintX_name nBits = makeBuiltinName "cast_uint\{show nBits}"

cast_uintX_code : Name -> Nat -> String
cast_uintX_code name nBits = """
    # Casts to uint\{show nBits}
    # Returns the result as uint\{show nBits}.
    func \{cairoName name}(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local offset : felt
        %{ (ids.offset, ids.res) = divmod(ids.a, \{show shift}) %}

        # Check offset can not trigger overflow / underflow
        #  to trigger overflow offset*SHIFT must be negative
        #  to trigger underflow offset*SHIFT must be > PRIME - (SHIFT-1)**2
        #    Note: 2**128 (rangecheck) < PRIME - (SHIFT-1)**2 (e.g: 64 => approx 2**128 < 2**192? - 2**128) 
        #    Note: Max needed offset*SHIFT = (SHIFT-1)*(SHIFT-1)- SHIFT = (SHIFT-2)*(SHIFT-1) < SHIFT**2
        #	 Note: for SHIFT = 2 ** 64 => offset*SHIFT < 2**128 ((2**64)**2)
        tempvar realOffset = offset * \{show shift}
        assert [range_check_ptr] = realOffset # is positive & smaller 2**128 (this is exactly range_check semantic)
        assert res = a - realOffset
        
        # inlined uint_check(res)
        assert [range_check_ptr+1] = res
        assert [range_check_ptr+2] = \{show (shift - 1)} - res
        let range_check_ptr = range_check_ptr+3
        
        return (res, range_check_ptr)
    end
"""
  where shift : Integer
        shift = pow2 nBits

cast_uintX : Nat -> (Name, Lazy CairoDef)
cast_uintX nBits = (name, def)
  where name : Name
        name = cast_uintX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (cast_uintX_code name nBits)) 1 1

export
[cast_to_uint8] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B8 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_uintX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 8) args]

export
[cast_to_uint16] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B16 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_uintX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 16) args]

export
[cast_to_uint32] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B32 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_uintX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 32) args]

export
[cast_to_uint64] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ B64 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_uintX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_uintX_name 64) args]
