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
-- UINT ADD
---------------------------------------------------------------------------------------------------
add_intX_name : Nat -> Name
add_intX_name nBits = makeBuiltinName "add_int\{show nBits}"

add_intX_code : Name -> Nat -> String
add_intX_code name nBits = """
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res
        local overflow
        %{ 
            raw_res = (ids.a + ids.b) % PRIME
            if (raw_res >= \{show halfShift}) & (raw_res < \{show shift}):
                (ids.overflow, ids.res) = (1, (raw_res - \{show shift}) % PRIME)
            elif (raw_res < PRIME - \{show halfShift}) & (PRIME - \{show shift} <= raw_res): 
                (ids.overflow, ids.res) = (-1 % PRIME, (raw_res + \{show shift}) % PRIME)
            else:
                (ids.overflow, ids.res) = (0, raw_res)
        %}

        assert overflow * overflow * overflow = overflow  # overflow is -1, 0 or 1
        assert res = a + b - overflow * \{show shift}
        
        #inlined int_check
        assert [range_check_ptr] = res + \{show halfShift}			#Ensure: -HALF_SHIFT <= res
        assert [range_check_ptr+1] = \{show (halfShift - 1)} - res	#Ensure: res < HALF_SHIFT
        let range_check_ptr = range_check_ptr + 2

        return (res, range_check_ptr)
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

add_intX : Nat -> (Name, Lazy CairoDef)
add_intX nBits = (name, def)
  where name : Name
        name = add_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (add_intX_code name nBits)) 2 1


-- Implements
export
[add_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I 0), _] = Just $ ArgValue 1
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_intX_name 64) args]

export
[add_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 0), _] = Just $ ArgValue 1
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_intX_name 8) args]

export
[add_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 0), _] = Just $ ArgValue 1
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_intX_name 16) args]

export
[add_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 0), _] = Just $ ArgValue 1
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_intX_name 32) args]

export
[add_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 0), _] = Just $ ArgValue 1
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a+b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [add_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (add_intX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT SUB
---------------------------------------------------------------------------------------------------
sub_intX_name : Nat -> Name
sub_intX_name nBits = makeBuiltinName "sub_int\{show nBits}"

sub_intX_code : Name -> Nat -> String
sub_intX_code name nBits = """
    # Subtraction.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res : felt
        local overflow : felt
        %{
            a_sub_b = (ids.a - ids.b) % PRIME 
            if (a_sub_b >= \{show halfShift}) & (a_sub_b < \{show shift}):
                (ids.overflow, ids.res) = (1, (a_sub_b - \{show shift}) % PRIME)
            elif (a_sub_b < PRIME - \{show halfShift}) & (PRIME - \{show shift} <= a_sub_b): 
                (ids.overflow, ids.res) = (-1 % PRIME, (a_sub_b + \{show shift}) % PRIME)
            else:
                (ids.overflow, ids.res) = (0, a_sub_b)
        %}

        assert overflow * overflow * overflow = overflow  # overflow is -1, 0 or 1
        assert res = a - b - overflow * \{show shift}
        
        #inlined int_check
        assert [range_check_ptr] = res + \{show halfShift}			#Ensure: -HALF_SHIFT <= res
        assert [range_check_ptr+1] = \{show (halfShift - 1)} - res	#Ensure: res < HALF_SHIFT
        let range_check_ptr = range_check_ptr + 2
        
        return (res,range_check_ptr)
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

sub_intX : Nat -> (Name, Lazy CairoDef)
sub_intX nBits = (name, def)
  where name : Name
        name = sub_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (sub_intX_code name nBits)) 2 1

export
[sub_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_intX_name 64) args]

export
[sub_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_intX_name 8) args]

export
[sub_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_intX_name 16) args]

export
[sub_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_intX_name 32) args]

export
[sub_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a-b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [sub_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (sub_intX_name 64) args]


---------------------------------------------------------------------------------------------------
-- UINT MUL
---------------------------------------------------------------------------------------------------
mul_intX_name : Nat -> Name
mul_intX_name nBits = makeBuiltinName "mul_int\{show nBits}"

mul_intX_code : Name -> Nat -> String
mul_intX_code name nBits = """
    # Multiplies two int.
    # Returns the result as int.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res
        local offset	
        %{
            from starkware.cairo.common.math_utils import as_int
            rawMult = ((as_int(ids.a, PRIME) * as_int(ids.b, PRIME)) + \{show halfShift})
            (rawOffset, resRaw) = divmod(rawMult, \{show shift}) 
            ids.offset = rawOffset % PRIME
            ids.res = (resRaw - \{show halfShift}) % PRIME
        %}

        # Check offset can not trigger overflow / underflow
        #  Note: Max valid offset absolute = HALF_SHIFT*HALF_SHIFT/SHIFT = (SHIFT*SHIFT)/4*SHIFT = SHIFT/4
        #  For simplicity we weaken to -HALF_SHIFT <= offset <= HALF_SHIFT then no overflow (for 64bit): -2**128 <= +/-(2**63 * 2**63) +/- (2**63 * 2**64) <= +2**128 & overflow is at ~+/-PRIME/2 (with PRIME ~= 2**192)	
        assert [range_check_ptr] = offset + \{show halfShift}		#Ensure: -HALF_SHIFT <= offset
        assert [range_check_ptr+1] = \{show halfShift} - offset	    #Ensure: offset <= HALF_SHIFT

        assert res = a * b - offset * \{show shift}

        # inlined int_check(res)
        assert [range_check_ptr+2] = res + \{show halfShift}		#Ensure: -HALF_SHIFT <= res
        assert [range_check_ptr+3] = \{show (halfShift - 1)} - res	#Ensure: res < HALF_SHIFT
        let range_check_ptr = range_check_ptr + 4
        
        return (res, range_check_ptr)
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

mul_intX : Nat -> (Name, Lazy CairoDef)
mul_intX nBits = (name, def)
  where name : Name
        name = mul_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (mul_intX_code name nBits)) 2 1


export
[mul_int] PrimFn where
    eval [_, ConstValue (I 1)] = Just $ ArgValue 0
    eval [ConstValue (I 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I 0)] = Just $ NewValue $ ConstValue $ I 0
    eval [ConstValue (I 0), _] = Just $ NewValue $ ConstValue $ I 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_intX_name 64) args]

export
[mul_int8] PrimFn where
    eval [_, ConstValue (I8 1)] = Just $ ArgValue 0
    eval [ConstValue (I8 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I8 0)] = Just $ NewValue $ ConstValue $ I8 0
    eval [ConstValue (I8 0), _] = Just $ NewValue $ ConstValue $ I8 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_intX_name 8) args]

export
[mul_int16] PrimFn where
    eval [_, ConstValue (I16 1)] = Just $ ArgValue 0
    eval [ConstValue (I16 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I16 0)] = Just $ NewValue $ ConstValue $ I16 0
    eval [ConstValue (I16 0), _] = Just $ NewValue $ ConstValue $ I16 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_intX_name 16) args]

export
[mul_int32] PrimFn where
    eval [_, ConstValue (I32 1)] = Just $ ArgValue 0
    eval [ConstValue (I32 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I32 0)] = Just $ NewValue $ ConstValue $ I32 0
    eval [ConstValue (I32 0), _] = Just $ NewValue $ ConstValue $ I32 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_intX_name 32) args]

export
[mul_int64] PrimFn where
    eval [_, ConstValue (I64 1)] = Just $ ArgValue 0
    eval [ConstValue (I64 1), _] = Just $ ArgValue 1
    eval [_, ConstValue (I64 0)] = Just $ NewValue $ ConstValue $ I64 0
    eval [ConstValue (I64 0), _] = Just $ NewValue $ ConstValue $ I64 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a*b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mul_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (mul_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- UINT DIV
---------------------------------------------------------------------------------------------------
div_intX_name : Nat -> Name
div_intX_name nBits = makeBuiltinName "div_int\{show nBits}"

div_intX_code : Name -> Nat -> String
div_intX_code name nBits = """
    # Division between int.
    # Returns the quotient.
    # Conforms to Idris specifications: division by 0 yields error.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (quotient : felt, range_check_ptr):
        alloc_locals
        local res
        local rem
        local sign
        local signB
        %{  
            from starkware.cairo.common.math_utils import as_int
            signB = 1 if as_int(ids.b, PRIME) >= 0 else -1 
            sign = signB if as_int(ids.a, PRIME) >= 0 else -signB
            ids.signB = signB % PRIME
            ids.sign = sign % PRIME
            #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
            # Question: is it ok to fail in hint or is a check with assert 0 =  1 needed
            (res, rem) = divmod(abs(as_int(ids.a,PRIME)), abs(as_int(ids.b,PRIME)))
            ids.res = res*sign % PRIME
            ids.rem = rem*sign % PRIME
        %}

        #check that the reverse is correct (this proofs correctnes if rem is valid)
        assert res * b + signB*rem = a

        #check the sign helpers are -1 or 1
        assert sign*sign = 1
        assert signB*signB = 1

        # check that rem & res have same sign & that the sign is correct
        assert [range_check_ptr] = sign*rem 				#rem is zero or has same sign as sign
        assert [range_check_ptr+1] = sign*res 				#res is zero or has same sign as sign
        
        #check that rem is between b and 0 (exclusive b, inclusive 0)
        # Note: if hint lies about signB then signB*b is negative and because sign*rem is proofen to be positive the rangecheck fails
        # Note: will fail if b = 0 which is the expected behaviour
        assert [range_check_ptr+2] = signB*b - sign*rem -1	# abs(rem) < abs(b)
        let range_check_ptr = range_check_ptr + 3

        # inlined int_check(res) -- implied as res must be between a and 0 to pass the checks & a is valid (input)
        # assert [range_check_ptr+3] = res + \{show halfShift}		#Ensure: -HALF_SHIFT <= res
        # assert [range_check_ptr+4] = \{show (halfShift - 1)} - res	#Ensure: res < HALF_SHIFT
        
        return (res, range_check_ptr)
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

div_intX : Nat -> (Name, Lazy CairoDef)
div_intX nBits = (name, def)
  where name : Name
        name = div_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (div_intX_code name nBits)) 2 1


export
[div_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I 1)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_intX_name 64) args]

export
[div_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I8 1)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_intX_name 8) args]

export
[div_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I16 1)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_intX_name 16) args]

export
[div_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I32 1)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_intX_name 32) args]

export
[div_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ Failure "Division by zero is not defined"
    eval [_, ConstValue (I64 1)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a `div` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [div_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (div_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- UINT MOD
---------------------------------------------------------------------------------------------------
mod_intX_name : Nat -> Name
mod_intX_name nBits = makeBuiltinName "mod_int\{show nBits}"

mod_intX_code : Name -> Nat -> String
mod_intX_code name nBits = """
    # Division between int.
    # Returns the remainder.
    # Conforms to Idris specifications: division by 0 yields error.
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (remainder : felt, range_check_ptr):
        alloc_locals
        local res
        local rem
        local sign
        local signB
        %{  
            from starkware.cairo.common.math_utils import as_int
            signB = 1 if as_int(ids.b, PRIME) >= 0 else -1 
            sign = signB if as_int(ids.a, PRIME) >= 0 else -signB
            ids.signB = signB % PRIME
            ids.sign = sign % PRIME
            #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
            # Question: is it ok to fail in hint or is a check with assert 0 =  1 needed
            (res, rem) = divmod(abs(as_int(ids.a,PRIME)), abs(as_int(ids.b,PRIME)))
            ids.res = res*sign % PRIME
            ids.rem = rem*sign % PRIME
        %}

        #check that the reverse is correct (this proofs correctnes if rem is valid)
        assert res * b + signB*rem = a

        #check the sign helpers are -1 or 1
        assert sign*sign = 1
        assert signB*signB = 1

        # check that rem & res have same sign & that the sign is correct
        assert [range_check_ptr] = sign*rem 				#rem is zero or has same sign as sign
        assert [range_check_ptr+1] = sign*res 				#res is zero or has same sign as sign
        
        #check that rem is between b and 0 (exclusive b, inclusive 0)
        # Note: if hint lies about signB then signB*b is negative and because sign*rem is proofen to be positive the rangecheck fails
        # Note: will fail if b = 0 which is the expected behaviour
        assert [range_check_ptr+2] = signB*b - sign*rem -1	# abs(rem) < abs(b)
        let range_check_ptr = range_check_ptr + 3

        # inlined int_check(res) -- implied as res must be between a and 0 to pass the checks & a is valid (input)
        # assert [range_check_ptr+3] = res + \{show halfShift}		#Ensure: -HALF_SHIFT <= res
        # assert [range_check_ptr+4] = \{show (halfShift - 1)} - res	#Ensure: res < HALF_SHIFT
        
        return (rem, range_check_ptr)
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

mod_intX : Nat -> (Name, Lazy CairoDef)
mod_intX nBits = (name, def)
  where name : Name
        name = mod_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (mod_intX_code name nBits)) 2 1

export
[mod_int] PrimFn where
    eval [_, ConstValue (I 1)] = Just $ NewValue $ ConstValue $ I 0
    eval [_, ConstValue (I 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_intX_name 64) args]

export
[mod_int8] PrimFn where
    eval [_, ConstValue (I8 1)] = Just $ NewValue $ ConstValue $ I8 0
    eval [_, ConstValue (I8 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_intX_name 8) args]

export
[mod_int16] PrimFn where
    eval [_, ConstValue (I16 1)] = Just $ NewValue $ ConstValue $ I16 0
    eval [_, ConstValue (I16 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_intX_name 16) args]

export
[mod_int32] PrimFn where
    eval [_, ConstValue (I32 1)] = Just $ NewValue $ ConstValue $ I32 0
    eval [_, ConstValue (I32 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_intX_name 32) args]

export
[mod_int64] PrimFn where
    eval [_, ConstValue (I64 1)] = Just $ NewValue $ ConstValue $ I64 0
    eval [_, ConstValue (I64 0)] = Just $ Failure "Division by zero is not defined"
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (a `mod` b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [mod_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (mod_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT NEG:
---------------------------------------------------------------------------------------------------
neg_intX_name : Nat -> Name
neg_intX_name nBits = makeBuiltinName "neg_int\{show nBits}"

neg_intX_code : Name -> Nat -> String
neg_intX_code name nBits = """
    # Note that int_neg(-HALF_SHIFT) = -HALF_SHIFT
    func \{cairoName name}(a : felt) -> (res):
        if a == -\{show halfShift}:
            return (a)
        else:
            return (-a)
        end
    end
"""
  where halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

neg_intX : Nat -> (Name, Lazy CairoDef)
neg_intX nBits = (name, def)
  where name : Name
        name = neg_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [] empty (neg_intX_code name nBits)) 1 1


export
[neg_int] PrimFn where
    eval [ConstValue (I a)] = Just $ NewValue $ ConstValue $ I (-a)
    eval _ = Nothing

    dependencies = fromList [neg_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_intX_name 64) args]

export
[neg_int8] PrimFn where
    eval [ConstValue (I8 a)] = Just $ NewValue $ ConstValue $ I8 (-a)
    eval _ = Nothing

    dependencies = fromList [neg_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_intX_name 8) args]

export
[neg_int16] PrimFn where
    eval [ConstValue (I16 a)] = Just $ NewValue $ ConstValue $ I16 (-a)
    eval _ = Nothing

    dependencies = fromList [neg_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_intX_name 16) args]

export
[neg_int32] PrimFn where
    eval [ConstValue (I32 a)] = Just $ NewValue $ ConstValue $ I32 (-a)
    eval _ = Nothing

    dependencies = fromList [neg_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_intX_name 16) args]

export
[neg_int64] PrimFn where
    eval [ConstValue (I64 a)] = Just $ NewValue $ ConstValue $ I64 (-a)
    eval _ = Nothing

    dependencies = fromList [neg_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (neg_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT SHL:
---------------------------------------------------------------------------------------------------
shl_intX_name : Nat -> Name
shl_intX_name nBits = makeBuiltinName "shl_int\{show nBits}"

shl_intX_code : Name -> Nat -> String
shl_intX_code name nBits = """
    ## Computes the logical left shift of an int.
    func \{cairoName name}(range_check_ptr, a, b) -> (res, range_check_ptr):
        # If b >= BIT_LENGTH - 1 , the result will be zero modulo 2**(BIT_LENGTH - 1).
        tempvar res
        %{ids.res = 1 if ids.b < \{show (nBits `minus` 1)} else 0 %}
        # b < 2**128 & a < 2**128 is given by semantics
        # b >= BIT_LENGTH - 1
        if res == 0: 
            assert [range_check_ptr] = b - \{show (nBits `minus` 1)}
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        # b < BIT_LENGTH - 1 
        else:
            assert [range_check_ptr] = \{show ((nBits `minus` 1) `minus` 1)} - b
            let range_check_ptr = range_check_ptr + 1
            let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
            \{cairoName (mul_intX_name nBits)}(range_check_ptr, a, c)
            ret
        end
    end
"""

shl_intX : Nat -> (Name, Lazy CairoDef)
shl_intX nBits = (name, def)
  where name : Name
        name = shl_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (shl_intX_code name nBits)) 2 1

shl_intX_imports : SortedSet Import
shl_intX_imports = singleton (MkImport "starkware.cairo.common.pow" "pow")

export
[shl_int] PrimFn where
    apStable = False

    eval [_, ConstValue(I 0)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__shl_Int a b)
    eval _ = Nothing

    imports = shl_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shl_intX 64, mul_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (shl_intX_name 64) args]


export
[shl_int8] PrimFn where
    apStable = False

    eval [_, ConstValue(I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__shl_Int8 (cast a) (cast b))
    eval _ = Nothing

    imports = shl_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shl_intX 8, mul_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (shl_intX_name 8) args]

export
[shl_int16] PrimFn where
    apStable = False

    eval [_, ConstValue(I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__shl_Int16 (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shl_int16"

export
[shl_int32] PrimFn where
    apStable = False

    eval [_, ConstValue(I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__shl_Int32 (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shl_int32"

export
[shl_int64] PrimFn where
    apStable = False

    eval [_, ConstValue(I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__shl_Int64 (cast a) (cast b))
    eval _ = Nothing

    generateCode = generateMissingCodeError "shl_int64"

---------------------------------------------------------------------------------------------------
-- INT SHR:
---------------------------------------------------------------------------------------------------
shr_intX_name : Nat -> Name
shr_intX_name nBits = makeBuiltinName "shr_int\{show nBits}"

shr_intX_code : Name -> Nat -> String
shr_intX_code name nBits = """
    # Computes the logical right shift of an int.
    func \{cairoName name}(range_check_ptr, a : felt,  b : felt) -> (res : felt, range_check_ptr):
        #inlined int_pow2
        # If a >= BIT_LENGTH - 1, the result will be zero modulo 2**(BIT_LENGTH-1).
        tempvar res
        %{ids.res = 1 if ids.b < \{show (nBits `minus` 1)} else 0 %}
        # b < 2**128 & a < 2**128 is given by semantics
        # BIT_LENGTH <= b
        if res == 0: 
            assert [range_check_ptr] = b - \{show (nBits `minus` 1)}
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        #b < BIT_LENGTH
        else:
            assert [range_check_ptr] = \{show ((nBits `minus` 1) `minus` 1)} - b
            let range_check_ptr = range_check_ptr + 1
            let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
            \{cairoName (div_intX_name nBits)}(range_check_ptr, a, c)
            ret
        end
    end
"""

shr_intX : Nat -> (Name, Lazy CairoDef)
shr_intX nBits = (name, def)
  where name : Name
        name = shr_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (shr_intX_code name nBits)) 2 1

shr_intX_imports : SortedSet Import
shr_intX_imports = singleton (MkImport "starkware.cairo.common.pow" "pow")

export
[shr_int] PrimFn where
    apStable = False

    eval [_, ConstValue(I 0)] = Just $ ArgValue 0
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__shr_Int a b)
    eval _ = Nothing

    imports = shr_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_intX 64, div_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_intX_name 64) args]

export
[shr_int8] PrimFn where
    apStable = False

    eval [_, ConstValue(I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__shr_Int8 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_intX 8, div_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_intX_name 8) args]

export
[shr_int16] PrimFn where
    apStable = False

    eval [_, ConstValue(I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__shr_Int16 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_intX 16, div_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_intX_name 16) args]

export
[shr_int32] PrimFn where
    apStable = False

    eval [_, ConstValue(I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__shr_Int32 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_intX 32, div_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_intX_name 32) args]

export
[shr_int64] PrimFn where
    apStable = False

    eval [_, ConstValue(I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__shr_Int64 (cast a) (cast b))
    eval _ = Nothing

    imports = shr_intX_imports
    implicits = singleton range_check_builtin
    dependencies = fromList [shr_intX 64, div_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (shr_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT AND:
---------------------------------------------------------------------------------------------------
and_intX_name : Nat -> Name
and_intX_name nBits = makeBuiltinName "and_int\{show nBits}"

and_intX_code : Name -> Nat -> String
and_intX_code name nBits = """
    func \{cairoName name}(range_check_ptr, bitwise_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr, bitwise_ptr):
        alloc_locals
        local signA
        local signB
        %{
            from starkware.cairo.common.math_utils import as_int
            ids.signA = 1 if as_int(ids.a, PRIME) >= 0 else (-1 % PRIME)
            ids.signB = 1 if as_int(ids.b, PRIME) >= 0 else (-1 % PRIME)	
        %}
        
        assert signA*signA = 1
        assert signB*signB = 1
        
        assert [range_check_ptr] = signA*a
        assert [range_check_ptr+1] = signB*b
        
        let a_offset = a - (signA - 1)*\{show halfShift} 	#from: ((signA - 1)/2)*SHIFT | ((signA - 1)/2) = -(signA == -1)
        let b_offset = b - (signB - 1)*\{show halfShift} 	#from: ((signB - 1)/2)*SHIFT | ((signB - 1)/2) = -(signB == -1)
        
        # inlined bitwise_and
        assert [bitwise_ptr] = a_offset 
        assert [bitwise_ptr+1] = b_offset        
        local res_value = [bitwise_ptr+2]
        let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE

        # If the result is HALF_SHIFT or greater, this indicates a twos complement negative value
        # See int_le for explanation: note res_value < 2**127 (because max 64bits)
        local must_shift
        %{ids.must_shift = 1 if \{show halfShift} <= ids.res_value else 0 %}
        if must_shift == 0: 
            assert [range_check_ptr+2] = \{show (halfShift - 1)} - res_value 
            let range_check_ptr = range_check_ptr + 3
            return (res_value, range_check_ptr, bitwise_ptr )
        else:
            assert [range_check_ptr+2] = res_value - \{show halfShift}
            let range_check_ptr = range_check_ptr + 3
            return (res_value - \{show shift}, range_check_ptr, bitwise_ptr)
        end
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

and_intX : Nat -> (Name, Lazy CairoDef)
and_intX nBits = (name, def)
  where name : Name
        name = and_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin, bitwise_builtin] empty (and_intX_code name nBits)) 2 1

export
[and_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ NewValue $ ConstValue $ I 0
    eval [ConstValue (I 0), _] = Just $ NewValue $ ConstValue $ I 0
    eval [_, ConstValue (I (-1))] = Just $ ArgValue 0
    eval [ConstValue (I (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__and_Int a b)
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [and_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (and_intX_name 64) args]

export
[and_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ NewValue $ ConstValue $ I8 0
    eval [ConstValue (I8 0), _] = Just $ NewValue $ ConstValue $ I8 0
    eval [_, ConstValue (I8 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I8 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__and_Int8 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [and_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (and_intX_name 8) args]

export
[and_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ NewValue $ ConstValue $ I16 0
    eval [ConstValue (I16 0), _] = Just $ NewValue $ ConstValue $ I16 0
    eval [_, ConstValue (I16 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I16 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__and_Int16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [and_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (and_intX_name 16) args]

export
[and_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ NewValue $ ConstValue $ I32 0
    eval [ConstValue (I32 0), _] = Just $ NewValue $ ConstValue $ I32 0
    eval [_, ConstValue (I32 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I32 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__and_Int32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [and_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (and_intX_name 32) args]

export
[and_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ NewValue $ ConstValue $ I64 0
    eval [ConstValue (I64 0), _] = Just $ NewValue $ ConstValue $ I64 0
    eval [_, ConstValue (I64 (-1))] = Just $ ArgValue 0
    eval [ConstValue (I64 (-1)), _] = Just $ ArgValue 1
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__and_Int64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [and_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (and_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT OR:
---------------------------------------------------------------------------------------------------
or_intX_name : Nat -> Name
or_intX_name nBits = makeBuiltinName "or_int\{show nBits}"

or_intX_code : Name -> Nat -> String
or_intX_code name nBits = """
    func \{cairoName name}(range_check_ptr, bitwise_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr, bitwise_ptr):
        alloc_locals
        local signA
        local signB
        %{
            from starkware.cairo.common.math_utils import as_int
            ids.signA = 1 if as_int(ids.a, PRIME) >= 0 else (-1 % PRIME)
            ids.signB = 1 if as_int(ids.b, PRIME) >= 0 else (-1 % PRIME)	
        %}
        
        assert signA*signA = 1
        assert signB*signB = 1
        
        assert [range_check_ptr] = signA*a
        assert [range_check_ptr+1] = signB*b
        
        let a_offset = a - (signA - 1)*\{show halfShift} 	#from: ((signA - 1)/2)*SHIFT | ((signA - 1)/2) = -(signA == -1)
        let b_offset = b - (signB - 1)*\{show halfShift} 	#from: ((signB - 1)/2)*SHIFT | ((signB - 1)/2) = -(signB == -1)
        
        # inlined bitwise_or
        assert [bitwise_ptr] = a_offset 
        assert [bitwise_ptr+1] = b_offset        
        local res_value = [bitwise_ptr+4]
        let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE

        # If the result is HALF_SHIFT or greater, this indicates a twos complement negative value
        # See int_le for explanation: note res_value < 2**127 (because max 64bits)
        local must_shift
        %{ids.must_shift = 1 if \{show halfShift} <= ids.res_value else 0 %}
        if must_shift == 0: 
            assert [range_check_ptr+2] = \{show (halfShift - 1)} - res_value # DK: check - is left associative
            let range_check_ptr = range_check_ptr + 3
            return (res_value, range_check_ptr, bitwise_ptr )
        else:
            assert [range_check_ptr+2] = res_value - \{show halfShift}		#-0 is for ap stability improves worse case in code gen
            let range_check_ptr = range_check_ptr + 3
            return (res_value - \{show shift}, range_check_ptr, bitwise_ptr)
        end
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

or_intX : Nat -> (Name, Lazy CairoDef)
or_intX nBits = (name, def)
  where name : Name
        name = or_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin, bitwise_builtin] empty (or_intX_code name nBits)) 2 1


export
[or_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I  (-1))] = Just $ NewValue $ ConstValue $ I (-1)
    eval [ConstValue (I  (-1)), _] = Just $ NewValue $ ConstValue $ I (-1)
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__or_Int a b)
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [or_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (or_intX_name 64) args]

export
[or_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I8 (-1))] = Just $ NewValue $ ConstValue $ I8 (-1)
    eval [ConstValue (I8 (-1)), _] = Just $ NewValue $ ConstValue $ I8 (-1)
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__or_Int8 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [or_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (or_intX_name 8) args]

export
[or_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I16 (-1))] = Just $ NewValue $ ConstValue $ I16 (-1)
    eval [ConstValue (I16 (-1)), _] = Just $ NewValue $ ConstValue $ I16 (-1)
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__or_Int16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [or_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (or_intX_name 16) args]

export
[or_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I32 (-1))] = Just $ NewValue $ ConstValue $ I32 (-1)
    eval [ConstValue (I32 (-1)), _] = Just $ NewValue $ ConstValue $ I32 (-1)
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__or_Int32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [or_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (or_intX_name 32) args]

export
[or_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 0), _] = Just $ ArgValue 1
    eval [_, ConstValue (I64 (-1))] = Just $ NewValue $ ConstValue $ I64 (-1)
    eval [ConstValue (I64 (-1)), _] = Just $ NewValue $ ConstValue $ I64 (-1)
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__or_Int64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [or_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (or_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT XOR:
---------------------------------------------------------------------------------------------------
xor_intX_name : Nat -> Name
xor_intX_name nBits = makeBuiltinName "xor_int\{show nBits}"

xor_intX_code : Name -> Nat -> String
xor_intX_code name nBits = """
    func \{cairoName name}(range_check_ptr, bitwise_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr, bitwise_ptr):
        alloc_locals
        let a_offset = a + \{show halfShift}  # guarantee positive number, since minimum input value is DEFAULT_PRIME - SHIFT.  e.g. 0 maps to 128, 127 maps to 255, and -1 maps to 127.  This gets applied to _both_ inputs, so intuitively, XOR doesn't notice or care. 
        let b_offset = b + \{show halfShift}

        # inlined bitwise_xor
        assert [bitwise_ptr] = a_offset 
        assert [bitwise_ptr+1] = b_offset        
        local res_value = [bitwise_ptr+3]
        let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE
        
        # If the result is HALF_SHIFT of greater, this indicates a twos complement negative value
        # See int_le for explanation: note res_value < 2**127 (because max 64bits)
        local must_shift
        %{ids.must_shift = 1 if \{show halfShift} <= ids.res_value else 0 %}
        if must_shift == 0: 
            assert [range_check_ptr] = \{show (halfShift-1)} - res_value
            let range_check_ptr = range_check_ptr + 1
            return (res_value, range_check_ptr, bitwise_ptr)
        else:
            assert [range_check_ptr] = res_value - \{show halfShift}
            let range_check_ptr = range_check_ptr + 1
            return (res_value - \{show shift}, range_check_ptr, bitwise_ptr)
        end
    end


"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

xor_intX : Nat -> (Name, Lazy CairoDef)
xor_intX nBits = (name, def)
  where name : Name
        name = xor_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin, bitwise_builtin] empty (xor_intX_code name nBits)) 2 1


export
[xor_int] PrimFn where
    eval [_, ConstValue (I 0)] = Just $ ArgValue 0
    eval [ConstValue (I 0), _] = Just $ ArgValue 1
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ I (prim__xor_Int a b)
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [xor_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (xor_intX_name 64) args]

export
[xor_int8] PrimFn where
    eval [_, ConstValue (I8 0)] = Just $ ArgValue 0
    eval [ConstValue (I8 0), _] = Just $ ArgValue 1
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ I8 (prim__xor_Int8 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [xor_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (xor_intX_name 8) args]

export
[xor_int16] PrimFn where
    eval [_, ConstValue (I16 0)] = Just $ ArgValue 0
    eval [ConstValue (I16 0), _] = Just $ ArgValue 1
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ I16 (prim__xor_Int16 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [xor_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (xor_intX_name 16) args]

export
[xor_int32] PrimFn where
    eval [_, ConstValue (I32 0)] = Just $ ArgValue 0
    eval [ConstValue (I32 0), _] = Just $ ArgValue 1
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ I32 (prim__xor_Int32 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [xor_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (xor_intX_name 32) args]

export
[xor_int64] PrimFn where
    eval [_, ConstValue (I64 0)] = Just $ ArgValue 0
    eval [ConstValue (I64 0), _] = Just $ ArgValue 1
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ I64 (prim__xor_Int64 (cast a) (cast b))
    eval _ = Nothing

    imports = singleton $ bitwiseBuiltinImport
    implicits = fromList [range_check_builtin, bitwise_builtin]
    dependencies = fromList [xor_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (xor_intX_name 64) args]

---------------------------------------------------------------------------------------------------
-- INT LT
---------------------------------------------------------------------------------------------------
lt_intX_name : Name
lt_intX_name = makeBuiltinName "lt_int"

lt_intX_code : Name -> String
lt_intX_code name = """
    # Returns 1 if the first integer is less than the second, otherwise returns 0.  
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
        tempvar res
        %{
            from starkware.cairo.common.math_utils import as_int
            ids.res = 1 if as_int(ids.a,PRIME) < as_int(ids.b,PRIME) else 0 
        %}
        # -2**127 <= b < 2**127 & -2**127 <= a < 2**127 is given by semantics (actuall even tighter as max 64bits)
        # implies: a - b < 2**128 & b - a < 2**128 (meaning in range check upper bound)
        # b <= a
        if res == 0: 
            assert [range_check_ptr] = a - b - 0 #+0 is for ap stability improves worse case in code gen
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        # a < b
        else:
            assert [range_check_ptr] = b - a - 1
            let range_check_ptr = range_check_ptr + 1
            return (1, range_check_ptr)
        end
    end
"""

lt_intX : (Name, Lazy CairoDef)
lt_intX = (lt_intX_name, def)
  where def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (lt_intX_code lt_intX_name)) 2 1

generateLtCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateLtCallCode res args implicits = Instructions [CALL [res] implicits lt_intX_name args] 

export
[lt_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateLtCallCode

export
[lt_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateLtCallCode

export
[lt_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateLtCallCode

export
[lt_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateLtCallCode

export
[lt_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a<b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateLtCallCode


---------------------------------------------------------------------------------------------------
-- INT LTE
---------------------------------------------------------------------------------------------------
lte_intX_name : Name
lte_intX_name = makeBuiltinName "lte_int"

lte_intX_code : Name -> String
lte_intX_code name = """
    # Returns 1 if the first integer is less than the second, otherwise returns 0.  
    func \{cairoName name}(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
        tempvar res
        %{
            from starkware.cairo.common.math_utils import as_int
            ids.res = 1 if as_int(ids.a,PRIME) < as_int(ids.b,PRIME) else 0 
        %}
        # -2**127 <= b < 2**127 & -2**127 <= a < 2**127 is given by semantics (actuall even tighter as max 64bits)
        # implies: a - b < 2**128 & b - a < 2**128 (meaning in range check upper bound)
        # b <= a
        if res == 0: 
            assert [range_check_ptr] = a - b - 0 #+0 is for ap stability improves worse case in code gen
            let range_check_ptr = range_check_ptr + 1
            return (0, range_check_ptr)
        # a < b
        else:
            assert [range_check_ptr] = b - a - 1
            let range_check_ptr = range_check_ptr + 1
            return (1, range_check_ptr)
        end
    end
"""

lte_intX : (Name, Lazy CairoDef)
lte_intX = (lte_intX_name, def)
  where def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (lte_intX_code lte_intX_name)) 2 1

generateLteCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateLteCallCode res args implicits = Instructions [CALL [res] implicits lte_intX_name args] 

export
[lte_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateLtCallCode

export
[lte_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateLtCallCode

export
[lte_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateLtCallCode

export
[lte_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateLtCallCode

export
[lte_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a<=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateLtCallCode

---------------------------------------------------------------------------------------------------
-- INT EQ
---------------------------------------------------------------------------------------------------
export
[eq_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_int" r a i

export
[eq_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_int8" r a i

export
[eq_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_int16" r a i

export
[eq_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_int32" r a i

export
[eq_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a==b)
    eval _ = Nothing

    generateCode r a i = Raw $ compileEqOp "eq_int64" r a i

---------------------------------------------------------------------------------------------------
-- INT GTE
-- Implementation uses flipped arguments to lte
---------------------------------------------------------------------------------------------------

generateGteCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateGteCallCode res [a,b] implicits = Instructions [CALL [res] implicits lte_intX_name [b,a]] -- Flipped arguments
generateGteCallCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode gte_intX"

export
[gte_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateGteCallCode

export
[gte_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateGteCallCode

export
[gte_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateGteCallCode

export
[gte_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateGteCallCode

export
[gte_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a>=b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lte_intX]
    generateCode = generateGteCallCode

---------------------------------------------------------------------------------------------------
-- INT GT
-- Implementation uses flipped arguments to lte
---------------------------------------------------------------------------------------------------

generateGtCallCode : CairoReg -> List CairoReg -> LinearImplicitArgs -> PrimFnCode
generateGtCallCode res [a,b] implicits = Instructions [CALL [res] implicits lt_intX_name [b,a]] -- Flipped arguments
generateGtCallCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode gt_intX"

export
[gt_int] PrimFn where
    eval [ConstValue (I a), ConstValue (I b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateGtCallCode

export
[gt_int8] PrimFn where
    eval [ConstValue (I8 a), ConstValue (I8 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateGtCallCode

export
[gt_int16] PrimFn where
    eval [ConstValue (I16 a), ConstValue (I16 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateGtCallCode

export
[gt_int32] PrimFn where
    eval [ConstValue (I32 a), ConstValue (I32 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateGtCallCode

export
[gt_int64] PrimFn where
    eval [ConstValue (I64 a), ConstValue (I64 b)] = Just $ NewValue $ ConstValue $ toInt (a>b)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [lt_intX]
    generateCode = generateGtCallCode

---------------------------------------------------------------------------------------------------
-- INT CASTS
---------------------------------------------------------------------------------------------------
cast_intX_name : Nat -> Name
cast_intX_name nBits = makeBuiltinName "cast_int\{show nBits}"

cast_intX_code : Name -> Nat -> String
cast_intX_code name nBits = """
    # Casts to int\{show nBits}
    # Returns the result as int\{show nBits}.
    func \{cairoName name}(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
        alloc_locals
        local res
        local offset	
        %{
            from starkware.cairo.common.math_utils import as_int
            rawRes = (as_int(ids.a, PRIME) + \{show halfShift})
            (rawOffset, resRaw) = divmod(rawRes, \{show shift}) 
            ids.offset = rawOffset % PRIME
            ids.res = (rawRes - \{show halfShift}) % PRIME
        %}

        # Check offset can not trigger overflow / underflow
        #  Note: Max valid offset absolute = HALF_SHIFT*HALF_SHIFT/SHIFT = (SHIFT*SHIFT)/4*SHIFT = SHIFT/4
        #  For simplicity we weaken to -HALF_SHIFT <= offset <= HALF_SHIFT then no overflow (for 64bit): -2**128 <= +/-(2**63 * 2**63) +/- (2**63 * 2**64) <= +2**128 & overflow is at ~+/-PRIME/2 (with PRIME ~= 2**192)	
        assert [range_check_ptr] = offset + \{show halfShift}		#Ensure: -HALF_SHIFT <= offset
        assert [range_check_ptr+1] = \{show halfShift} - offset	    #Ensure: offset <= HALF_SHIFT

        assert res = a - offset * \{show shift}

        # inlined int_check(res)
        assert [range_check_ptr+2] = res + \{show halfShift}		#Ensure: -HALF_SHIFT <= res
        assert [range_check_ptr+3] = \{show (halfShift - 1)} - res	#Ensure: res < HALF_SHIFT
        let range_check_ptr = range_check_ptr + 4
        
        return (res, range_check_ptr)
    end

"""
  where shift : Integer
        shift = pow2 nBits
        halfShift : Integer
        halfShift = pow2 (nBits `minus` 1)

cast_intX : Nat -> (Name, Lazy CairoDef)
cast_intX nBits = (name, def)
  where name : Name
        name = cast_intX_name nBits
        def : CairoDef
        def = ForeignDef (MkForeignInfo True Nothing [range_check_builtin] empty (cast_intX_code name nBits)) 1 1

export
[cast_to_int] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_intX_name 64) args]

export
[cast_to_int8] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I8 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_intX 8]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_intX_name 8) args]

export
[cast_to_int16] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I16 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_intX 16]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_intX_name 16) args]

export
[cast_to_int32] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I32 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_intX 32]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_intX_name 32) args]

export
[cast_to_int64] PrimFn where
    eval [ConstValue c] = map (\i => NewValue $ ConstValue $ I64 $ cast i) (constToInteger c)
    eval _ = Nothing

    implicits = singleton range_check_builtin
    dependencies = fromList [cast_intX 64]
    generateCode res args implicits = Instructions [CALL [res] implicits (cast_intX_name 64) args]
