from starkware.cairo.common.cairo_builtins import BitwiseBuiltin
from starkware.cairo.common.bitwise import bitwise_and, bitwise_or, bitwise_xor
from starkware.cairo.common.pow import pow

# Some constants
const BIT_LENGTH = 8  # I'm aiming for the rest of the file to be parametric over values for BIT_LENGTH up to 64, if possible
const SHIFT = 2 ** 8
const HALF_SHIFT = 2 ** 7

# Represents a signed integer in the range [-HALF_SHIFT, HALF_SHIFT)
# In other words, this is a numerical type with values in -HALF_SHIFT to HALF_SHIFT-1 inclusive.

# Arithmetic.
# Adds two int.
func int_add(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res
    local overflow
    %{ 
        raw_res = (ids.a + ids.b) % PRIME
        if (raw_res >= ids.HALF_SHIFT) & (raw_res < ids.SHIFT):
          (ids.overflow, ids.res) = (1, (raw_res - ids.SHIFT) % PRIME)
        elif (raw_res < PRIME - ids.HALF_SHIFT) & (PRIME - ids.SHIFT <= raw_res): 
          (ids.overflow, ids.res) = (-1 % PRIME, (raw_res + ids.SHIFT) % PRIME)
        else:
          (ids.overflow, ids.res) = (0, raw_res)
    %}

    assert overflow * overflow * overflow = overflow  # overflow is -1, 0 or 1
    assert res = a + b - overflow * SHIFT
    
    #inlined int_check
    assert [range_check_ptr] = res + HALF_SHIFT			#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+1] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr + 2

    return (res, range_check_ptr)
end

# Subtraction.
func int_sub(range_check_ptr, a : felt, b : felt) -> (res : felt,range_check_ptr):
    alloc_locals
    local res : felt
    local overflow : felt
    %{
        a_sub_b = (ids.a - ids.b) % PRIME 
        if (a_sub_b >= ids.HALF_SHIFT) & (a_sub_b < ids.SHIFT):
          (ids.overflow, ids.res) = (1, (a_sub_b - ids.SHIFT) % PRIME)
        elif (a_sub_b < PRIME - ids.HALF_SHIFT) & (PRIME - ids.SHIFT <= a_sub_b): 
          (ids.overflow, ids.res) = (-1 % PRIME, (a_sub_b + ids.SHIFT) % PRIME)
        else:
          (ids.overflow, ids.res) = (0, a_sub_b)
    %}

    assert overflow * overflow * overflow = overflow  # overflow is -1, 0 or 1
    assert res = a - b - overflow * SHIFT
    
    #inlined int_check
    assert [range_check_ptr] = res + HALF_SHIFT			#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+1] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr + 2
    
    return (res, range_check_ptr)
end

# Note that int_neg(-HALF_SHIFT) = -HALF_SHIFT
func int_neg(a : felt) -> (res : felt):
    if a == -HALF_SHIFT:
        return (a)
    else:
        return (-a)
    end
end

# Multiplies two int.
# Returns the result as int.
func int_mul(range_check_ptr, a : felt, b:felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res
    local offset	
    %{
        from starkware.cairo.common.math_utils import as_int
        rawMult = ((as_int(ids.a, PRIME) * as_int(ids.b, PRIME)) + ids.HALF_SHIFT)
        (rawOffset, resRaw) = divmod(rawMult, ids.SHIFT) 
        ids.offset = rawOffset % PRIME
        ids.res = (resRaw - ids.HALF_SHIFT) % PRIME
    %}

    # Check offset can not trigger overflow / underflow
    #  Note: Max valid offset absolute = HALF_SHIFT*HALF_SHIFT/SHIFT = (SHIFT*SHIFT)/4*SHIFT = SHIFT/4
    #  For simplicity we weaken to -HALF_SHIFT <= offset <= HALF_SHIFT then no overflow (for 64bit): -2**128 <= +/-(2**63 * 2**63) +/- (2**63 * 2**64) <= +2**128 & overflow is at ~+/-PRIME/2 (with PRIME ~= 2**192)	
    assert [range_check_ptr] = offset + HALF_SHIFT		#Ensure: -HALF_SHIFT <= offset
    assert [range_check_ptr+1] = HALF_SHIFT - offset	#Ensure: offset <= HALF_SHIFT

    assert res = a * b - offset * SHIFT

    # inlined int_check(res)
    assert [range_check_ptr+2] = res + HALF_SHIFT		#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+3] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr + 4
    
    return (res, range_check_ptr)
end

# Division between int.
# Returns the quotient.
# Conforms to Idris specifications: division by 0 yields error.
func int_div(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res
    local rem
    local signB
    %{  
        from starkware.cairo.common.math_utils import as_int
        signB = 1 if as_int(ids.b, PRIME) >= 0 else -1 
        ids.signB = signB % PRIME
        #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
        # Question: is it ok to fail in hint or is a check with assert 0 =  1 needed
        # Quick fix from old to new idris behaviour
        b = as_int(ids.b,PRIME)
        (res, rem) = divmod(as_int(ids.a,PRIME), b)
        if rem < 0:
            ids.res = (res+1) % PRIME
            ids.rem = (rem-b) % PRIME
        else:
            ids.res = res % PRIME
            ids.rem = rem % PRIME
    %}

    #check that the reverse is correct (this proofs correcntes if rem is valid)
    #assert res * b + signB*rem = a # old idris behaviour
    assert res * b + rem = a        # new idris behaviour

    #check the sign helpers are -1 or 1
    # assert sign*sign = 1 # irrelevant for new behaviour
    assert signB*signB = 1

    # check that rem & res have same sign & that the sign is correct # irrelevant for new behaviour
    # assert [range_check_ptr] = sign*rem 				#rem is zero or has same sign as sign
    # assert [range_check_ptr+1] = sign*res 			#res is zero or has same sign as sign

    # check  that rem is positive #necessary for idris new behaviour
    assert [range_check_ptr] = rem

    # Old Idris behaviour
    #check that rem is between b and 0 (exclusive b, inclusive 0)
    # Note: if hint lies about signB then signB*b is negative and because sign*rem is proofen to be positive the rangecheck fails
    # Note: will fail if b = 0 which is the expected behaviour
    # assert [range_check_ptr+2] = signB*b - sign*rem -1	# abs(rem) < abs(b)

    # New idris behaviour
    # check that rem is between 0 and abs(b) (exclusive b, inclusive 0)
    # Note: if hint lies about signB then signB*b is negative and because rem is proofen to be positive the rangecheck fails
    # Note: will fail if b = 0 which is the expected behaviour
    assert [range_check_ptr+1] = signB*b - rem - 1	# rem < abs(b)

    let range_check_ptr = range_check_ptr + 2

    # inlined int_check(res) -- implied by assert res * b + rem = a if b != 0 & rem < abs(b) & a,b are valid ints
    # assert [range_check_ptr+3] = res + HALF_SHIFT		#Ensure: -HALF_SHIFT <= res
    # assert [range_check_ptr+4] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    
    return (res, range_check_ptr)
end

func int_mod(range_check_ptr, a : felt, b : felt) -> (remainder : felt, range_check_ptr):
    alloc_locals
    local res
    local rem
    local signB
    %{
        from starkware.cairo.common.math_utils import as_int
        signB = 1 if as_int(ids.b, PRIME) >= 0 else -1
        ids.signB = signB % PRIME
        #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
        # Question: is it ok to fail in hint or is a check with assert 0 =  1 needed
        # Quick fix from old to new idris behaviour
        b = as_int(ids.b,PRIME)
        (res, rem) = divmod(as_int(ids.a,PRIME), b)
        if rem < 0:
            ids.res = (res+1) % PRIME
            ids.rem = (rem-b) % PRIME
        else:
            ids.res = res % PRIME
            ids.rem = rem % PRIME
    %}

    #check that the reverse is correct (this proofs correcntes if rem is valid)
    #assert res * b + signB*rem = a # old idris behaviour
    assert res * b + rem = a        # new idris behaviour

    #check the sign helpers are -1 or 1
    # assert sign*sign = 1 # irrelevant for new behaviour
    assert signB*signB = 1

    # check that rem & res have same sign & that the sign is correct # irrelevant for new behaviour
    # assert [range_check_ptr] = sign*rem 				#rem is zero or has same sign as sign
    # assert [range_check_ptr+1] = sign*res 			#res is zero or has same sign as sign

    # check  that rem is positive #necessary for idris new behaviour
    assert [range_check_ptr] = rem

    # Old Idris behaviour
    #check that rem is between b and 0 (exclusive b, inclusive 0)
    # Note: if hint lies about signB then signB*b is negative and because sign*rem is proofen to be positive the rangecheck fails
    # Note: will fail if b = 0 which is the expected behaviour
    # assert [range_check_ptr+2] = signB*b - sign*rem -1	# abs(rem) < abs(b)

    # New idris behaviour
    # check that rem is between 0 and abs(b) (exclusive b, inclusive 0)
    # Note: if hint lies about signB then signB*b is negative and because rem is proofen to be positive the rangecheck fails
    # Note: will fail if b = 0 which is the expected behaviour
    assert [range_check_ptr+1] = signB*b - rem - 1	# rem < abs(b)

    let range_check_ptr = range_check_ptr + 2

    # inlined int_check(res) -- implied by assert rem < abs(b) & b are valid ints
    # assert [range_check_ptr+3] = rem + HALF_SHIFT		#Ensure: -HALF_SHIFT <= rem
    # assert [range_check_ptr+4] = HALF_SHIFT - 1 - rem	#Ensure: rem < HALF_SHIFT

    return (rem, range_check_ptr)
end


## Bitwise

# mjg
# bitwise builtin in current Cairo version (cairo-lang==0.6.1) doesn't like numbers greater than or equal to 2^251.  So we "adjust" negative inputs upwards by adding an offset of HALF_SHIFT. 

# bitwise XOR
func int_xor(range_check_ptr, bitwise_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr, bitwise_ptr):
    alloc_locals
    let a_offset = a + HALF_SHIFT  # guarantee positive number, since minimum input value is DEFAULT_PRIME - SHIFT.  e.g. 0 maps to 128, 127 maps to 255, and -1 maps to 127.  This gets applied to _both_ inputs, so intuitively, XOR doesn't notice or care.
    let b_offset = b + HALF_SHIFT

    # inlined bitwise_xor
    assert [bitwise_ptr] = a_offset
    assert [bitwise_ptr+1] = b_offset
    local res_value = [bitwise_ptr+3]
    let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE

    # If the result is HALF_SHIFT of greater, this indicates a twos complement negative value
    # See int_le for explanation: note res_value < 2**127 (because max 64bits)
    local must_shift
    %{ids.must_shift = 1 if (ids.HALF_SHIFT) <= ids.res_value else 0 %}
    if must_shift == 0:
        assert [range_check_ptr] = (HALF_SHIFT - 1) - res_value
        let range_check_ptr = range_check_ptr + 1
        return (res_value, range_check_ptr, bitwise_ptr)
    else:
        assert [range_check_ptr] = res_value - HALF_SHIFT
        let range_check_ptr = range_check_ptr + 1
        return (res_value - SHIFT, range_check_ptr, bitwise_ptr)
    end
end
# Worked examples: 
# int_xor(0,-1)  ->   bitwise_xor(128,127) = 255   ->   -1
# int_xor(0,-2)  ->   bitwise_xor(128,126) = 254   ->   -2 
# int_xor(127,-127)-> bitwise_xor(255,1) = 254     ->   -2

## bitwise OR
func int_or(range_check_ptr, bitwise_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr, bitwise_ptr):
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

    let a_offset = a - (signA - 1)*HALF_SHIFT	#from: ((signA - 1)/2)*SHIFT | ((signA - 1)/2) = -(signA == -1)
    let b_offset = b - (signB - 1)*HALF_SHIFT	#from: ((signB - 1)/2)*SHIFT | ((signB - 1)/2) = -(signB == -1)

    # inlined bitwise_or
    assert [bitwise_ptr] = a_offset
    assert [bitwise_ptr+1] = b_offset
    local res_value = [bitwise_ptr+4]
    let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE

    # If the result is HALF_SHIFT or greater, this indicates a twos complement negative value
    # See int_le for explanation: note res_value < 2**127 (because max 64bits)
    local must_shift
    %{ids.must_shift = 1 if ids.HALF_SHIFT <= ids.res_value else 0 %}
    if must_shift == 0:
        assert [range_check_ptr+2] = (HALF_SHIFT - 1) - res_value # DK: check - is left associative
        let range_check_ptr = range_check_ptr + 3
        return (res_value, range_check_ptr, bitwise_ptr )
    else:
        assert [range_check_ptr+2] = res_value - HALF_SHIFT		#-0 is for ap stability improves worse case in code gen
        let range_check_ptr = range_check_ptr + 3
        return (res_value - SHIFT, range_check_ptr, bitwise_ptr)
    end
end

## bitwise AND
func int_and(range_check_ptr, bitwise_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr, bitwise_ptr):
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

    let a_offset = a - (signA - 1)*HALF_SHIFT 	#from: ((signA - 1)/2)*SHIFT | ((signA - 1)/2) = -(signA == -1)
    let b_offset = b - (signB - 1)*HALF_SHIFT 	#from: ((signB - 1)/2)*SHIFT | ((signB - 1)/2) = -(signB == -1)

    # inlined bitwise_and
    assert [bitwise_ptr] = a_offset
    assert [bitwise_ptr+1] = b_offset
    local res_value = [bitwise_ptr+2]
    let bitwise_ptr = bitwise_ptr + BitwiseBuiltin.SIZE

    # If the result is HALF_SHIFT or greater, this indicates a twos complement negative value
    # See int_le for explanation: note res_value < 2**127 (because max 64bits)
    local must_shift
    %{ids.must_shift = 1 if ids.HALF_SHIFT <= ids.res_value else 0 %}
    if must_shift == 0:
        assert [range_check_ptr+2] = HALF_SHIFT - 1 - res_value
        let range_check_ptr = range_check_ptr + 3
        return (res_value, range_check_ptr, bitwise_ptr )
    else:
        assert [range_check_ptr+2] = res_value - HALF_SHIFT
        let range_check_ptr = range_check_ptr + 3
        return (res_value - SHIFT, range_check_ptr, bitwise_ptr)
    end
end

# Casts to int
func int_cast(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res
    local offset
    %{
        from starkware.cairo.common.math_utils import as_int
        rawRes = (as_int(ids.a, PRIME) + ids.HALF_SHIFT)
        (rawOffset, resRaw) = divmod(rawRes, ids.SHIFT)
        ids.offset = rawOffset % PRIME
        ids.res = (rawRes - ids.HALF_SHIFT) % PRIME
    %}

    # Check offset can not trigger overflow / underflow
    #  Note: Max valid offset absolute = HALF_SHIFT*HALF_SHIFT/SHIFT = (SHIFT*SHIFT)/4*SHIFT = SHIFT/4
    #  For simplicity we weaken to -HALF_SHIFT <= offset <= HALF_SHIFT then no overflow (for 64bit): -2**128 <= +/-(2**63 * 2**63) +/- (2**63 * 2**64) <= +2**128 & overflow is at ~+/-PRIME/2 (with PRIME ~= 2**192)
    assert [range_check_ptr] = offset + HALF_SHIFT	#Ensure: -HALF_SHIFT <= offset
    assert [range_check_ptr+1] = HALF_SHIFT - offset	#Ensure: offset <= HALF_SHIFT

    assert res = a - offset * SHIFT

    # inlined int_check(res)
    assert [range_check_ptr+2] = res + HALF_SHIFT		#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+3] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr + 4

    return (res, range_check_ptr)
end

## Computes the logical left shift of an int.
func int_shl(range_check_ptr, a, b) -> (res, range_check_ptr):
    # If b >= BIT_LENGTH - 1 , the result will be zero modulo 2**(BIT_LENGTH - 1).
    tempvar res
    %{ids.res = 1 if ids.b < (ids.BIT_LENGTH - 1) else 0 %}
    # b < 2**128 & a < 2**128 is given by semantics
    # b >= BIT_LENGTH - 1
    if res == 0:
        assert [range_check_ptr] = b - (BIT_LENGTH - 1)
        let range_check_ptr = range_check_ptr + 1
        return (0, range_check_ptr)
    # b < BIT_LENGTH - 1
    else:
        assert [range_check_ptr] = (BIT_LENGTH - 2) - b
        let range_check_ptr = range_check_ptr + 1
        let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
        int_mul(range_check_ptr, a, c)
        ret
    end
end

# Computes the logical right shift of an int.
func int_shr(range_check_ptr, a : felt,  b : felt) -> (res : felt, range_check_ptr):
    #inlined int_pow2
    # If a >= BIT_LENGTH - 1, the result will be zero modulo 2**(BIT_LENGTH-1).
    tempvar res
    %{ids.res = 1 if ids.b < (ids.BIT_LENGTH - 1) else 0 %}
    # b < 2**128 & a < 2**128 is given by semantics
    # BIT_LENGTH <= b
    if res == 0:
        assert [range_check_ptr] = b - (BIT_LENGTH - 1)
        let range_check_ptr = range_check_ptr + 1
        return (0, range_check_ptr)
    #b < BIT_LENGTH
    else:
        assert [range_check_ptr] = (BIT_LENGTH - 2) - b
        let range_check_ptr = range_check_ptr + 1
        let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
        int_div(range_check_ptr, a, c)
        ret
    end
end
