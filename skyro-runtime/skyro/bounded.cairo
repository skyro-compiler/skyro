from starkware.cairo.common.math import signed_div_rem

# 125bit signed int
# Fails assert on over/underflow
# The reason for 125 is because 2^125 * 2^125 < PRIME but 2^126 * 2^126 > PRIME
#  Meaning with 126+ multiplication could overflow the felt, leading to accepted values even if they should not

const BIT_LENGTH = 125  # I'm aiming for the rest of the file to be parametric over values for BIT_LENGTH up to 64, if possible
const SHIFT = 2 ** 125
const HALF_SHIFT = 2 ** 124

# EQUALITY
# Verifies that `a` and `b` point to arithmetically equal boundedInts.
# Returns 0 if non-equal and 1 if equal
# Should be inlined?
func bounded_eq(a : felt, b : felt) -> (res : felt):
    if a == b:
       return (1)
    else:
       return (0)
    end
end

# COMPARISON
func bounded_lt(range_check_ptr,a, b) -> (res, range_check_ptr):
    %{ memory[ap] = 0 if (ids.a % PRIME) < (ids.b % PRIME) else 1 %}
    jmp not_lt if [ap] != 0; ap++
    assert_lt_felt{range_check_ptr=range_check_ptr}(a, b)
    return (1, range_check_ptr)

    not_lt:
    assert_le_felt{range_check_ptr=range_check_ptr}(b, a)
    return (0, range_check_ptr)
end

func bounded_lte(range_check_ptr, a, b) -> (res, range_check_ptr):
    %{ memory[ap] = 0 if (ids.a % PRIME) <= (ids.b % PRIME) else 1 %}
    jmp not_le if [ap] != 0; ap++
    assert_le_felt{range_check_ptr=range_check_ptr}(a, b)
    return (1, range_check_ptr)

    not_le:
    assert_lt_felt{range_check_ptr=range_check_ptr}(b, a)
    return (0, range_check_ptr)
end

# ARITHMETIC
# Should be inlined?
func bounded_add(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    let res = a + b
    assert [range_check_ptr] = res + HALF_SHIFT			#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+1] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr+2
    return (res, range_check_ptr)
end

# Should be inlined
func bounded_unchecked_add(a : felt, b : felt) -> (res : feltr):
    let res = a + b
    return (res)
end

# Should be inlined?
func bounded_sub(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    let res = a - b
    assert [range_check_ptr] = res + HALF_SHIFT			#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+1] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr+2
    return (res, range_check_ptr)
end

# Should be inlined
func bounded_unchecked_sub(a : felt, b : felt) -> (res : feltr):
    let res = a - b
    return (res)
end

# Should be inlined?
func bounded_mul(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    let res = a * b
    assert [range_check_ptr] = res + HALF_SHIFT			#Ensure: -HALF_SHIFT <= res
    assert [range_check_ptr+1] = HALF_SHIFT - 1 - res	#Ensure: res < HALF_SHIFT
    let range_check_ptr = range_check_ptr+2
    return (res, range_check_ptr)
end

# Should be inlined
func bounded_unchecked_mul(a : felt, b : felt) -> (res : feltr):
    let res = a * b
    return (res)
end

func bounded_div(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res
    local rem
    local signB
    %{
        from starkware.cairo.common.math_utils import as_int
        signB = 1 if as_int(ids.b, PRIME) >= 0 else -1
        ids.signB = signB % PRIME
        b = as_int(ids.b,PRIME)
        #Note fails if b = 0, which is ok as this is expected (Hint can not find a solution)
        # Question: is it ok to fail in hint or is a check with assert 0 = 1 needed
        (res, rem) = divmod(as_int(ids.a,PRIME), b)
        if rem < 0:
            ids.res = (res+1) % PRIME
            ids.rem = (rem-b) % PRIME
        else:
            ids.res = res % PRIME
            ids.rem = rem % PRIME
    %}

    #check that the reverse is correct
    assert res * b + rem = a

    #check the sign helpers are -1 or 1
    assert signB*signB = 1

    # check  that rem is positive
    assert [range_check_ptr] = rem

    # check that rem is between 0 and abs(b) (exclusive b, inclusive 0)
    # Note: if hint lies about signB then signB*b is negative and because rem is proofen to be positive the rangecheck fails
    # Note: will fail if b = 0 which is the expected behaviour
    assert [range_check_ptr+1] = signB*b - rem - 1	# rem < abs(b)

    let range_check_ptr = range_check_ptr + 2
    return (res, range_check_ptr)
end

#no unchecked div variant, as hint could cheat so we need to ckeck always (and the bound check even holds implicitly)
