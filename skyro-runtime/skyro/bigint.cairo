from skyro.biguint import len as biguint_len
from skyro.biguint import is_not_zero as biguint_is_not_zero
from skyro.biguint import eq as biguint_eq
from skyro.biguint import compare as biguint_compare
from skyro.biguint import add as biguint_add
from skyro.biguint import sub as biguint_sub
from skyro.biguint import mul as biguint_mul
from skyro.biguint import div as biguint_div
from skyro.biguint import to_felt as biguint_to_felt

# Some constants
# The file should be parametric over values for BIT_LENGTH up to 125
const BIT_LENGTH = 125
const SHIFT = 2 ** 125
const EON = -1

# Calculates how many digits the absolute value of a number has, in modulo-SHIFT representation.
# E.g. (-1, [0, 1, -1]) has two digits and represents the number -SHIFT.
func len(a : felt) -> (res : felt):
    return biguint_len([a+1])
end

# EQUALITY

# Verifies whether `a` denotes zero
# Returns 0 if zero and 1 if nonzero
func is_not_zero(a : felt) -> (res : felt):
    return biguint_is_not_zero([a+1])
end

# Verifies that `a` and `b` point to arithmetically equal bigints.
# Returns 0 if non-equal and 1 if equal
# Could be trivially implemented using compare, but the version below should be quicker and it does not require the range_check builtin
func eq(a : felt, b : felt) -> (res : felt):
    if ([[a+1]] + [[b+1]]) == -2:
        # Absolute values of a and b are both zero?  Equal!
        return (1)
    end
    if [a] != [b]:
        # Not both zero, and have distinct signs?  Non-equal!
        return (0)
    end
    return biguint_eq([a+1], [b+1])
end

# Assert that `a` and `b` point to arithmetically equal biguints.
# Fails if they don't
# This rather brutal implementation just calls `eq`
func assert_eq(a : felt, b : felt):
    let (res) = eq(a, b)
    assert res = 1
    return ()
end

# COMPARISON

# utility function designed to be called on two biguints of equal lengh
# returns -1 if a<b, 0 if a=b, +1 if a>b

# Compare two biguints
# returns -1 if a<b, 0 if a=b, +1 if a>b
func compare(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    if ([[a+1]] + [[b+1]]) == -2:
        # Absolute values of a and b are both zero?  Equal!
        return (0, range_check_ptr)
    end
    if [b] - [a] == 2:
        # b positive and a negative and at least one nonzero?  a < b!
        return (-1, range_check_ptr)
    end
    if [a] - [b] == 2:
        # a positive and b negative and at least one nonzero?  a > b!
        return (1, range_check_ptr)
    end
    # a and b have the same sign (and at least one of them is nonzero)
    # Compare |a| with |b|
    with range_check_ptr:
        let (res_abs) = biguint_compare([a+1], [b+1])
    end
    # Return the sign of a multiplied by the result
    return ([a] * res_abs, range_check_ptr)
end

func lt(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    let (cmp, range_check_ptr) = compare(range_check_ptr, a, b)
    # cmp = -1 if a<b, 0 if a=b, +1 if a>b
    # ((cmp - 1) * cmp) / 2 = 1 if cmp=-1, and = 0 if cmp=0 or 1.
    return (((cmp - 1) * cmp) / 2, range_check_ptr)
end

func lte(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    let (cmp, range_check_ptr) = compare(range_check_ptr, b, a)
    # cmp = -1 if a>b, 0 if b=a, +1 if a<b
    # 1 - (((cmp - 1) * cmp) / 2) = 0 if cmp=-1,  = 1 if cmp=0 or 1.
    return (1 - (((cmp - 1) * cmp) / 2), range_check_ptr)
end

# ARITHMETIC

func neg(a : felt) -> (res : felt):
    tempvar res = new([a] * (-1), [a+1])
    return (cast(res,felt))
end

func add(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    let a_abs = [a+1]
    let b_abs = [b+1]
    if [a] * [b] == 1:
        # If a and b are both positive or both negative
        # then res=a+b has the sign of a (and of b)
        let res_sign = [a]
        with range_check_ptr:
            let (res_abs) = biguint_add(a_abs, b_abs)
        end
        tempvar res = new(res_sign,res_abs)
        return (cast(res,felt), range_check_ptr)
    else:
        if [a] == 1:
            with range_check_ptr:
                # a is positive, b is negative.  a+b = |a|-|b|
                let (res_abs, res_sign) = biguint_sub(a_abs, b_abs)
            end
            tempvar res = new(res_sign,res_abs)
            return (cast(res,felt), range_check_ptr)
        else:
            with range_check_ptr:
                # b is positive, a is negative.  a+b = |b|-|a|
                let (res_abs, res_sign) = biguint_sub(b_abs, a_abs)
            end
            tempvar res = new(res_sign,res_abs)
            return (cast(res,felt), range_check_ptr)
        end
    end
end

# Calculates a - b.
func sub(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    let (neg_b) = neg(b)
    let (a_sub_b, range_check_ptr) = add(range_check_ptr, a, neg_b)
    return (a_sub_b, range_check_ptr)
end

func mul(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    with range_check_ptr:
        # sign of mult is mult of signs
        let res_sign = [a] * [b]
        let (res_abs) = biguint_mul([a+1], [b+1])
    end
    tempvar res = new(res_sign,res_abs)
    return (cast(res,felt), range_check_ptr)
end

func div(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    with range_check_ptr:
        # sign of div is mult of signs
        let (res_abs, remainder_abs) = biguint_div([a+1], [b+1])
    end
    let res_sign = [a] * [b]
    tempvar res2_raw = new(res_sign,res_abs)
    let res2 = cast(res2_raw,felt)
    if [a] == -1 :
        if [remainder_abs] == EON:
            return (res2, range_check_ptr)
        else:
            tempvar one = new([b], new(1,EON))
            let (res3, range_check_ptr) = sub(range_check_ptr, res2, cast(one,felt))
            return (res3, range_check_ptr)
        end
    else:
        return (res2, range_check_ptr)
    end
end

func mod(range_check_ptr, a : felt, b : felt) -> (rem : felt, range_check_ptr):
    # sign of div is mult of signs
    with range_check_ptr:
        let (res_abs, remainder_abs) = biguint_div([a+1], [b+1])
    end
    tempvar res = new(1, remainder_abs)
    return (cast(res,felt), range_check_ptr)
end

# From Felt
# Assumes abs(felt) < SHIFT
func from_small_felt(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local sign
    if a == 0:
        tempvar sres = new(1, new(EON))
        return (cast(sres,felt), range_check_ptr)
    end

    %{
        from starkware.cairo.common.math_utils import as_int
        input = as_int(ids.a, PRIME)
        ids.sign = -1 if input < 0 else 1
    %}

    # Check sign is -1 or 1
    assert sign*sign = 1

    # Compute absolute
    tempvar absolute = sign*a

    # Check absolute is in range
    assert [range_check_ptr] = absolute
    assert [range_check_ptr+1] = SHIFT - absolute
    let range_check_ptr = range_check_ptr+2

    # Construct BigInt
    tempvar res = new(sign, new(absolute,EON))
    return (cast(res,felt), range_check_ptr)
end


# signed least significant entry
func signed_lsf(a : felt) -> (res : felt):
    let res = [a]*[[a+1]]
    return (res)
end

# To Felt
func to_felt(a : felt) -> (res : felt):
    let (res) = biguint_to_felt([a+1])
    return ([a]*res)
end


func checked_to_felt(range_check_ptr, a : felt) -> (res : felt, len : felt,  range_check_ptr):
    if [a] == EON:
        return (0, 0, range_check_ptr)
    else:
        assert [range_check_ptr] = [a]
        assert [range_check_ptr+1] = SHIFT - [a]
        let (rec, len, range_check_ptr) = checked_to_felt(range_check_ptr+2, a+1)
        return ((rec*SHIFT)+[a], len+1, range_check_ptr)
    end
end

# From Felt
func from_felt(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local isSmall
    local sign
    local arr
    %{
        from starkware.cairo.common.math_utils import as_int
        input = as_int(ids.a, PRIME)
        shift = as_int(ids.SHIFT, PRIME)
        ids.isSmall = 1 if (input < shift) and (input > -shift) else 0
        ids.sign = (-1 % PRIME) if input < 0 else 1
    %}
    if isSmall == 0:
        # Check sign is -1 or 1
        assert sign*sign = 1

        # Compute absolute
        tempvar absolute = sign*a
        %{
            from starkware.cairo.common.math_utils import as_int
            ids.arr = segments.add()
            input = as_int(ids.absolute, PRIME)
            shift = as_int(ids.SHIFT, PRIME)
            (c1, e1) = divmod(input, shift)
            memory[ids.arr] = e1 % PRIME
            (c2, e2) = divmod(c1, shift)
            memory[ids.arr+1] = e2 % PRIME
            if c2 == 0:
                memory[ids.arr+2] = ids.EON % PRIME
            else:
                (d, e3) = divmod(c2, shift)
                memory[ids.arr+2] = e3 % PRIME
                memory[ids.arr+3] = ids.EON % PRIME
        %}

        let (raw, len, range_check_ptr) = checked_to_felt(range_check_ptr, arr)
        # Todo: Not correct (could be 3)
        # Note: it could be a len 3 value with very small third comp
        #       However, the 3rd can not be anything, but must be rather small
        #       This is not implemented yet and to be save we support only numbers up to 2^250
        assert len = 2
        assert absolute = raw
        tempvar res = new(sign,arr)
        return (cast(res,felt),range_check_ptr)
    else:
        let (sres, range_check_ptr) = from_small_felt(range_check_ptr, a)
        return (sres, range_check_ptr)
    end
end
