from starkware.cairo.common.math import assert_nn_le, assert_not_zero, assert_in_range
from starkware.cairo.common.math_cmp import is_nn

#Note: idris does not really use biguint, so this is just here as helper for bigint and thus does not have skyro calling conventions

# Some constants
# The file should be parametric over values for BIT_LENGTH up to 125
const BIT_LENGTH = 125
const SHIFT = 2 ** 125
const EON = -1

# Represents an unbounded unsigned integer (a natural number) as a pointer to the integer in memory (for Skyro compatibility the type is felt not felt*),
# represented base SHIFT as an EON-terminated list of felts in [0,SHIFT) with least significant digit first.
# For example: 1 is represented as `[1,EON]` and 0 is represented as `[EON]`.

# Verifies that `a` points to a properly-formatted biguint
func num_check_helper{range_check_ptr}(a : felt, previous_digit : felt):
    # If we terminate here, make sure the previous digit was not 0, e.g. [0,EON] is considered invalid.
    if [a] == EON:
        assert_not_zero(previous_digit)
        return ()
    else:
        assert_in_range([a], 0, SHIFT)
        num_check_helper(a + 1, [a])
        return ()
    end
end

# A valid biguint is either
# * [EON] (representing zero) or
# * some least dignificant digit followed by a valid biguint.
func num_check{range_check_ptr}(a : felt):
    if [a] != EON:
        assert_in_range([a], 0, SHIFT)
        num_check_helper(a + 1, [a])
        return ()
    end
    return ()
end

# Calculates how many digits a number has, in modulo-SHIFT representation.
# E.g. [0, 1, -1] has two digits and represents the number SHIFT.
func len(a : felt) -> (res : felt):
    if [a] == EON:
        # a is zero, nothing more to check
        return (0)
    else:
        let (tail_len) = len(a + 1)
        return (res=1 + tail_len)
    end
end

# EQUALITY

# Verifies whether `a` denotes zero
# Returns 0 if zero and 1 if nonzero
func is_not_zero(a : felt) -> (res : felt):
    if [a] == EON:
        return (0)
    else:
        return (1)
    end
end

# Verifies that `a` and `b` point to arithmetically equal biguints.
# Returns 0 if non-equal and 1 if equal
# Could be trivially implemented using compare, but the version below should be quicker and it does not require the range_check builtin
func eq(a : felt, b : felt) -> (res : felt):
    if [a] == EON:
        if [b] == EON:
            # both a and b are zero, thus equal
            return (1)
        else:
            # a is 0 and b isn't, thus they are not equal
            return (0)
        end
    else:
        # least significant digits equal?  Proceed to next digit
        if [a] == [b]:
            let (res) = eq(a + 1, b + 1)
            return (res)
        else:
            # lsd are non-equal?  Return 0.
            return (0)
        end
    end
end

# Assert that `a` and `b` point to arithmetically equal biguints.
# Fails if they don't
func assert_eq(a : felt, b : felt):
    if ([a] - EON) + ([b] - EON) == 0:
        # both a and b are zero, thus equal
        return ()
    end
    # least significant digits equal?  Proceed to next digit
    if [a] == [b]:
        assert_eq(a + 1, b + 1)
        return ()
    else:
        assert 1 = 0
        return ()
    end
end

# COMPARISON

# utility function designed to be called on two biguints of equal lenght
# returns -1 if a<b, 0 if a=b, +1 if a>b
func compare_helper{range_check_ptr}(a_ptr : felt, b_ptr : felt, len) -> (res : felt):
    if len == -1:
        # no digits left to compare.  a and b are equal
        return (0)
    end
    # is the most significant digit of a less than that of b?
    # e.g. if a = 2 and b = 2 then b-a-1 = -1.
    let (a_leading_digit_lt_b_leading_digit) = is_nn([b_ptr + len] - [a_ptr + len] - 1)
    if a_leading_digit_lt_b_leading_digit == 1:
        return (-1)
    end
    # is the most significant digit of b less than that of a?
    let (b_leading_digit_lt_a_leading_digit) = is_nn([a_ptr + len] - [b_ptr + len] - 1)
    if b_leading_digit_lt_a_leading_digit == 1:
        return (1)
    end
    # most significant digits are equal.  Must go to less significant digit
    return compare_helper(a_ptr, b_ptr, len - 1)
end

# Compare two biguints
# returns -1 if a<b, 0 if a=b, +1 if a>b
func compare{range_check_ptr}(a : felt, b : felt) -> (res : felt):
    alloc_locals
    let (a_len) = len(a)
    let (b_len) = len(b)
    let (is_a_shorter_than_b) = is_nn(b_len - a_len - 1)  # e.g. if b_len = a_len = 2 then (b_len - a_len - 1 = -1, which is negative)
    if is_a_shorter_than_b == 1:
        return (-1)
    end
    let (is_b_shorter_than_a) = is_nn(a_len - b_len - 1)  # e.g. if a_len = b_len = 2 then (a_len - b_len - 1 = -1, which is negative)
    if is_b_shorter_than_a == 1:
        return (1)
    end
    # Looks like a and b have equal digit length.
    # Time to pull out our lexicographic order!
    return compare_helper(a, b, a_len)
end

func lt{range_check_ptr}(a : felt, b : felt) -> (res : felt):
    alloc_locals
    let (cmp) = compare(a, b)
    # cmp = -1 if a<b, 0 if a=b, +1 if a>b
    # ((cmp - 1) * cmp) / 2 = 1 if cmp=-1, and = 0 if cmp=0 or 1.
    return (((cmp - 1) * cmp) / 2)
end

func lte{range_check_ptr}(a : felt, b : felt) -> (res : felt):
    alloc_locals
    let (cmp) = compare(b, a)
    # cmp = -1 if a>b, 0 if b=a, +1 if a<b
    # 1 - (((cmp - 1) * cmp) / 2) = 0 if cmp=-1,  = 1 if cmp=0 or 1.
    return (1 - (((cmp - 1) * cmp) / 2))
end

# ARITHMETIC

func assert_sum_eq_with_carry{range_check_ptr}(
        a_digits_ptr : felt, b_digits_ptr : felt, res_digits_ptr : felt, last_carry : felt):
    alloc_locals
    local a_digit : felt
    local a_continues : felt
    local b_digit : felt
    local b_continues : felt

    # has a finished?
    if [a_digits_ptr] == EON:
        a_digit = 0
        a_continues = 0
    else:
        a_digit = [a_digits_ptr]
        a_continues = 1
    end
    # has b finished?
    if [b_digits_ptr] == EON:
        b_digit = 0
        b_continues = 0
    else:
        b_digit = [b_digits_ptr]
        b_continues = 1
    end
    # Have a and b finished _and_ there's no carry?
    if a_continues + b_continues + last_carry == 0:
        # Then res should be finished.  Check for EON marker and return
        assert [res_digits_ptr] = EON
        return ()
    end
    # If we get to here, then a, b, or last_carry contribute some non-zero component.
    # Check 0 <= res_digit < SHIFT
    assert_nn_le([res_digits_ptr], SHIFT - 1)
    # a_digit + b_digit + last_carry = [res.ptr] + next_carry * SHIFT
    local next_carry = (a_digit + b_digit + last_carry - [res_digits_ptr]) / SHIFT
    # Check next_carry is 0 or 1
    assert next_carry * next_carry = next_carry
    return assert_sum_eq_with_carry(
        a_digits_ptr + a_continues, b_digits_ptr + b_continues, res_digits_ptr + 1, next_carry)
end

func add{range_check_ptr}(a : felt, b : felt) -> (res : felt):
    alloc_locals
    # guess a result
    local res_ptr : felt
    %{
        # hint populates res_ptr with correct result
        from skyro.biguint_tools import peek_one_num_from, num_add
        a = peek_one_num_from(memory, ids.a)
        b = peek_one_num_from(memory, ids.b)
        a_plus_b = num_add(a, b)
        ids.res_ptr = segments.gen_arg(a_plus_b)
    %}
    # Check res_ptr (points to a) biguint
    num_check(res_ptr)
    # check res = a + b
    assert_sum_eq_with_carry(a, b, res_ptr, 0)
    # Lucky guess!  Return the result
    return (res_ptr)
end

# Calculates a - b.
# If a >= b returns (a-b,  1)
# If a  < b returns (b-a, -1)
func sub{range_check_ptr}(a : felt, b : felt) -> (res : felt, sign : felt):
    alloc_locals
    # guess a result
    local res_ptr : felt
    local sign : felt
    %{
        # hint populates res_ptr with correct result
        from skyro.biguint_tools import peek_one_num_from, num_sub
        a = peek_one_num_from(memory, ids.a)
        b = peek_one_num_from(memory, ids.b)
        (sign, res) = num_sub(a, b)
        ids.res_ptr = segments.gen_arg(res)
        ids.sign = (sign % PRIME)
    %}
    # expect sign to be 1 or -1
    assert sign * sign = 1
    # Check res_ptr (points to a) biguint
    num_check(res_ptr)
    if sign == 1:
        # Expect res + b = a
        assert_sum_eq_with_carry(res_ptr, b, a, 0)
        return (res=res_ptr, sign=1)
    else:
        # Expect -res + b = a, so res + a = b
        assert_sum_eq_with_carry(res_ptr, a, b, 0)
        return (res=res_ptr, sign=-1)
    end
end

# multiplies a biguint by a single nonzero digit (helper function)
func mul_by_nonzero_digit_helper{range_check_ptr}(
        a_digits_ptr : felt, b : felt, res_digits_ptr : felt, last_carry : felt):
    alloc_locals
    local a_digit : felt
    local a_continues : felt
    # has a finished?
    if [a_digits_ptr] == EON:
        a_digit = 0
        a_continues = 0
    else:
        a_digit = [a_digits_ptr]
        a_continues = 1
    end
    # Has a finished and there's no carry?
    if a_continues + last_carry == 0:
        # Then res should be finished.  Check for EON marker and return
        assert [res_digits_ptr] = EON
        return ()
    end
    # If we get to here, then a or last_carry contribute some non-zero component.
    # Check 0 <= res_digit < SHIFT
    assert_nn_le([res_digits_ptr], SHIFT - 1)
    local next_carry = (a_digit * b + last_carry - [res_digits_ptr]) / SHIFT
    # Check 0 <= next_carry < SHIFT
    assert_nn_le(next_carry, SHIFT - 1)
    # a_digit * b + last_carry = [res.ptr] + next_carry * SHIFT
    return mul_by_nonzero_digit_helper(
        a_digits_ptr + a_continues, b, res_digits_ptr + 1, next_carry)
end

# Multiplies a biguint by a single (possibly zero) digit.
# This is the basic building block of the O(n^2) multiplication algorithm
func mul_by_digit{range_check_ptr}(a : felt, b : felt) -> (res : felt):
    alloc_locals
    # guess a result
    local res_ptr : felt
    # is a or b zero?  if so, return zero immediately
    if ([a] - EON) * b == 0:
        %{ ids.res_ptr = segments.gen_arg([ids.EON]) %}
        assert [res_ptr] = EON
        return (res_ptr)
    end
    %{
        # hint populates res_ptr with correct result
        from skyro.biguint_tools import peek_one_num_from, num_mul, int_to_num
        a = peek_one_num_from(memory, ids.a)
        b = int_to_num(ids.b)
        a_mul_b = num_mul(a, b)
        ids.res_ptr = segments.gen_arg(a_mul_b)
    %}
    # Check our guess for res is a biguint (omitted because we do not expect this function to be called directly)
    # num_check(res_ptr)
    # check res = a * b
    mul_by_nonzero_digit_helper(a, b, res_ptr, 0)
    # Return the result
    return (res_ptr)
end

# Multiplies two biguint following the standard O(n^2) "long multiplication" algorithm,
# inducting on the length of the second argument
# mjg might be useful to hand-optimise biguint multiplication with special algorithm if both numbers consist of at most two digits.
func mul{range_check_ptr}(a : felt, b : felt) -> (res : felt):
    alloc_locals
    # guess a result
    local res_ptr : felt
    # is a or b zero, i.e. equal to [EON]?  Then return zero immediately
    if ([a] - EON) * ([b] - EON) == 0:
        %{ ids.res_ptr = segments.gen_arg([ids.EON]) %}
        assert [res_ptr] = EON
        return (res_ptr)
    end
    # Write b as a high part `b_high`, and a final digit `b_low`.  Thus:
    #    b = b_high * PRIME + b_low
    # Then
    #    res = a * b_high * PRIME + a * b_low
    # Thus
    #    res - (a * b_low) = a * b_high * PRIME
    let b_low = [b]
    let (a__mul__b_low) = mul_by_digit(a, b_low)
    # perhaps b is a single digit, so we're done?
    if [b + 1] == EON:
        return (a__mul__b_low)
    end
    # no, b has multiple digits
    let b_high = b + 1
    let (a__mul__b_high) = mul(a, b_high)
    %{
        # hint populates res_ptr with correct result
        from skyro.biguint_tools import peek_one_num_from, num_mul
        a = peek_one_num_from(memory, ids.a)
        b = peek_one_num_from(memory, ids.b)
        a_mul_b = num_mul(a, b)
        ids.res_ptr = segments.gen_arg(a_mul_b)
    %}
    # Check our guess for res is a biguint
    num_check(res_ptr)
    # res - (a * b_low) = a * b_high * PRIME
    let (res___sub___a__mul__b_low, _) = sub(res_ptr, a__mul__b_low)
    # check final digit of res is equal to final digit of a * b_low
    assert [res___sub___a__mul__b_low] = 0
    # check equality of all but final digits of res - (a * b_low) and a * b_high * PRIME
    assert_eq(res___sub___a__mul__b_low + 1, a__mul__b_high)
    # All good!  Return the result
    return (res_ptr)
end

# Divides biguint a by biguint b, to calculate a quotient and a remainder
# Conforms to EVM specifications: division by 0 yields 0.
func div{range_check_ptr}(a : felt, b : felt) -> (res : felt, remainder : felt):
    alloc_locals
    # guess a result
    local quotient_ptr : felt
    local remainder_ptr : felt

    # If a = 0 or b = 0, return (0, 0).
    if ([b] - EON) * ([a] - EON) == 0:
        %{
            # populate quotient and remainder with 0, 0
            ids.quotient_ptr = segments.gen_arg([ids.EON])
            ids.remainder_ptr = segments.gen_arg([ids.EON])
        %}
        assert [quotient_ptr] = EON
        assert [remainder_ptr] = EON
        return (quotient_ptr, remainder_ptr)
    end
    # OK, so a and b are nonzero.
    %{
        # hint populates quotient and remainder with correct results
        from skyro.biguint_tools import peek_one_num_from, num_div
        a = peek_one_num_from(memory, ids.a)
        b = peek_one_num_from(memory, ids.b)
        (quotient, remainder) = num_div(a, b)
        ids.quotient_ptr = segments.gen_arg(quotient)
        ids.remainder_ptr = segments.gen_arg(remainder)
    %}
    # check that nonneterministically provided quotient and remainder are valid biguints
    num_check(quotient_ptr)
    num_check(remainder_ptr)
    # Check that a = quotient * b + remainder
    let (quotient_mul_b) = mul(quotient_ptr, b)
    let (quotient_mul_b__add__remainder) = add(quotient_mul_b, remainder_ptr)
    assert_eq(a, quotient_mul_b__add__remainder)
    # Great.  Return result
    return (quotient_ptr, remainder_ptr)
end

func to_felt(a : felt) -> (res : felt):
    if [a] == EON:
        return (0)
    else:
        let (res) = to_felt(a+1)
        return ((res*SHIFT)+[a])
    end
end
