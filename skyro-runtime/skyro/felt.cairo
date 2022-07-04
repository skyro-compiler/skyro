from starkware.cairo.common.math_cmp import assert_lt_felt
from starkware.cairo.common.math_cmp import assert_le_felt

# Checks if the unsigned integer lift (as a number in the range [0, PRIME)) of a is lower than
# that of b.
# See split_felt() for more details.
# Returns 1 if true, 0 otherwise.
func felt_lt(range_check_ptr,a, b) -> (res, range_check_ptr):
    %{ memory[ap] = 0 if (ids.a % PRIME) < (ids.b % PRIME) else 1 %}
    jmp not_lt if [ap] != 0; ap++
    assert_lt_felt{range_check_ptr=range_check_ptr}(a, b)
    return (1, range_check_ptr)

    not_lt:
    assert_le_felt{range_check_ptr=range_check_ptr}(b, a)
    return (0, range_check_ptr)
end

# Checks if the unsigned integer lift (as a number in the range [0, PRIME)) of a is lower than
# or equal to that of b.
# See split_felt() for more details.
# Returns 1 if true, 0 otherwise.
func felt_lte(range_check_ptr, a, b) -> (res, range_check_ptr):
    %{ memory[ap] = 0 if (ids.a % PRIME) <= (ids.b % PRIME) else 1 %}
    jmp not_le if [ap] != 0; ap++
    assert_le_felt{range_check_ptr=range_check_ptr}(a, b)
    return (1, range_check_ptr)

    not_le:
    assert_lt_felt{range_check_ptr=range_check_ptr}(b, a)
    return (0, range_check_ptr)
end
