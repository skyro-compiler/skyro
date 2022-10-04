from starkware.cairo.common.math_cmp import is_le_felt

# Checks if the unsigned integer lift (as a number in the range [0, PRIME)) of a is lower than
# that of b.
# See split_felt() for more details.
# Returns 1 if true, 0 otherwise.
func felt_lt(range_check_ptr,a, b) -> (res, range_check_ptr):
    if a == b:
        return (0, range_check_ptr)
    else:
        with range_check_ptr:
            let (res) = is_le_felt(a, b)
        end
        return (res, range_check_ptr)
    end
end

# Checks if the unsigned integer lift (as a number in the range [0, PRIME)) of a is lower than
# or equal to that of b.
# See split_felt() for more details.
# Returns 1 if true, 0 otherwise.
func felt_lte(range_check_ptr, a, b) -> (res, range_check_ptr):
    with range_check_ptr:
        let (res) = is_le_felt(a, b)
    end
    return (res, range_check_ptr)
end
