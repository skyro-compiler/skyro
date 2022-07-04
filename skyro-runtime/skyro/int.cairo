# Comparisons
# Returns 1 if the first integer is less than the second, otherwise returns 0.
func int_lt(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
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

# Returns 1 if the first int is less than or equal to the second int, otherwise returns 0.
func int_lte(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
    tempvar res
    %{
        from starkware.cairo.common.math_utils import as_int
        ids.res = 1 if as_int(ids.a,PRIME) <= as_int(ids.b,PRIME) else 0
    %}
    # -2**127 <= b < 2**127 & -2**127 <= a < 2**127 is given by semantics (actuall even tighter as max 64bits)
    # implies: a - b < 2**128 & b - a < 2**128 (meaning in range check upper bound)
    # b < a
    if res == 0:
        assert [range_check_ptr] = a - b - 1
        let range_check_ptr = range_check_ptr + 1
        return (0, range_check_ptr)
    # a <= b
    else:
        assert [range_check_ptr] = b - a - 0 		#-0 is for ap stability improves worse case in code gen
        let range_check_ptr = range_check_ptr + 1
        return (1, range_check_ptr)
    end
end
