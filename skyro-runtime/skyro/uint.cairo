
# Returns 1 if the first unsigned integer is less than the second unsigned integer, otherwise returns 0.
func uint_lt(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
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

# Returns 1 if the first unsigned integer is less than or equal to the second unsigned integer, otherwise returns 0.
func uint_lte(range_check_ptr, a : felt, b : felt) -> (res, range_check_ptr):
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
