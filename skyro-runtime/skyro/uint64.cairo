from starkware.cairo.common.pow import pow

# Some constants
const BIT_LENGTH = 64  # I'm aiming for the rest of the file to be parametric over values for BIT_LENGTH up to 64, if possible
const SHIFT = 2 ** 64  # mjg can we eliminate this duplication?

# Represents an unsigned integer in the range [0, SHIFT)
# In other words, this is a numerical type with values in 0 to SHIFT-1 inclusive.

# Arithmetic.

# Adds two uints, with carry bit.
# Returns the result as a uint and a 1-bit carry bit
func uint_add(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res : felt
    local carry : felt
    %{ (ids.carry, ids.res) = divmod(ids.a + ids.b, ids.SHIFT) %}

    assert carry * carry = carry  # carry is 0 or 1
    assert res = a + b - carry * SHIFT

	# inlined uint_check(res)
	assert [range_check_ptr] = res
	assert [range_check_ptr+1] = (SHIFT-1) - res
	let range_check_ptr = range_check_ptr+2

    return (res, range_check_ptr)
end

# Subtracts two integers.
# Returns the result as a uint.
func uint_sub(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res : felt
    local borrow : felt
    %{
        (carry, ids.res) = divmod(ids.a - ids.b, ids.SHIFT)
        ids.borrow = -carry  # if b > a then carry is -1
    %}

    assert borrow * borrow = borrow  # borrow is 0 or 1
    assert res = a - b + borrow * SHIFT
	# inlined uint_check(res)
	assert [range_check_ptr] = res
	assert [range_check_ptr+1] =  (SHIFT-1) - res
	let range_check_ptr = range_check_ptr+2

    return (res, range_check_ptr)
end

# Multiplies two uint.
# Returns the result
func uint_mul(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
	alloc_locals
    local res : felt
    local offset : felt
    %{ (ids.offset, ids.res) = divmod(ids.a * ids.b, ids.SHIFT) %}

	# Check offset can not trigger overflow / underflow
	#  to trigger overflow offset*SHIFT must be negative
	#  to trigger underflow offset*SHIFT must be > PRIME - (SHIFT-1)**2
	#    Note: 2**128 (rangecheck) < PRIME - (SHIFT-1)**2 (e.g: 64 => approx 2**128 < 2**192? - 2**128)
	#    Note: Max needed offset*SHIFT = (SHIFT-1)*(SHIFT-1)- SHIFT = (SHIFT-2)*(SHIFT-1) < SHIFT**2
	#	 Note: for SHIFT = 2 ** 64 => offset*SHIFT < 2**128 ((2**64)**2)
	tempvar realOffset = offset * SHIFT
	assert [range_check_ptr] = realOffset # is positive & smaller 2**128 (this is exactly range_check semantic)
    assert res = a * b - realOffset

	# inlined uint_check(res)
	assert [range_check_ptr+1] = res
	assert [range_check_ptr+2] = (SHIFT-1) - res
	let range_check_ptr = range_check_ptr+3

    return (res, range_check_ptr)
end

# Division between uint.
# Returns the quotient.
# Conforms to Idris specifications: division by 0 yields error.
func uint_div(range_check_ptr, a : felt, b : felt) -> (quotient : felt, range_check_ptr):
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
	# assert [range_check_ptr+3] = (SHIFT-1) - res
	let range_check_ptr = range_check_ptr+2

    return (res, range_check_ptr)
end

func uint_mod(range_check_ptr, a : felt, b : felt) -> (remainder : felt, range_check_ptr):
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
    # assert [range_check_ptr+3] = (SHIFT - 1) - res
    let range_check_ptr = range_check_ptr+2

    return (rem, range_check_ptr)
end

# Returns -x the negation of x, in the sense that it is that number such that x + -x = 0, if addition wraps around such that 255+1=0.
# Note that -128 is 128, since 128+128=0.
func uint_neg(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
	#Todo: inline uint_sub to get rid of a copy, call, ret (3 instrs)
	#      Further the const 0 may allow some const folding
    uint_sub(range_check_ptr, 0, a)
    ret
end

# Bitwise.

# bitwise XOR
# this is just a tail call to a builtin invocation wrapper so simply inline the builtin invocation into code gen

# bitwise OR
# this is just a tail call to a builtin invocation wrapper so simply inline the builtin invocation into code gen

# bitwise AND
# this is just a tail call to a builtin invocation wrapper so simply inline the builtin invocation into code gen

# Computes the logical left shift of a uint.
#  Note: We should consider not supporting these
#  Reason: Programmers expect them to be quick and often try to optimize by replacing some *,/ with <<, >>
#          But in cairo these are horrendibly slow
#		   Inconviniently these are the only one requiring imports and they are the only one that are not ap stable
func uint_shl(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    # TODO: Analyze complexity of pow and see if a bitpattern based mult is more efficient
	#inlined uint_pow2
	# If b >= BIT_LENGTH, the result will be zero modulo 2**BIT_LENGTH.
	tempvar res
	%{ids.res = 1 if ids.b < ids.BIT_LENGTH else 0 %}
	# b < 2**128 & a < 2**128 is given by semantics
	# BIT_LENGTH <= b
    if res == 0:
        assert [range_check_ptr] = b - BIT_LENGTH
		let range_check_ptr = range_check_ptr + 1
        return (0, range_check_ptr)
	#b < BIT_LENGTH
    else:
        assert [range_check_ptr] = BIT_LENGTH - b - 1
		let range_check_ptr = range_check_ptr + 1
		let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
		uint_mul(range_check_ptr, a, c)
		ret
    end
end

# Computes the logical right shift of a uint.
#  Reason: Programmers expect them to be quick and often try to optimize by replacing some *,/ with <<, >>
#          But in cairo these are horrendibly slow
#		   Inconviniently these are the only one requiring imports and they are the only one that are not ap stable
func uint_shr(range_check_ptr, a : felt, b : felt) -> (res : felt, range_check_ptr):
    # TODO: Analyze complexity of pow and see if a bitpattern based div is more efficient
	#inlined uint_pow2
	# If a >= BIT_LENGTH, the result will be zero modulo 2**BIT_LENGTH.
	tempvar res
	%{ids.res = 1 if ids.b < ids.BIT_LENGTH else 0 %}
	# b < 2**128 & a < 2**128 is given by semantics
	# BIT_LENGTH <= b
    if res == 0:
        assert [range_check_ptr] = b - BIT_LENGTH
		let range_check_ptr = range_check_ptr + 1
        return (0, range_check_ptr)
	#b < BIT_LENGTH
    else:
        assert [range_check_ptr] = BIT_LENGTH - b - 1
		let range_check_ptr = range_check_ptr + 1
		let (c) = pow{range_check_ptr=range_check_ptr}(2, b)
		uint_div(range_check_ptr, a, c)
		ret
    end
end

func uint_cast(range_check_ptr, a : felt) -> (res : felt, range_check_ptr):
    alloc_locals
    local res : felt
    local offset : felt
    %{ (ids.offset, ids.res) = divmod(ids.a, ids.SHIFT) %}

    # Check offset can not trigger overflow / underflow
    #  to trigger overflow offset*SHIFT must be negative
    #  to trigger underflow offset*SHIFT must be > PRIME - (SHIFT-1)**2
    #    Note: 2**128 (rangecheck) < PRIME - (SHIFT-1)**2 (e.g: 64 => approx 2**128 < 2**192? - 2**128)
    #    Note: Max needed offset*SHIFT = (SHIFT-1)*(SHIFT-1)- SHIFT = (SHIFT-2)*(SHIFT-1) < SHIFT**2
    #	 Note: for SHIFT = 2 ** 64 => offset*SHIFT < 2**128 ((2**64)**2)
    tempvar realOffset = offset * SHIFT
    assert [range_check_ptr] = realOffset # is positive & smaller 2**128 (this is exactly range_check semantic)
    assert res = a - realOffset

    # inlined uint_check(res)
    assert [range_check_ptr+1] = res
    assert [range_check_ptr+2] = SHIFT - 1 - res
    let range_check_ptr = range_check_ptr+3

    return (res, range_check_ptr)
end
