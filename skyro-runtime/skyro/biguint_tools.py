from functools import reduce
from itertools import takewhile, repeat

from starkware.cairo.lang.cairo_constants import DEFAULT_PRIME

# Some key constants

# File is parametric over values for BIT_LENGTH up to 125.  Smaller values (e.g. 8) may be helpful for testing and debugging.
BIT_LENGTH = 125
SHIFT = 2**BIT_LENGTH
MIN_VAL = 0
MAX_VAL = SHIFT - 1
ALL_ONES = SHIFT - 1
# The 128 in RC_BOUND below is fixed by the Cairo system
RC_BOUND = 2**128
# EON = "End-of-number".  We use this as a convenient number used to indicate the end of a num in the Cairo VM memory
EON = -1
EON_MOD_PRIME = EON % DEFAULT_PRIME


# LIST MANIPUALTION UTILITIES

# Add the EON (end-of-number) marker -1
def add_eon(l):
    assert l == [] or l[-1] != EON  # check the EON marker is not already there
    return l + [EON]


# Strip the EON (end-of-number) marker -1
def strip_eon(l):
    assert l[-1] == EON
    return l[:-1]


# SOME NUM INSTANCES (USEFUL FOR TESTING)

# Our core numerical type `num` is a list of integers in [0, SHIFT-1), that is not terminated by 0, followed by an end-of-number marker EON.
some_num = [
    add_eon(a)
    for a in [
        [],
        [1],
        [2],
        [3],
        [BIT_LENGTH],
        [SHIFT - 1],
        [SHIFT // 2],
        [(SHIFT // 2) - 1],
        [(SHIFT // 2) + 1],
        [0, 1],
        [1, 1],
        [SHIFT - 1, SHIFT - 1],
        [SHIFT - 1, 0, 1],
        [SHIFT - 1, 1, 1],
    ]
]


# CAIRO MEMORY UTILITY FUNCTIONS


def memory_iterator_from(memory, pointer):
    # The iteration below is bounded to 2**16 steps.  The reasoning is that if we're reading more than 2**16 cells sequentially from the Cairo memory, then something has probably gone wrong:
    for _ in repeat(
            None, 2**16
    ):  # `repeat(None, 2**16)` lazily generates 2**16 copies of `None`
        yield memory[pointer]
        pointer += 1


# Read from an iterator until we reach the Cairo terminator marker EON_MOD_PRIME
# `list` forces eager evaluation of `takewhile` object
# Restore EON marker as EON (not EON_MOD_PRIME)
def read_num_from_iterator(iterator):
    return add_eon(list(takewhile(lambda i: i != EON_MOD_PRIME, iterator)))


# Peek from the runner's VM memory (treated as an iterator) until we reach the EON (end-of-number) marker.
def peek_one_num_from(memory, pointer):
    return read_num_from_iterator(iterator=memory_iterator_from(memory, pointer))


# NUM MANIPULATIONS

# a `num` consists of a list of numbers in [0, SHIFT), with no trailing zeroes, terminated with an EON (end-of-number) value
def is_num(a):
    return (
            a[-1] == EON
            and (len(a) == 1 or a[-2] != 0)
            and all([0 <= i < SHIFT for i in a[:-1]])
    )


# int to num
# An intended use case here is that `a` here is a felt, thus the integer here is obtained from the Cairo VM.
# This matters in the following sense: in principle we might bound the `while` loop below but in practice we don't because in our intended use-case, `a` is obtained from a felt and so is bounded by DEFAULT_PRIME.
def int_to_num(a):
    acc = []
    while a != 0:
        acc.append(a & ALL_ONES)
        a = a >> BIT_LENGTH
    return add_eon(acc)


# num to int
# if a = [1, 2, 3] then reversed(a) = [3, 2, 1]
def num_to_int(a):
    return reduce(
        lambda acc, next_element: next_element + (acc << BIT_LENGTH),
        reversed(strip_eon(a)),
        0,
    )


# Slow but clean num addition, for testing and Cairo hints
def num_add(a, b):
    return int_to_num(num_to_int(a) + num_to_int(b))


# Slow but clean num subtraction, for testing and Cairo hints
# If a >= b returns ( 1, a-b)
# If a  < b returns (-1, b-a)
def num_sub(a, b):
    res = num_to_int(a) - num_to_int(b)
    if res >= 0:
        return (1, int_to_num(res))
    else:
        return (-1, int_to_num(-res))


# Slow but clean biguint multiplication, for testing and Cairo hints
def num_mul(a, b):
    return int_to_num(num_to_int(a) * num_to_int(b))


# Slow but clean num divmod, for testing and Cairo hints
def num_div(a, b):
    (quotient, remainder) = divmod(num_to_int(a), num_to_int(b))
    return (int_to_num(quotient), int_to_num(remainder))


# maps a signed integer to a sign and an absolute value.  0 maps to (1, 0)
int_to_sign_and_abs = lambda a: (1, a) if a >= 0 else (-1, -a)


# "better" = "more relevant to our needs here"
# better_divmod( 5, 3) = ( 1,  2)
# better_divmod(-5,-3) = ( 1, -2)
# better_divmod(-5, 3) = (-1, -2)
#        divmod(-5, 3) = (-2,  1)
def better_divmod(a, b):
    if a == 0 or b == 0:
        return (0, 0)
    (a_sign, a_abs) = int_to_sign_and_abs(a)
    (b_sign, b_abs) = int_to_sign_and_abs(b)
    quotient = (
            a_sign * b_sign * (a_abs // b_abs)
    )  # this rounds towards zero; a // b rounds down always (including on negative numbers)
    # a = b * quotient + remainder
    remainder = a - b * quotient
    return (quotient, remainder)
