module Main

import Cairo


public export
%foreign 
    "linear_implicits:range_check_ptr, pedersen_ptr"
    "imports:starkware.cairo.common.pow pow, starkware.cairo.common.hash hash2, starkware.cairo.common.cairo_builtins HashBuiltin"
    """
    code:
    # Important notes: 
    # - Parameters are untyped
    # - Implicit paramters come first in the same order as listed aboove in "linear_implicits"
    # - The results come first, followed by the implicits, again in the same order 
    func Main_externalfn(range_check_ptr, pedersen_ptr, a, b) -> (res, range_check_ptr, pedersen_ptr):
        let (p) = pow{range_check_ptr=range_check_ptr}(a,b)
        let pedersen_ptr_cast = cast(pedersen_ptr, HashBuiltin*)
        let (res) = hash2{hash_ptr=pedersen_ptr_cast}(p,p)
        return (res, range_check_ptr, cast(pedersen_ptr_cast, felt))
    end
    """
externalfn : Felt -> Felt -> Felt

%noinline
main : Cairo ()
main = output $ externalfn 2 3
