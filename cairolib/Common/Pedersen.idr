module Common.Pedersen

import Common

public export
%foreign 
    "apStable:True"
    "linear_implicits:pedersen_ptr"
    """
    code:
    func Common_Pedersen_pedersenHash(pedersen_ptr, x, y) -> (result, pedersen_ptr):
        assert [pedersen_ptr] = x
        assert [pedersen_ptr + 1] = y
        return ([pedersen_ptr + 2], pedersen_ptr + 3)
    end
    """
pedersenHash : Felt -> Felt -> Felt