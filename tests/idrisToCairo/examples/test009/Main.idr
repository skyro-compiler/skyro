{- 
%builtins output pedersen

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.hash import hash2
from starkware.cairo.common.serialize import serialize_word

func main{output_ptr : felt*, pedersen_ptr : HashBuiltin*}():
    let (res) = hash2{hash_ptr=pedersen_ptr}(1,2)
    serialize_word(res + 1)
    return ()
end
-}

module Main

import Cairo

%noinline
main : Cairo ()
main =
    output (1 + (pedersenHash 1 2))
