module Main

import Cairo

PRIME : Felt
PRIME = fromInteger 3618502788666131213697322783095070105623107215331596699973092056135872020481

-- The +1 -1 simulates integer division on this specific felt
HALF : Felt
HALF = ((PRIME + 1) `div` 2) -1

%noinline
main : Cairo ()
main = do
    output HALF
    output (HALF + 1)
    let r = 1 `div` 3
    output r
    output (r * 3)
