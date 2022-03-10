||| Fibonacci but in linear time
module Main
import Cairo

-- O(n) version
fibl : Felt -> Felt
fibl n = go n 0 1
  where
    go : Felt -> Felt -> Felt -> Felt
    go n a b = if n == 0 then a else go (n-1) b (a+b)

%noinline
main : Cairo ()
main = output (fibl 10)
