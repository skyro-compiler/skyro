||| The mandatory fibonacci
module Main
import Cairo

fib : (i: Felt) -> Felt
fib n = if n == 0 || n == 1
          then n 
          else fib (n - 1) + fib (n - 2)

%noinline
main : Cairo ()
main = output (fib 5)
