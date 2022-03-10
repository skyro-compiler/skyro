import Starknet

export
fib : (i: Felt) -> Felt
fib n = if n == 0 || n == 1
    then n
    else fib (n - 1) + fib (n - 2)


export
main : Cairo ()
main = 
  do
     val <- storageRead 123
     storageWrite 123 (val + fib 5)

     topic <- createMemory
     writeMemory 0 123 topic

     value <- createMemory
     writeMemory 0 val value
     
     emitEvent 1 topic 1 value
