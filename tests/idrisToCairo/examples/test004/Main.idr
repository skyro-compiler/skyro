||| Compiling an Idris2 interface and implementations
module Main

import Cairo

interface I a where
  f : a -> Felt

I Felt where
  f = id

I Bool where
  f False = 0
  f True = 1

%noinline
main : Cairo ()
main = do
    output $ f True
    output $ f (the Felt 42)
