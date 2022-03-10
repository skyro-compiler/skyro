module Main

import Cairo

data Clist a = Nil | (::) a (Clist a)

clength : Clist a -> Felt
clength Nil = 0
clength (_::as) = 1 + clength as

cfoldl : (a -> e -> a) -> a -> Clist e -> a
cfoldl _ acc Nil = acc
cfoldl f acc (e::es) = cfoldl f (f acc e) es

export
hashChain' : (l: Clist Felt) -> Felt
hashChain' l = cfoldl pedersenHash (clength l) l

%noinline
main : Cairo ()
main = output (hashChain' [1,2,3,4,5,6,7,8,9,10])
