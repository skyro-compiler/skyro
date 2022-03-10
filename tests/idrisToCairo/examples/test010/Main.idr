module Main

import Cairo

flip : (a,b) -> (b,a)
flip (a,b) = (b,a)

%noinline
main : Cairo ()
main = output $ fst (flip (1,2))
