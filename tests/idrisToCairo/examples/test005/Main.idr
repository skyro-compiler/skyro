module Main

import Cairo

data Expr = Val Felt
          | Add Expr Expr

eval : Expr -> Felt
eval (Val f) = f
eval (Add l r) = eval l + eval r

%noinline
main : Cairo ()
main = output $ eval (Val 1 `Add` (Val 2 `Add` Val 3))

