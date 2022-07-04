module Main
import Starknet
%language ElabReflection

data Expr: Type where 
  Add : Expr -> Expr -> Expr
  Val : Felt -> Expr

evalExpr : (Felt -> Felt) -> (expr:Expr) -> Felt
evalExpr f (Val v) = f v
evalExpr f (Add l r) = f ((evalExpr f l) + (evalExpr f r))

-- Add (Val 1) (Val 2) ~ [0,1,1,1,2]
eval : View m => (expr:Expr) -> m Felt
eval exp = pure $ evalExpr (\id => 2*id) exp

main = abi {functions=["eval"]}
