module Main
import Starknet
%language ElabReflection

data Expr : Type -> Type where 
  Add : Expr a -> Expr a -> Expr a
  Val : a -> Expr a

-- Add (Val 1) (Val 2) ~ [0,1,1,1,2]
eval : View m => (expr:Expr Felt) -> m Felt
eval (Val v) = pure v
eval (Add l r) = do 
  l' <- eval l
  r' <- eval r
  pure $ l' + r'

main = abi {functions=["eval"]}
