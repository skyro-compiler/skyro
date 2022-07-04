module Main

import Control.Monad.State
import Cairo

%foreign 
  "untupled:(_,_)"
  """
  code:
  func Main_cairo_identityPrim(key, world) -> (world, result):
      return (world, result=key)
  end
  """
cairo_identityPrim : Felt -> PrimCairo Felt

cairo_identity : Felt -> Cairo Felt
cairo_identity val = fromPrimCairo (cairo_identityPrim val)

multiply : Felt -> Felt -> Felt
multiply a b = a * b

foo : State (Felt, Felt) Felt
foo = do
  (current, acc) <- get
  if current == 10
    then pure acc
    else do
      put (current + 1, acc + current)
      foo
  

pythag_check : Felt -> Felt -> Felt -> Bool
pythag_check a b c = (a * a + b * b) == (c * c)

main : Cairo ()
main = do
  m1' <- cairo_identity 55
  let m1 = multiply 20 m1'
  let m2 = multiply 25 50

  if m1 == m2
    then output m1
    else output m2

  let pyth = pythag_check

  if pyth 3 4 5
    then output $ cast $ the Int32 20
    else output 40

  output $ pedersenHash 20 30
  -- output $ evalState (0, 0) foo
