module Main
import Starknet
%language ElabReflection

viewSegEx : View m => Segment -> m Segment
viewSegEx a = pure $ a

viewNatEx : View m => Nat -> m Nat
viewNatEx a = pure $ S a

viewIntegerEx : View m => Integer -> m Integer
viewIntegerEx a = pure $ a + 5

main = abi {functions=["viewSegEx", "viewNatEx", "viewIntegerEx"]}
