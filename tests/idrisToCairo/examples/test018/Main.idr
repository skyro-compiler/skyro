module Main
import Starknet
%language ElabReflection

record RecType where
  constructor MkRec
  valA : Felt
  valB : Felt

data MyEnum = A | B | C
data Command = Add RecType | Sub RecType

viewEx : View m => (addr:Felt) -> m Felt
viewEx addr = readStorage (MkStorageAddr addr)

recEx : External m => MyEnum -> Felt -> Felt -> m Command
recEx A a b = pure $ Add (MkRec a b)
recEx B a b = pure $ Sub (MkRec a b)
recEx C a b = pure $ Sub (MkRec b a)

-- Todo: Seperate test
-- recEx3 : External m => Segment -> m Segment
-- recEx3 a = pure $ a

eval : Command -> Felt
eval (Add (MkRec a b)) = a + b
eval (Sub (MkRec a b)) = a - b

writeEx : External m => (addr:Felt) -> (value:Felt) -> m Unit
writeEx addr value = do
   res <- viewEx addr
   cmd <- recEx A 1 5
   let res2 = eval cmd
   writeStorage (MkStorageAddr addr) (res + value + res2)

constrEx : Constructor m => (addr:Felt) -> (initVal:Felt) -> (n:Nat) ->  m Unit
constrEx addr initVal _ = writeStorage (MkStorageAddr addr) initVal

main = abi {functions=["writeEx", "viewEx", "recEx", "constrEx"]}
