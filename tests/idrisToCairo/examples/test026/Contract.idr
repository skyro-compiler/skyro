module Main
import Starknet
%language ElabReflection

counter : StorageSpace [Felt] Felt

add : External m => (addr: Felt)-> (val: Felt)-> m Unit
add addr val = do
  let slot = counter `at` addr
  bal <- readStorageVar slot
  let newBal = (bal + val)
  writeStorageVar slot newBal

get : View m => (addr: Felt) -> m Felt
get addr = readStorageVar (counter `at` addr)

main = abi
        {functions=["add", "get"]}
        {storageVars = ["counter"]}
