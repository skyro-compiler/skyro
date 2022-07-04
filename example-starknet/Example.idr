module Main
import Starknet
%language ElabReflection

-- Event with zero additional keys and two values of type Felt.
balanceChanged : EventDesc [] [Felt, Felt]

-- Storage variable with one key of type Felt storing a value of type Felt.
balance : StorageSpace [Felt] Felt

-- View function
getBalance : View m => (addr: Felt) ->  m Felt
getBalance addr = readStorageVar (balance `at` addr)

-- External function
changeBalance : External m => (difference: Felt) -> m Unit
changeBalance difference = do 
  callerAddr <- getCallerAddress
  bal <- getBalance callerAddr
  let newBal = bal + difference
  writeStorageVar (balance `at` callerAddr) newBal
  emitEvent ((balanceChanged `applyValue` callerAddr) `applyValue` newBal)

main = abi 
  {functions   = ["getBalance", "changeBalance"]} 
  {storageVars = ["balance"]} 
  {events      = ["balanceChanged"]}