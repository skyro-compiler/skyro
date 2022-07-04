module Main
import Starknet
%language ElabReflection

-- Event
balanceChanged : EventDesc [] [Felt, Felt]

-- Storage variable
balance : StorageSpace [Felt] Felt

-- Constructor
constr : Constructor m => (initVal: Felt) ->  m Unit
constr initVal = writeStorageVar (balance `at` 12) initVal

-- View function
viewEx : View m => m Felt
viewEx = readStorageVar (balance `at` 12)

-- External function
writeEx : External m => Felt -> m Unit
writeEx val = do 
  bal <- viewEx
  let newBal = (bal + val)
  writeStorageVar (balance `at` 12) newBal
  emitEvent ((balanceChanged `applyValue` 12) `applyValue` newBal)

main = abi 
  {functions = ["constr", "viewEx", "writeEx"]} 
  {storageVars = ["balance"]} 
  {events = ["balanceChanged"]}