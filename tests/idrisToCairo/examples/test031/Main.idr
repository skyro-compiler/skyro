module Main
import Starknet
%language ElabReflection

stoZero : StorageSlot Felt

checkZero : View m => m Unit
checkZero = do
    n <- readStorageVar stoZero
    if n == 0
        then pure ()
        else assert_total $ idris_crash "n is not zero"

testFunc : External m => m Unit
testFunc = do
    -- if condition is changed to 0 == 0 it will work
    if 1 == 0
        then checkZero
        else pure ()

main = abi
  {functions = ["testFunc"]}
  {storageVars = ["stoZero"]}
