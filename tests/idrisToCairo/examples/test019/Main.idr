module Main
import Starknet
%language ElabReflection

balance : StorageSpace [Felt] Felt

viewEx : View m => m Felt
viewEx = readStorageVar (balance `at` 12)

writeEx : External m => Felt -> m Unit
writeEx val = writeStorageVar (balance `at` 12) val

main = abi {functions=["writeEx", "viewEx"]} {storageVars=["balance"]}
