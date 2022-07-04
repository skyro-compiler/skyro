module Main
import Starknet
%language ElabReflection

constrEx : Constructor m => (addr:Felt) -> (initVal:Felt)->  m Unit
constrEx addr initVal = writeStorage (MkStorageAddr addr) initVal

viewEx : View m => (addr:Felt) -> m Felt
viewEx addr = readStorage (MkStorageAddr addr)

main = abi {functions=["constrEx", "viewEx"]}
