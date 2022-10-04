module Main
import Starknet
%language ElabReflection

-- %logging "elab" 10
namespace CounterContract
  add : External m => (val: Felt)-> (val: Felt)-> m Unit
  get : View m => (val: Felt) -> m Felt

  %runElab contract_interface ["add", "get"]

increment : External m => (addr: Felt) -> m Unit
increment addr = map CounterContract.add_decodeResult $ callContract addr CounterContract.add_selector (CounterContract.add_encodeParams 1 1)

main = abi {functions=["increment"]}
