#! /bin/bash

export STARKNET_NETWORK=alpha-goerli

[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate

# Cleanup
rm -rf build
mkdir -p build/deploy

# Compile Idris library to cairo "--directive starknetlib"
../build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo --directive starknetlib ExampleLib.idr -o ExampleLib.cairo_unformatted

# Format compiled code
cairo-format build/exec/ExampleLib.cairo_unformatted > build/deploy/ExampleLib.cairo

cp Contract.cairo build/deploy/Contract.cairo

# Starknet-compile wrapper contract which delegates to library (which was originally written in Idris)
starknet-compile --cairo_path build/deploy build/deploy/Contract.cairo --output build/deploy/Contract_compiled.json --abi build/deploy/Contract_abi.json 

# Deploy compiled contract
deploy_result=$(starknet deploy --contract build/deploy/Contract_compiled.json)
echo $deploy_result

export CONTRACT_ADDRESS="$(echo "$deploy_result" | grep "^Contract address: " | cut -d':' -f 2)"

invoke_result=$(starknet invoke --address ${CONTRACT_ADDRESS} --abi build/deploy/Contract_abi.json --function test)
echo $invoke_result

tx=$(echo "$invoke_result" | grep "^Transaction hash: " | cut -d':' -f 2 | tr -d '[:space:]')

starknet tx_status --hash $tx

echo "Contract successfully deployed. Observe the emitted event once the transaction is processed:"
echo "https://goerli.voyager.online/tx/${tx}#events"
