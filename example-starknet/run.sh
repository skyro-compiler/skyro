#! /bin/bash

export STARKNET_NETWORK=alpha-goerli
export SKYRORUNTIME="../skyro-runtime" 
export PYTHONPATH="${PYTHONPATH}:${SKYRORUNTIME}"

[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate

# Cleanup
rm -rf build
mkdir -p build/deploy

# Compile the Idris2 code to a starknet contract "--directive starknet"
../build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo --directive starknet Example.idr -o Example.cairo_unformatted

# Format compiled code
cairo-format build/exec/Example.cairo_unformatted > build/deploy/Example.cairo

# Starknet-compile 
starknet-compile --cairo_path ${SKYRORUNTIME} build/deploy/Example.cairo --output build/deploy/Example_compiled.json --abi build/deploy/Example_abi.json 

# Run local python starknet test
pytest -p no:warnings --no-header --no-summary contract_test.py | head -n 4
