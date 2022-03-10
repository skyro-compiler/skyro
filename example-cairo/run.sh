#! /bin/bash

# Delete old build artifacts
rm -rf ./build/*

# Activate the cairo virtual environment
[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate

# Compile Example.idr to Example.cairo_unformatted
../build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo Example.idr -o Example.cairo_unformatted
# Format Example.cairo_unformatted to Example.cairo
cairo-format ./build/exec/Example.cairo_unformatted > ./build/exec/Example.cairo
# Compile Example.cairo with the official Cairo compiler
cairo-compile ./build/exec/Example.cairo --output ./build/exec/Example_compiled.json
# Run the compiled program
cairo-run --program=./build/exec/Example_compiled.json --print_output --layout=all --program_input=input.json
