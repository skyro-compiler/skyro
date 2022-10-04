#! /bin/bash

[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate
rm -rf ./build/*

../build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo Example.idr -o Example.cairo_unformatted
cairo-format ./build/exec/Example.cairo_unformatted > ./build/exec/Example.cairo
cairo-compile ./build/exec/Example.cairo --output ./build/exec/Example_compiled.json

cairo-run --program=./build/exec/Example_compiled.json --print_output --layout=all
