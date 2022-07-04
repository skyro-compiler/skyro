#!/usr/bin/env bash
FILE_NAME=$(tr -d '\r\n' <<< "$1") # If the `run` file is saved with a trailing newline, it's included in $1 and messes up the rest; so we strip it
TEST_DIRECTORY=$(dirname $(readlink -f $0))
CURRENT_TEST=$(realpath --relative-to=$TEST_DIRECTORY $(pwd))
TIMEOUT=${2:-${TEST_TIMEOUT:-30}}
SKYRO_COMPILE_ERR=0

# Make sure directory exists
mkdir -p ./build
# source is only required if used outside of docker
# TODO May fail when encountering MKCON calls, see run.sh
[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate
rm -rf ./build/*

set -e

../../../build/exec/skyroToCairo -i $FILE_NAME.skyro -o ./build/$FILE_NAME.cairo_unformatted || SKYRO_COMPILE_ERR=$?
if [ $SKYRO_COMPILE_ERR -eq 124 ]; then
    echo "\033[48;5;088;1;37mTimeout after $TIMEOUT seconds when trying to compile $CURRENT_TEST from Skyro.\033[0m" >&2
    exit 1
fi

cairo-format ./build/$FILE_NAME.cairo_unformatted > ./build/$FILE_NAME.cairo
cairo-compile ./build/$FILE_NAME.cairo --cairo_path ../../../skyro-runtime --output ./build/${FILE_NAME}_compile.json

# Add python runtime support libraries to the path
export PYTHONPATH="${PYTHONPATH}:../../../../skyro-runtime"

if [ -f cairoInput.json ]; then
    cairo-run --program=./build/${FILE_NAME}_compile.json --print_output --layout=all --program_input=cairoInput.json
else
    cairo-run --program=./build/${FILE_NAME}_compile.json --print_output --layout=all
fi
