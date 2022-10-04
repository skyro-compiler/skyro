FILE_NAME=$1
TEST_DIRECTORY=$(dirname $(readlink -f $0))
CURRENT_TEST=$(realpath --relative-to=$TEST_DIRECTORY $(pwd))
TIMEOUT=${2:-${TEST_TIMEOUT:-60}}
IDRIS_COMPILE_ERR=0

# source is only required if used outside of docker
# TODO Source currently doesn't work (this file is interpreted by /bin/sh, not bash, which doesn't have source)
# See run.sh
[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate
rm -rf ./build/*

set -e

# Todo: add variable to the location of the idrisToCairo binary 
# Further options: --dumpanf anf.txt  --directive verbose
timeout $TIMEOUT ../../../../build/exec/idrisToCairo --no-color --directive O3 --directive starknet --no-prelude -p cairolib --cg cairo $FILE_NAME.idr -o $FILE_NAME.cairo_unformatted || IDRIS_COMPILE_ERR=$?
if [ $IDRIS_COMPILE_ERR = 124 ]; then
    echo "\033[48;5;088;1;37mTimeout after $TIMEOUT seconds when trying to compile $CURRENT_TEST from Idris.\033[0m" >&2
    exit 1
fi

cairo-format ./build/exec/$FILE_NAME.cairo_unformatted > ./build/exec/$FILE_NAME.cairo

starknet-compile --cairo_path ../../../../skyro-runtime build/exec/$FILE_NAME.cairo --output build/exec/${FILE_NAME}_compiled.json --abi build/exec/${FILE_NAME}_abi.json --disable_hint_validation
