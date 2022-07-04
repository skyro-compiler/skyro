FILE_NAME=$1
TEST_DIRECTORY=$(dirname $(readlink -f $0))
CURRENT_TEST=$(realpath --relative-to=$TEST_DIRECTORY $(pwd))
TIMEOUT=${2:-${TEST_TIMEOUT:-30}}
IDRIS_COMPILE_ERR=0

# source is only required if used outside of docker
# TODO Source currently doesn't work (this file is interpreted by /bin/sh, not bash, which doesn't have source)
# However, were this to be fixed, the virtual-evironment stops correctly formatting files - it doesn't leave a gap between "new" and the (, making cairo-compile FAIL!
[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate
rm -rf ./build/*

set -e

# Todo: add variable to the location of the idrisToCairo binary 
# Further options: --dumpanf anf.txt
timeout $TIMEOUT ../../../../build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo $FILE_NAME.idr -o Main.cairo_unformatted || IDRIS_COMPILE_ERR=$?
if [ $IDRIS_COMPILE_ERR -eq 124 ]; then
    echo "\033[48;5;088;1;37mTimeout after $TIMEOUT seconds when trying to compile $CURRENT_TEST from Idris.\033[0m" >&2
    exit 1
fi

cairo-format ./build/exec/$FILE_NAME.cairo_unformatted > ./build/exec/$FILE_NAME.cairo
cairo-compile ./build/exec/$FILE_NAME.cairo --cairo_path ../../../../skyro-runtime --output ./build/exec/${FILE_NAME}_compile.json

# Add python runtime support libraries to the path
export PYTHONPATH="${PYTHONPATH}:../../../../skyro-runtime"

if [ -f cairoInput.json ]; then
    cairo-run --program=./build/exec/${FILE_NAME}_compile.json --print_output --layout=all --program_input=cairoInput.json
else
    cairo-run --program=./build/exec/${FILE_NAME}_compile.json --print_output --layout=all
fi
