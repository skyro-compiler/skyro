FILE_NAME=$1

# source is only required if used outside of docker
[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate
rm -rf ./build/*

# Todo: add variable to the location of the idrisToCairo binary 
# Further options: --dumpanf anf.txt
../../../../build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo $FILE_NAME.idr -o Main.cairo_unformatted
cairo-format ./build/exec/$FILE_NAME.cairo_unformatted > ./build/exec/$FILE_NAME.cairo
cairo-compile ./build/exec/$FILE_NAME.cairo --output ./build/exec/${FILE_NAME}_compile.json

if [ -f cairoInput.json ]; then
    cairo-run --program=./build/exec/${FILE_NAME}_compile.json --print_output --layout=all --program_input=cairoInput.json
else
    cairo-run --program=./build/exec/${FILE_NAME}_compile.json --print_output --layout=all
fi