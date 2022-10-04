This directory can be used to compile Idris2 programs to Cairo running the compiler within docker:
Run the following command in the toplevel project directory:

Linux / OSx:
```
vmcode> docker run --rm -it --platform linux/amd64 -v $(pwd)/docker-compile:/app/docker-compile skyro idrisToCairo --no-prelude -p cairolib /app/docker-compile/Example.idr -o /app/docker-compile/Example.cairo
```
Windows:

```
vmcode> docker run --rm -it -v %cd%/docker-compile:/app/docker-compile skyro idrisToCairo --no-prelude -p cairolib /app/docker-compile/Example.idr -o /app/docker-compile/Example.cairo
```