module Main
import Cairo

%noinline
main : Cairo ()
main = do
    ptr <- createMemory
    writeMemory 0 42 ptr
    res <- readMemory 0 ptr
    output res
