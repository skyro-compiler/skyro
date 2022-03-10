%lang starknet
from ExampleLib import main

@external
func test{syscall_ptr}():
    let (syscall_ptr) = main(syscall_ptr)
    return ()
end

