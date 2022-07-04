# Closure Gen
Their are many ways to compile closures and apply calls. Depending on the target platforms capabilites not all are possible.

## Candidates

### Defunctionalisation
When using defuntionalisation, a data type is generated with one constructor per parameter for each function.
As an example the function with following signature:
```    
Example : a -> b -> c -> d
```
Leads to the following constructors:
```    
Example0
Example1 a
Example2 a b
```
The apply is implemented over a giant jump table matching on the constructor and generating the next in line.

For example `apply Example1 b == Example2 a b`. The last one calls the function instead.

The primary advantage of defuntionalisation is that all dynamic calls are eliminated and replaced with a jump table.

### Currying
When using currying, an additional functions type per parameter of the original function is generated. 
As an example the function with following signature:
```    
Example : a -> b -> c -> d
```
Leads to the following functions
```    
example0 : Example0 -> a -> Example1
example1 : Example1 -> b -> Example2
example2 : Example2 -> c -> d
```
In the example the data `Example*` corresponds to a pointer into a memory region containing the pointer to the `example*` function followed by the `*` arguments.
An apply simply calls the stored function `example*` and passes the `Example*` and the next param

## Comparison
The following table compares the solutions including the proof of work concept currently implemented.

| Criteria          | Defunct     | Curry       | Current     |
| ----------------- | ----------- | ----------- | ----------- |
| Code Size         | Ok          | Ok          | Good        |
| Performance       | Ok          | Good        | Bad         |
| Code Readability  | Ok          | Good        | Bad         |

Unless code size is the optimisation target the currying implementation is the winner.
Because of this the current implementation will be replaced with curring in the future


# Implementation
As an example for the currying strategy, we use the following example:
```
add : Felt -> Felt -> Felt
add a b = a + b

hof : (a -> b -> c) -> a -> b -> c
hof f a b = f a b

%noinline
main : Cairo ()
main = output (hof add 1 2)
```

`add` is passed as the first argument to `hof`. And `hof` is applied to two arguments one after another. The first application of `f` to `a` results in a new closure which is then applied to `b`.


```
%builtins output
from starkware.cairo.common.alloc import alloc

programStart:

# The function which is used as a closure.
func add(a, b) -> (res):
    return (a+b)
end

# Takes the last argument and calls the function.
func mn__curried__Main_mn__main_0_1(p_0, p_1) -> (applied_ret):
    # Get previous arguments from the closure.
    let b_1 = [p_0 + 1]
    # And call the target functions 
    let (b_0) = add(b_1, p_1)
    return (b_0)
end

# Takes the first argument and returns a new closure.
func mn__curried__Main_mn__main_0_2(p_0, p_1) -> (applied_ret):
    # MKCLOSURE
    const mn__curried__Main_mn__main_0_2_names__0_addr_ = mn__curried__Main_mn__main_0_1 - programStart
    tempvar b_0_ptr_1 = new (mn__curried__Main_mn__main_0_2_names__0_addr_, p_1)
    let b_0 = cast(b_0_ptr_1, felt)

    return (b_0)
end


func Main_hof(clo, arg1, arg2) -> (res):
    # APPLY to first argument
    tempvar dispatcher = [clo] - (JumpPoint1 - programStart)

    [ap] = clo; ap++
    [ap] = arg1; ap++

    JumpPoint1:
    call rel dispatcher
    let res1 = [ap - 1]
    # res1 is the result (a closure) of applying to the first argument

    # APPLY to second argument
    tempvar closure = res1
    tempvar dispatcher = [closure] - (JumpPoint2 - programStart)

    [ap] = closure; ap++
    [ap] = arg2; ap++

    JumpPoint2:
    call rel dispatcher
    let b_0 = [ap - 1]

    return (b_0)
end



# ExtFunDef

func main{output_ptr}():
    # Create a closure which only contains its address relative to the label `programStart`
    const Main_main_names__0_addr_ = mn__curried__Main_mn__main_0_2 - programStart
    # This is the closure, which has 0 arguments
    tempvar b_2_ptr_0 = new (Main_main_names__0_addr_)
    let b_2 = cast(b_2_ptr_0, felt)

    # Pass the closure to `hof`
    let (b_1) = Main_hof(b_2, 1, 2)

    assert [output_ptr] = b_1
    let output_ptr = output_ptr + 1
    return ()
end

```
The `programStart` and the `JumpPointN` labels are required to work around the restriction, that 
absolut `call` instructions require the name of a label and do not accept `felt` as an argument.
The current strategy computes the relative jump from the `JumpPoint`s.  