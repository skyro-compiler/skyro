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
