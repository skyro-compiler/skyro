# Optimisations

The optimisations are seperated in small individual phases which work together to produce
an optimized result. Individual phases on their own may produce code that require another
phase to be usable. The following Optimisations exist.

## Untupling
Untuppling analyses functions and identifies functions which construct composite values and
then return them. If all the returns have the same structure then the construction of the 
composite value can be done by the caller instead of the calee. This has the advantage that
other optimisations may now be able to eliminate the whole construction and access the
fields directly. This Optimisations leverages Cairo's multi return capability. Closures
need special treatment for this to be save which is described later. The process consist of
the following steps.

### Candidate identification
The analysis inspects `RETURN`, `CALL` and `MKCON` opcodes and inferes if and what kind of
composite value is returned. CALLs do use the result of the Called function when doing so.
Because the called function may not be analysed yet the process is repeated multiple times,
using the result from the previous pass for the next until nothing changes anymore. At the
beginning it is unknown if a composite value can be returned for all functions then we 
detect values that are composite and others which are not. We can mark a value that was
previously marked as a composite value as no longer beeing a composite value. However, we 
can never mark a return as a composite value which was previously marked as non-composite
value to ensure termination of the algorithm. It has to be noted that the analysis is
faster and produce better results if the definitions are processed in topological order.
However, the untupling does not sort the definitions, and this should be done by another 
phase.

A function can return a composite value if all returned values have the same structure.
Meaning the have the same tag and the same number of fields and the fields have the same 
structure. If they differ in size or tag, then untupling can not be done. However, it is
possible to untupple only parts of the return. For example if one return returns a 
composite value with two fields, each composite values themself and anonther return returns
a composite value with two fields where none of the fields are composite values then the
top level composite value can still be untuppled.

At the end of this step it is known which functions can be untupled.

### Return Untuppling
The next step is to replace each `RETURN` opcode in the identified functions with a
multi-return. First `PROJECT` opcodes are injected right before the `RETURN` to deconstruct
the composite values and gain access to the fields. Second the `RETURN` is replaced with a
`RETURN` that returns the extracted fields instead of the composite value.

This often leads to code that construct values, then deconstruct it and then returns the 
fields. This is less efficient then the original. However, the remaining phases can 
eliminate this overhead if possible. By doing it this way this step is simple to implement
and does not need to distinguish different special cases but can reuse functionality
present in other optimizers to achieve the same result.

### Call Retupling
The last regular step is to replace `CALL` opcode to an untupled function with a 
multi-return `CALL` opcode. First each `CALL` is adapted to return the extracted fields
instead of the composite value. Second `MKCON` opcodes are introduced to reconstruct the
original composite value.

This often leads to code that construct values, then deconstruct it. However, similar to
the result of the untuplling step other optimizers can eliminate this overhead.

### Handling Externals
External functions can not be analyzed in step 1, because their code is not available in an 
analyzable form. Instead the untupling process can be parameterized by defining which 
external function returns their result in untupled form and how to retuple them. Only the
retupling step has to be done for these.

For external primitives on the other hand, their code is generated during code gen and
we know if they can return their result in untupled form. For these where this is possible
code gen implements a untupled and a tupled implementation and if the untupling phase
is active the untupled is used, otherwise the tupled is used.

### Handling Closures
Closures constitute dynamic calls and thus on an `APPLY` the target is not known and thus
it is not known if a retupling is needed or not. This is fixed in two steps. First for 
functions that are never used as target of a `CALL` opcode and only ever are used in a
`MKCLOSURE` we skipp the untupling all together. Second, for functions used as both we introduce
a wrapper function that calls the untupled function and then retuples the result and
returns the retupled value. All `MKCLOSURE` then are rewired to use this wrapper function
instead of the original one. This introduces overhead for closures. However, `APPLY` does
already perform worse then `CALL` and should be eliminated where possible. Further, if 
inlining is implemented then the wrapper can inline the original function to eliminate this
overhead.

## Constant Folding
Constant folding is an optimization usefull on its own. However, its main purpose is to 
clean up or leverage the result of optimisations like untupling and inlining (if we do it)
Constant Folding does collect information about static properties of values stored in
registers and based on that replaces opcodes with different more efficient ones. The most
basic operation from which the technic gets its name is to replace operations where all
inputs are known with the result. For example: 'a = 3 + 7' becomes 'a = 10'. However, it
currently only optimises the 'OP' opcode this way and not yet the `CALL` and `EXTPRIM` 
opcodes, as these requires an interpreter (for `CALL`) or an implementation of externals
in idris2 (for 'EXTPRIM'). Besides this the constant folding does further oprimisation
based on static information:

### Input Selection
For each opcode where the inputs are available in multiple registers it replaces the 
input register with the earliest assigned one. for example: If an opcode uses the
result of a chain of `ASSIGN` opcodes alla 'b = a ; c = b; d = c + b' then 'd = c + b'
is replaced with 'd = a + a'. In addition to `ASSIGN` this can handle `MKCON` and
`PROJECT` as well. For example in: 'a = construct (name:b,age:c) ; d = a.age; e = d + 1'
the 'e = d + 1' is replaced with 'e = c + 1'.

In the end this can leave a lot of opcodes that assign to no longer used registers.
However, constant folding does not eliminate them but delegates this task to a dead code
optimisation.

### Error Propagation
The `ERROR` operation is special in the regard that it never succeeds as it represents an
unrecoverable error. Meaning that the register holding the result of `ERROR` will never be
assigned, at least not by any `ERROR` operation. Thus an opcode use of a register only 
assignable by an error is never reachable and can safely be replaced by the error making
intermediary computations eligible for elimination (delegated to dead code optimisation).
For example in 'a = error ; b = a + 1' then 'b = a + 1' is replaced with 'b = error'.

### Apply Elimination
The `MKCLOSURE` and `APPLY` error are important for representing functional languages.
However, they are less efficient then the `CALL` opcode, which is their static counterpart.
The main culprit is the `APPLY` opcode which needs a helper method to be implemented.
If the target of a `APPLY` is statically known it can be transformed into a `MKCLOSURE` or
`CALL` opcode. For example in 'a = closure#test(1,2); b = a(3)' where 'test' has 3 
arguments total represent missing arguments 'b = apply#a(3)' can be replaced with 
'b = call#test(1,2,3)'. If test would have had 4 arguments the replacement would be
'b = closure#test(1,2,3)'. This can often eliminate closures completely, especially in 
junction with inlining higher order functions (not implemented yet)

### Case Elimination
The `CONCASE` and `CONSTCASE` opcodes conditionally execute code depending on the value of
either a tag from a composite value or a constant. If static information shows that the
the tag or the constant value is limited to a subset of values then the some branches can
be eliminated. In some cases this leaves only one branch and in that case the code
generator is able to inline that branch, eliminating the whole construct.

## Dead Code Elimination
Local optimizations often result in code that is no longer needed. Dead code elimination
detects no longer needed instructions and eliminates them. This is approached in two steps.
In the first step all the registers are collected that are needed to compute the return 
value. In the second step all opcodes that do not assign to at least one live register
are eliminated.
