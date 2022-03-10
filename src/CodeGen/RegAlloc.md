TODO: Update description


# Register Allocator
This file describes the register allocation algorithm

## Overview
Cairo has 5 ways of allocating registers.
- Locals: Allocated in the functions frame and accessed over fp. These are accessible in the whole function
- Params: Like locals, but placed by the caller not the calee
- Tempvar: A variable placed on the "stack" that can be accessed over ap.  These are only accessible as long as the ap can be statically tracked
- Let: Like tempvars, however the cairo compiler decides when to manifest them as tempvars. Which currently is right before each use. 
- Consts: Like let, however they are placed in code as immediate values where possible. Their content has to be known at compiletime 

The goal is to have as many consts as possible, as these use the least number of computation steps to allocate and use. However, most of the data is not statically known and thus this is often not possible.
After consts the lets are the preferred variant, as the cairo compiler already does some optimisations in their placing which prevents unnecessary copies in many cases. But, sadly the cairo compiler manifests them multiple times if they are used multiple times.
If a register is used multiple times on the same execution path tempvars are prefered to lets. 
In the case that the ap is not statically trackable between assignment and a local is used.

Locals are reused between branches. If two register are never used simultaneously in the same run of a function they can share the same local definition.
Further, cairo supports multiple returns, which is not present in Idris 2 which uses records instead (often tuples). Instead of placing them into memory on the calee's side and unpacking them into registers on the caller's side they can be directly passed over the multiple return.
Returns from functions are automatically assigned to tempvars in cairo (even if the let keyword is used).

## Assumptions
This register allocator assumes that the cairo compiler is free to manifest let values and consts on ap whenever it wants.
Code that rely on a certain order of ap allocated values has to manifest them beforehand if they are lets.

## Phases
The allocator works in 4 Phases. However, the last one is integrated into the code generation.
The phases are described conceptually only, the details are given in each optimisation.

### Phase 1: UseDef Collection
In this phase the code of a function is analysed and for each register in the CairoCode it is collected where the register is assigned and where it is used.

### Phase 2: Building Usage Tree
From the results of Phase 1 a tree is build representing the program structure (Blocks and Branches).
Each register is placed in the lowest possible element that still contains all the registers assignments and uses.

### Phase 3: Allocation
Based on the information collected and prepared in the previous two phases it is decided how and where to allocate that register.

### Phase 4: Code Gen
During code generation register assignments and definitions are placed according to the results of the previous phase.

## Optimisations

### Ap Allocations (Assigning to Let/Tempvar)
To find out which registers can become let, tempvar or consts we split the code of the functions into ap regions.
An ap region contains all instructions where it is possible to statically compute the change in ap between each pair.
To achieve this we process instructions sequentially (in Phase 1) and whenever an instruction is encountered that may modify ap in a statically unknown manner we start a new ap region.
The only instructions that can trigger a new ap region are: `APPLY`, `CALL`, `EXTPRIM`, `CASE`, `CONSTCASE`. 
In case of `CALL` and `EXTPRIM` depending on the targeted function or primitive it does not trigger a new ap region.
This is the case if the targeted function or primitive's body consist of a single ap region.
`CASE` and `CONSTCASE` are special as well, because when entering each branch of it the ap region does not change, only when leaving a branch the ap region changes.
The structure of the VMCode already ensures that no register is assigned in one branch and then used in another of the same case instruction and thus this is safe.

When in Phase 1 a register is encountered the ap region is stored in the corresponding UseDef entry.
After a function is processed we check if it used only one ap region and if so we record it in a map used to decide if `CALL`'s for that function need an ap region switch.
This assumes that functions are processed in dependency order. Which Idris 2 does, except for mutual recursive functions. However, recursive functions must always trigger an ap region change.

This Optimisation does nothing in Phase 2. In Phase 3 it is checked for each register if all UseDef entries are in the same ap region and if so it is marked as let or tempvar.
To make the distinction it is checked if all uses are on seperate execution paths. If a register is used twice on the same execution path it is markes as tempvar and otherwise as let.

During Phase 4 the corresponding registers are defined as whatever Phase 3 marked with one exception.
If the value is statically known a const is used instead. Further, if the register is written in a hint a tempvar is used, as lets can not be defined in hints.

### Const Allocation
When in Phase 1 a `MKCONSTANT` instruction is detected we record the constant value in the Def entry.

In Phase 3 when we encounter a register marked as let or tempvar where all defs have the same constant value. We mark the register as constant.

In Phase 4 `MKCONSTANT` instruction that are marked constant are omitted. The other are introduced over the `const` keyword if they are let or temp marked.
When a marked constant is used, then the constant is directly inlined (supported by cairo)

### Local Sharing (Assigning to Local)
Everything not assigned let or tempvar is a local (or param).
To decide which registers can share a local the code block is recorded for each UseDef entry.
The function body forms a code block and each branch of each `CASE` and `CONSTCASE` instruction forms a code block.
A code block is identified through its path from the root.
For example the 2nd branch of the 3rd case instruction in the root block has the identifier: `/3/2` where the first `/` identifies the root block, `3` identifies the third case and `2` the second branch.

In Phase 1 the current block path is tracked and recorded in the UseDef entry whenever a register is encountered.

In Phase 2 each register is placed in the tree at the lowest node which contains all UseDefs. The tree contains a node for each Block and for each case instruction.
To place a register in the tree the common prefix over all the paths recorded in its UseDef entries is taken.
The result identifies the block or case instruction where to record the register.

In Phase 3 each register that is not marked as let or tempvar gets marked as local and gets a number.
Registers with the same number will share a local. 
This is done by traversing the tree and sequentially assigne numbers. However when encountering a case node we can use the same numbers in each branch.
This is achieved by resetting the counter used to assign number after each branch to the value it had before the first branch and after the last branch the counter is set to the maximum it had at the end of any branch.

In Phase 4 a local is defined in the top scope for each number aasigned to registers.
And whenever a register is encountered the corresponding local is used.
One exceptions are function returns which initially are always defined as tempvars.
If a function return is marked as local it is copied to the corresponding local.

### Returned Record Inlining (Using Cairo's multireturn)

