# Skyro 🦜
Welcome to the home of the Skyro compiler!

Skyro compiles programs written in [Idris2](https://github.com/idris-lang/Idris2) to [Cairo](https://www.cairo-lang.org/) and thereby enables high-level, pure functional programming for [verifiable computation](https://en.wikipedia.org/wiki/Verifiable_computing). Skyro also supports [StarkNet](https://starknet.io/) contract programming ([see below](#starknet)).

We strongly believe that Cairo as a technology could have a big impact on society (trust in math, not companies and not governments) and we think that typed, pure functional programming is currently the best way to write programs in general.

⚠️ Disclaimer: This is experimental software and there will be bugs! Use at your own risk!

## High-level, typed functional programming
Idris2 is a state of the art functional programming language. It supports algebraic data types, pattern matching, higher order functions, an extraordinary expressive type system and much more ([check their documentation](https://idris2.readthedocs.io/en/latest/tutorial/index.html)).

Here is a short example showing the basics:
```haskell
-- Import the Cairo prelude
import Cairo
import Data.List

-- Define a datatype
record Account where
  constructor MkAccount
  number: Felt 
  balance: Felt

-- Read from private input (using inline Cairo)
%foreign 
  """
  code:
  func Main_readFromInput(key) -> (result):
      tempvar result
      %{  
          from starkware.cairo.common.math_utils import as_int
          val = program_input[ids.key]
          ids.result = as_int(val, PRIME) % PRIME
      %}
      return (result)
  end
  """
readFromInput : Felt -> Felt

-- Creates an account based on an index into the JSON array in `input.json`
createAccount : Felt -> Account
createAccount index = MkAccount number balance
  where number : Felt
        number = readFromInput index
        balance : Felt
        balance = readFromInput (index + 1) 

-- List of available accounts (we assume there are 3 accounts)
privateAccounts : List Account
privateAccounts = map createAccount [0,2,4] 

-- Define a function which gets a list of accounts and returns the sum of their balances
sumOfBalances : List Account -> Felt
sumOfBalances accounts = sum (map balance accounts)

-- Computes the hash of the account data (no need to pass the pedersen_ptr)
hashOfAccountData : List Account -> Felt
hashOfAccountData accounts = foldl pedersenHash 3 (foldMap (\a => [a.number, a.balance]) accounts)

-- The main entry point:
-- Computes and outputs the hash of the account data
-- together with the sum of the balances
main : Cairo ()
main = do
  output $ hashOfAccountData privateAccounts
  output $ sumOfBalances privateAccounts
```

The above example can be found in [example-cairo/Example.idr](example-cairo/Example.idr). Just run the co-located [run.sh](example-cairo/run.sh) script. It compiles `Example.idr` to the corresponding `Example.cairo` and executes it. (The `run.sh` script requires a [native platform build](#native-platform-build) of the compiler in this repository.)
```
> ./run.sh
Program output:
  -921563739618134302503453243076189111596859429415631340131891813586074046706
  300
```

The generated Cairo program can then be found in [example-cairo/build/exec/Example.cairo](example-cairo/build/exec/Example.cairo) and can be executed in the [Cairo playground](https://www.cairo-lang.org/playground/) like any other Cairo program.


## Features
### Compiles most of Idris2 to Cairo
Cairo programms can now be written with full scale dependent types in Idris2!
Check [whats missing](#whats-missing--limitations) to get a list of things that are currently not supported.
`IO` programs (like reading a file) can not be compiled (and never will) because there is no way to execute `IO` actions in Cairo.

### Register allocator
Are you confused by `let` and `local` and revoked references? Skyro automatically chooses the most efficient type of variable so you don't need to.

### Implicit injection: 
Implicits are tracked and injected automatically, no need for manual handling of revoked implicits.

### Foreign Function Interface (FFI)
FFI is the mechanism to call functions written in Cairo from Idris2. See [test011/Main.idr](tests/idrisToCairo/examples/test011/Main.idr) as an example.

## StarkNet
StarkNet contract programming is now supported!
Here is an example:

```haskell
module Main
import Starknet
%language ElabReflection

-- Event with zero additional keys and two values of type Felt.
balanceChanged : EventDesc [] [Felt, Felt]

-- Storage variable with one key of type Felt storing a value of type Felt.
balance : StorageSpace [Felt] Felt

-- View function
getBalance : View m => (addr: Felt) ->  m Felt
getBalance addr = readStorageVar (balance `at` addr)

-- External function
changeBalance : External m => (difference: Felt) -> m Unit
changeBalance difference = do 
  callerAddr <- getCallerAddress
  bal <- getBalance callerAddr
  let newBal = bal + difference
  writeStorageVar (balance `at` callerAddr) newBal
  emitEvent ((balanceChanged `applyValue` callerAddr) `applyValue` newBal)

main = abi 
  {functions   = ["getBalance", "changeBalance"]} 
  {storageVars = ["balance"]} 
  {events      = ["balanceChanged"]}
```

The above example can be found in [example-starknet/Example.idr](example-starknet/Example.idr). Just run the co-located [run.sh](example-starknet/run.sh) script. It compiles `Example.idr` to the corresponding `Example.cairo` contract and runs [example-starknet/contract_test.py](example-starknet/contract_test.py) locally. (The `run.sh` script requires a [native platform build](#native-platform-build) of the compiler in this repository.)
```
> ./run.sh
============================= test session starts ==============================
collected 1 item

contract_test.py .                                                       [100%]
```

### Features:
- Support for `Constructor`, `L1Handler`, `External` and `View` functions. `External` functions are allowed to call `View` functions, but not vice versa. This is ensured by the typesystem.
- Most `syscall` operations are [available](cairolib/Starknet/Types.idr).
- Support for events with multiple keys and multiple values.
- Support for storage variables.
- Expressive datatypes (records and variants) are supported in the interface (parameter and return types of functions, keys and values of events and storage variables).


## What's missing / limitations
- Primitive types and operations:
  - `String` and `Char` are not yet supported. 
  - Patternmatching on `Felt` emits a warning and does not work.
  - `Felt` is a field element and by definition has no defined `Ord`ering.
  - `Felt` does not have bitwise operations (because Cairo bitwise builtin is not defined over the whole range of Felt).
- Standard library:
  - Currently we expose the whole Idris2 prelude (except `IO`), this needs to be refined.
  - Most cairo specific functionality is currently offered in a primitive form although Idris2 would allow the definition of very elegant and typesafe abstractions and APIs. These need to be worked out.
- StarkNet:
  - Cross contract / library calls are possible using raw syscall functions. A much more convenient and typesafe interface mechanism should be provided.
  - Operations on numeric types other then `Felt` (e.g. `Int32`, `Integer`) use hints in their implementation but are not whitelisted. They won't work on StarkNet.
  - The generated code uses `@raw_input`, `@raw_output`, therefore the generated ABI appears unstructured. This needs improvement.
- Testing: 
  - Currently there are mainly small program examples in the [tests](/tests/) directory.
  - Much more automated testing is required!
- Documentation:
  - Skyro needs an onboarding tutorial.
  - More documentation about the implementation is also required.

## Contribution
If you find a problem we are happy if you would open an issue with a small example.
We are also happy to take pull requests!

## Questions and Answers

#### Q: Why did you choose Idris2 and not for example Python?
A: The target platform Cairo has a _write once memory_ (immutable memory) which is a great fit for purely functional languages (which we prefer anyways when it comes to programs which should be correct).

#### Q: Why did you choose Idris2 and not Haskell?
A: There are mutliple reasons:
- Idris2 uses by-value evaluation which is simpler to map to Cairo than Haskell's lazy evaluation.
- Idris2 is designed for pluggable custom backend integration.
- The Idris2 compiler is much smaller than GHC and thus simpler to understand and it takes less time to build it.
- Idris2's quantitative type system [QTT](https://arxiv.org/abs/2104.00480) allows for safe and elegant APIs (see Dict as an example).
  
#### Q: Are you willing to work for my crypto startup?
A: We are currently happy with our jobs at the university and we are always looking for research collaboration on interesting topics.


## Repository Structure
```
.
├── cairolib                   Standard library (prelude)
│   ├── Cairo                  Cairo specific parts
│   ├── Common                 Common parts for Cairo and Starknet
│   └── Starknet               Starknet specific parts
├── example-cairo              Cairo example    
├── example-starknet           Starknet example
├── skyro-runtime              Runtime library 
├── src                        Compiler source directory
│   ├── ABI                    Definition of the application binary interface
│   ├── CairoCode              Definition of the intermediate representation (IR)
│   ├── CodeGen                Code generator (turning IR to Cairo source code)
│   ├── Optimisation           Optimization passes
│   ├── Primitives             Support for primitive types
│   ├── RewriteRules           Simple rewrite rules
│   └── Utils                  General functionality which is used in different places
└── tests                      Tests root directory
    └── idrisToCairo           Tests and examples for the compiler
        ├── examples           Tests compilation on different examples
        └── primitives         Tests for the primitive types in Idris2

```


# Build Instructions

The compiler can be built directly on the [target platform](#native-platform-build) as well as [within docker](#docker-build).
If you just want to use the compiler, we recommend to follow [these instructions](#using-the-compiler-from-within-docker).

## Native platform build

### Install the Cairo environment
Follow the instructions [here](https://cairo-lang.org/docs/quickstart.html).

### Checkout and build the Idris2 compiler
Tested with version 9e92e7ded05741aa7d030f815c0441867b77ad0b
```
> git clone https://github.com/idris-lang/Idris2.git
> cd Idris2
> git checkout 9e92e7ded05741aa7d030f815c0441867b77ad0b
> make bootstrap SCHEME=chez
> make install && make clean
> make all && make install && make install-api
```
The `chez` in `SCHEME=chez` is the name of the [chez](https://github.com/cisco/chezscheme) binary. On Ubuntu it is `chezscheme9.5` and on WSL it could be `scheme`.

### Build Skyro
The following command builds the Skyro compiler, the required libraries and runs the tests:
```
> make test
```

### Run the compiler
Compile an Idris2 program to to Cairo:
```
> ./build/exec/idrisToCairo --no-prelude -p cairolib --cg cairo Example.idr -o Example.cairo
```
Argument description:
 - `--no-prelude` do not automatically import the Idris2 standard prelude (standard library)
 - `-p cairolib` make our Cairo library available
 - `--cg cairo` use the Cairo code generator
 - `Example.idr` the Idris2 program to compile
 - `-o Example.cairo` the resulting Cairo program (default location ./build/exec/Exanple.cairo)

To compile a StarkNet contract, add `--directive starknet`.

Compile Cairo to AIR and execute AIR:

```
> export SKYRORUNTIME="../skyro-runtime" 
> export PYTHONPATH="${PYTHONPATH}:${SKYRORUNTIME}"
> cairo-compile --cairo_path ${SKYRORUNTIME} ./build/exec/Example.cairo --output ./build/exec/Example_compile.json && 
  cairo-run --program=./build/exec/Example_compile.json --print_output --print_info --layout=small
```

`SKYRORUNTIME` must point to the [skyro-runtime/](skyro-rumtime/) directory. This ensures that `cairo-compile` finds required dependencies on its `--cairo_path`. `PYTHONPATH` must be extended because `cairo-run` potentially runs hints which import python helpers from the skyro-runtime.  

Format the cairo code (not required):
```
> cairo-format ./build/exec/Example.cairo > FormattedExample.cairo
```

## Docker build
The [Dockerfile](./Dockerfile) defines two stages: 
 - Stage `environment` builds the image which contains all build dependencies.
 - Stage `compiler` builds the image with the skyro compiler included on top of the `environment` stage.

If you only want to [use the compiler](#using-the-compiler-from-within-docker), we suggest to build the `compiler` stage and use it.
If you want to [hack on the compiler](#hack-on-the-compiler-source), we suggest to build the `environment` stage and use it to build the compiler.

You may need to increase the available memory in your docker settings.

## Using the compiler from within docker
### Build
To build the compiler within a docker image, execute the following command:
```
> docker build --platform linux/amd64 . -t skyro
```

### Usage
To run the compiler within docker, put your source into the `docker-compile` folder (e.g. `docker-compile/Example.idr`) and run the following command:

Linux / macOS:
```
> docker run --rm -it --platform linux/amd64 -v $(pwd)/docker-compile:/app/docker-compile skyro idrisToCairo --no-prelude -p cairolib /app/docker-compile/Example.idr -o /app/docker-compile/Example.cairo
```

Windows:
```
docker run --rm -it -v %cd%/docker-compile:/app/docker-compile skyro idrisToCairo --no-prelude -p cairolib /app/docker-compile/Example.idr -o /app/docker-compile/Example.cairo
```

## Hack on the compiler source

### Build the docker image
The following command create a docker image containing all prerequisits for building the compiler:
```
> docker build --target environment --platform linux/amd64 . -t skyro
```

- `--target environment` only builds the `environment` stage
- `--platform linux/amd64` is required on Apple M1 hardware because `chezscheme` is not available on arm.

### Build the compiler
The following commands map the root directory of this projet into docker and starts the build:

Linux / macOS:
```
> docker run --platform linux/amd64 -v $(pwd):/app/ skyro /app/docker-bin/skyro-build.sh 
```
Windows:
```
> docker run -v %cd%:/app/ skyro /app/docker-bin/skyro-build.sh
```

### Run tests
Linux / macOS:
```
> docker run --platform linux/amd64 -v $(pwd):/app/ skyro-env /app/docker-bin/skyro-test.sh
```
Windows:
```
> docker run -v %cd%:/app/ skyro /app/docker-bin/skyro-test.sh
```

### Clean build artifacts
Linux / macOS:
```
> docker run --platform linux/amd64 -v $(pwd):/app/ skyro-env /app/docker-bin/skyro-clean.sh
```
Windows:
```
> docker run -v %cd%:/app/ skyro /app/docker-bin/skyro-clean.sh
```

# Credits
Skyro is developed at the [University of Applied Sciences and Arts Northwestern Switzerland (FHNW)](https://www.fhnw.ch/en/about-fhnw/schools/school-of-engineering/institutes/institute-of-mobile-and-distributed-systems) 



<img src="https://www.fhnw.ch/en/++theme++web16theme/assets/media/img/university-applied-sciences-arts-northwestern-switzerland-fhnw-logo.svg" alt="FHNW logo" height="50"/>

<br>

This project is sponsored by [StarkWare](https://starkware.co/):

<img src="https://starkware.co/wp-content/uploads/2021/04/logotype.svg" alt="StarkWare logo" height="50"/>

<br>

and the Switzerland based [Hasler Foundation](https://haslerstiftung.ch/en/the-hasler-foundation/): 

<img src="https://haslerstiftung.ch/wp-content/uploads/2018/07/cropped-Hasler_Logo_Horizontal.png" alt="Hasler logo" height="40"/>


Thank you both for your generous support in this project!

Also many thanks for the kind support from the talented people of the [Idris2](https://github.com/idris-lang/Idris2) community - their compiler is the foundation of this work.
