module Main
import Starknet
%language ElabReflection

errorIfNot42 : External m => (number : Felt) -> m Felt
errorIfNot42 n = if n /= 42
    then assert_total $ idris_crash "Not 42!"
    else pure (1)

main = abi
  {functions = ["errorIfNot42"]}
