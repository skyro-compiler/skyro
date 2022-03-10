module Main
-- Run a single test
-- > make test only=test013
import Cairo

example : Felt -> Cairo Felt
example n = dict 0 (\d => 
  let d1 = dwrite d 1 2
      d2 = dwrite d1 2 n
      d3 = dwrite d2 3 4
  in dread d3 2)


{- 
Error: While processing right hand side of non_example. Trying to use linear name inner in non-linear context.

non_example : Felt -> Felt
non_example n = 
  dict 0 (\outer => 
    let inner' = dict 1 (\inner => (outer, inner))
     in (inner', n)
  )
-}   

pureDictComp : (1 d : LinDict) -> (LinDict, Felt)
pureDictComp d = 
  let d1 = dwrite d 1 2
      d2 = dwrite d1 2 3
      d3 = dwrite d2 3 4
  in dread d3 5

%noinline
main : Cairo ()
main = do
    result1 <- example 42
    output result1
    result2 <- dict 8 pureDictComp 
    output result2 -- returns default 8
    -- output $ non_example 42
