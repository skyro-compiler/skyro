module Main

import Test.Golden

%default covering

-- To add more tests, copy one of the test directories, then update this list
examples : TestPool
examples = 
  MkTestPool "Examples: Idris -> Cairo -> Output" 
    [] Default
    [ "test001", "test002", "test003", "test004", "test005",
      "test006", "test007", "test008", "test009", "test010",
      "test011", "test012", "test013", "test014", "test015"]

primitiveTests : TestPool
primitiveTests = MkTestPool "'Tests' Primops" 
    [] Default
    [ "felt", "uint", "int"]

main : IO ()
main = runner
  [ testPaths "idrisToCairo/examples" examples,
    testPaths "idrisToCairo/primitives" primitiveTests
  ] where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
