module MainIR

import Core.Context
import CairoCode.CairoCodeSerializer
import CairoCode.CairoCodeParser
import CommonDef
import Data.Maybe

import Main
import System
import System.File
import System.Path

Checked : Bool -> Type -> Type
Checked False a = Maybe a
Checked True  a = a

record Options (a : Bool) where
  constructor MkOptions
  target     : Checked a TargetType
  inputFile  : Checked a String
  outputFile : Checked a String
  verbose : Bool

printHelp : IO a
printHelp = do
  putStrLn "Usage:"
  putStrLn "skyroToCairo --help"
  putStrLn "skyroToCairo [--starknet] [-v | --verbose] {-i | --input} inputfile {-o | --output} outputfile"
  putStrLn ""
  exitWith $ ExitFailure 1

consumeArgs : (Options False) -> List String -> IO (Options False)
consumeArgs opts [] = pure opts
consumeArgs opts ("--starknet"             :: xs) = consumeArgs ({ target     := Just StarkNet } opts) xs
consumeArgs opts ("-v"                     :: xs) = consumeArgs ({ verbose    := True          } opts) xs
consumeArgs opts ("--verbose"              :: xs) = consumeArgs ({ verbose    := True          } opts) xs
consumeArgs opts ("-i"         :: fileName :: xs) = consumeArgs ({ inputFile  := Just fileName } opts) xs
consumeArgs opts ("--input"    :: fileName :: xs) = consumeArgs ({ inputFile  := Just fileName } opts) xs
consumeArgs opts ("-o"         :: fileName :: xs) = consumeArgs ({ outputFile := Just fileName } opts) xs
consumeArgs opts ("--output"   :: fileName :: xs) = consumeArgs ({ outputFile := Just fileName } opts) xs
consumeArgs opts _ = printHelp

parseArgs : IO (Options True)
parseArgs = do
  let defaultOptions = MkOptions {a=False} (Just Cairo) Nothing Nothing False

  args <- getArgs
  case args of
    [] => do
      putStrLn "You managed to pass 0 arguments somehow."
      printHelp
    [_] => do
      printHelp
    (_ :: args) => do
      finalOptions <- consumeArgs defaultOptions args
      case (finalOptions.inputFile, finalOptions.outputFile) of
        (Nothing, _) => printHelp
        (_, Nothing) => printHelp
        (Just input, Just output) => do
          pure $ MkOptions {a=True} (fromMaybe Cairo finalOptions.target) input output finalOptions.verbose
      

main : IO ()
main = do
  MkOptions target input output verbose <- parseArgs
  putStrLn ""
  putStrLn $ "Compiling Skyro in \{case target of Cairo => "Cairo"; _ => "Starknet"} mode"
  putStrLn $ "Input file: \{input}, Output file \{output}, Verbosity: \{show verbose}"
  putStrLn ""
  
  Right fileContents <- readFile input
    | Left err => putStrLn "Error reading input file \{input}: \{show err}"

  Right program <- pure $ parseSkyro fileContents
    | Left errs => do
      putStrLn "Could not parse input program:"
      putStrLn errs
      exitWith $ ExitFailure 1

  let (phaseFolder, actualVerbose) = case parent output of
        Just dir => (dir </> ".phases", verbose)
        Nothing => (output </> ".phases", False)
  
  when (actualVerbose /= verbose) $ putStrLn "Parent directory of output file not found - cannot print Phases. \ESC[1;31mForcibly switching off verbose mode.\ESC[0m"

  finalProgram <- compileIR target program actualVerbose phaseFolder

  Right () <- writeFile output finalProgram
    | Left err => do
      putStrLn "Could not write the output file:"
      printLn err
  
  putStrLn "Compilation complete!"
