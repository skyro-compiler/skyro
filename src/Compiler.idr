module Compiler

import System
import System.Clock
import System.File
import System.Directory
import Libraries.Utils.Path

import CairoCode.Name
import Data.List
import Data.List1
import Data.String
import Data.Vect
import Data.Either
import Data.SortedSet
import Data.SortedMap
import CommonDef
import CairoCode.CairoCode
import CairoCode.CairoCodeSerializer
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
import CairoCode.Checker
import CodeGen.CodeGen
import CodeGen.CurryingBasedClosures

import CodeGen.RegAllocator
import Optimisation.DeadCodeElimination
import Optimisation.DeadArgumentEliminator
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.GlobalStaticOptimizer
import Optimisation.Inliner
import Optimisation.Specialiser
import Optimisation.OrderAndEliminateDefinitions
import Optimisation.DataFlowOptimizer

import Optimisation.Untupling
import CodeGen.InjectLinearImplicits
import RewriteRules.EqChainInline
import RewriteRules.TailBranchFolder
import RewriteRules.ApplyShift
import Primitives.Primitives
import CodeGen.RegAllocator

import Debug.Trace

import ABI.Definitions
import ABI.Generator

generateMainCall : CairoDef -> CairoReg -> CairoReg -> List CairoInst
generateMainCall (FunDef [_] _ [_] _) resReg stateReg = [CALL [resReg] empty cairo_main [stateReg]]
generateMainCall (FunDef Nil _ [_] _) resReg stateReg = [CALL [reg 0] empty cairo_main [], APPLY resReg empty (reg 0) stateReg]
    where reg : Int -> CairoReg
          reg i = Unassigned (Just "main_call") i 0
generateMainCall _ _ _ = assert_total $ idris_crash "Unsupported Main signature"

genericEntryDef : LinearImplicit -> CairoDef -> (CairoName, CairoDef)
genericEntryDef io_implicit main_def = (entry_name, ExtFunDef [] [] (singleton io_implicit io_ptr_reg) [] body)
    where
          io_ptr_reg : CairoReg
          io_ptr_reg = implicitReg io_implicit
          reg : Int -> CairoReg
          reg i = Unassigned (Just "main") i 0
          body : List CairoInst
          {- Version without new type optimisation
          body = ((MKCON (reg 0) Nothing [io_ptr_reg])::(generateMainCall main_def (reg 1) (reg 0))) ++ [
              (PROJECT (reg 2) (reg 1) 0),
              (PROJECT (reg 3) (reg 2) 0),
              (RETURN [] (singleton io_implicit (reg 3)))
            ]
          -}
          -- new type optimized version (because Cairo Monad has only 1 field at the moment (output_ptr)
          body = (generateMainCall main_def (reg 0) (io_ptr_reg)) ++ [
            (PROJECT (reg 1) (reg 0) 0),
            (RETURN [] (singleton io_implicit (reg 1)))
          ]

-- Note: we treat output_ptr as implicit only to ensure that the parameter order and names ends up correctly
--       This is ok as this is the entry point (which has a fixed signature) and no one has to provide output_ptr implicitly
entryDef : CairoDef -> (CairoName, CairoDef)
entryDef = genericEntryDef output_builtin

entryDefStarknet : CairoDef -> (CairoName, CairoDef)
entryDefStarknet = genericEntryDef syscall_builtin

-- Debuging helper Phases
trace_code_selective : ((CairoName, CairoDef) -> Bool) -> CairoCodePass
trace_code_selective fn cairocode = trace (show (filter fn cairocode)) cairocode

trace_code : CairoCodePass
trace_code = trace_code_selective (\_ => True)

check_def_integrity : CairoCodePass
check_def_integrity = integrityCheckDefs

-- Compilation Phases
eliminate_unused_and_order_topological : CairoCodePass
eliminate_unused_and_order_topological = orderUsedDefs

eq_chain_inline : CairoCodePass
eq_chain_inline = eqChainInline

tail_branch_inline : CairoCodePass
tail_branch_inline = tailBranch

tupled_returns : CairoCodePass
tupled_returns = untupling

implicit_injection : CairoCodePass
implicit_injection = injectLinearImplicitsDefs

constant_folding : CairoCodePass
constant_folding = localStaticOptimizeDefs

dead_code_eliminator : CairoCodePass
dead_code_eliminator = map eliminateDeadCode

dead_data_eliminator : CairoCodePass
dead_data_eliminator = deadDataEliminator

data CleanupMode = Full | Partial | Essential

cleanup : CleanupMode -> CairoCodePass
cleanup Full cairocode = dead_code_eliminator $ constant_folding $ eliminate_unused_and_order_topological cairocode
cleanup Partial cairocode = dead_code_eliminator $ constant_folding cairocode
cleanup Essential cairocode = map orderUnassignedRegIndexes cairocode

global_constant_folding : CairoCodePass
global_constant_folding = globalStaticOptimize

aggressive_inlining : Maybe Nat -> Bool -> CairoCodePass
aggressive_inlining sizeLimit tailBranchingActive = inlineDefs sizeLimit tailBranchingActive

inlining_save : CairoCodePass
inlining_save = inlineSaveDefs False

apply_outlining : Bool -> CairoCodePass
apply_outlining tailBranchingActive = applyOutlining tailBranchingActive

aggressive_specialising : Maybe Nat -> Bool -> Nat -> CairoCodePass
aggressive_specialising inlineSizeLimit tailBranchingActive maxIters = specialiseAndInlineDefs inlineSizeLimit tailBranchingActive maxIters

dead_argument_eliminator : CairoCodePass
dead_argument_eliminator = eliminateDeadArgumentsDefs

closure_gen : CairoCodePass
closure_gen = preprocessClosures

allocate_registers : CairoCodePass
allocate_registers cairocode = reverse (snd (foldl allocateCairoDef (empty, []) cairocode))
     where allocateCairoDef : (SortedSet CairoName, List (CairoName, CairoDef)) -> (CairoName, CairoDef) -> (SortedSet CairoName, List (CairoName, CairoDef))
           allocateCairoDef (safeCalls, acc) (name, cairodef) = let (ncdef, newSafeCalls) = allocateCairoDefRegisters safeCalls (name, cairodef) in (newSafeCalls , (name,ncdef)::acc)

-- todo: change to infere entry_name(s) instead of giving down
generate_code : TargetType -> List (CairoName, CairoDef) -> String
generate_code targetType cairocode = generateCairoCode targetType cairocode


{-
debug : List (CairoName, CairoDef) -> List String
debug strs = strs >>= extract
    where extract : (CairoName, CairoDef) -> List String
          extract (name, ForeignDef (MkForeignInfo True _ _ _) _ _) = [cairoName name]
          extract _ = []
-}

printIrToFile : String -> String -> Nat -> List (CairoName, CairoDef) -> IO ()
printIrToFile irFolder phaseName phaseNo res = do
  let phaseNo' = if phaseNo < 10 then "0\{show phaseNo}" else show phaseNo
  let out = irFolder </> "\{phaseNo'}_\{phaseName}.skyro"
  let representation = serializeProgram res
  -- Makes sure directory exists, but doesn't check it's a directory and not a file (unlikely to occur)
  folderExists <- exists irFolder
  Right () <- the (IO (Either FileError ())) (if folderExists then pure (Right ()) else createDir irFolder)
    | Left err => printLn err -- (FileErr out err)
  Right () <- writeFile out representation
    | Left err => printLn err -- (FileErr out err)
  pure ()

executePhase : Bool -> String -> (List (CairoName, CairoDef), Nat) -> (String, CairoCodePass) -> IO (List (CairoName, CairoDef), Nat)
executePhase True irFolder (cairocode, phaseNo) (phaseName, phaseFunction) = do
    putStrLn $ "Running phase: " ++ phaseName
    start <- clockTime Monotonic
    let result = integrityCheckDefs $ phaseFunction cairocode
    end <- clockTime Monotonic
    let time = timeDifference end start
    putStrLn $ "Phase " ++ phaseName ++ " took "++(show time)++" to run"
    printIrToFile irFolder phaseName phaseNo result
    pure (result, phaseNo + 1)
executePhase False _ (cairocode, phaseNo) (phaseName, phaseFunction) = do
    let result = integrityCheckDefs $ phaseFunction cairocode
    pure (result, phaseNo + 1)



minimalViablePhases : List (String,CairoCodePass)
minimalViablePhases  = [
    -- Prepare Section & Initial Pass Section
    ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
    -- Untupling Section --
    ("tupled_returns", tupled_returns),
    ("partial_cleanup", cleanup Partial),
    -- Implicit Injection Section --
    ("implicit_injection", implicit_injection),
    ("essential_cleanup", cleanup Essential),
    ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
    -- Closure Gen Preparation Section --
    ("closure_gen", closure_gen),
    ("essential_cleanup", cleanup Essential),
    ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
    -- Register Allocation Section --
    ("allocate_registers", allocate_registers)
]

intermediaryCompilerPhases : List (String,CairoCodePass)
intermediaryCompilerPhases = [
        -- Prepare Section & Initial Pass Section
        ("initial_integrity_check", check_def_integrity),
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("global_constant_folding", global_constant_folding), -- includes a local constant folding pass
        ("dead_argument_eliminator", dead_argument_eliminator), -- includes a dead code elimination pass
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Common Pattern Rewrites Section --
        ("eq_chain_inline", eq_chain_inline),
        ("partial_cleanup", cleanup Partial),
        -- Inlining Section
        ("inlining", aggressive_inlining (Just 150) False),
        ("full_cleanup", cleanup Full),
        -- Monadic Expression Optimisation (their pattern should be visible by now)
        ("global_constant_folding", global_constant_folding), -- Make sure patterns are visible
        ("apply_outlining", apply_outlining False), -- despite the name does some inlining as well
        ("full_cleanup", cleanup Full),
        -- Post transform Optims & clean ups
        ("dead_argument_eliminator", dead_argument_eliminator), -- We have the final form now and can eliminate
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("full_cleanup", cleanup Full),
        -- From here on its mostly the necessary stuff
        -- Untupling Section --
        ("tupled_returns", tupled_returns),
        ("full_cleanup", cleanup Full),
        -- Implicit Injection Section --
        ("implicit_injection", implicit_injection),
        ("partial_cleanup", cleanup Partial),
        -- Closure Gen Preparation Section --
        ("closure_gen", closure_gen),
        ("essential_cleanup", cleanup Essential),
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Register Allocation Section --
        ("allocate_registers", allocate_registers)
    ]

standardCompilerPhases : List (String,CairoCodePass)
standardCompilerPhases = [
        -- Prepare Section & Initial Pass Section
        ("initial_integrity_check", check_def_integrity),
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("global_constant_folding", global_constant_folding), -- includes a local constant folding pass
        ("dead_argument_eliminator", dead_argument_eliminator), -- includes a dead code elimination pass
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Common Pattern Rewrites Section --
        ("eq_chain_inline", eq_chain_inline),
        ("partial_cleanup", cleanup Partial),
        -- Inlining Section
        ("inlining", aggressive_inlining (Just 300) False),
        ("full_cleanup", cleanup Full),
        -- Specialising
        ("specialising", aggressive_specialising (Just 300) False 1),
        ("full_cleanup", cleanup Full),
        -- Monadic Expression Optimisation (their pattern should be visible by now)
        ("global_constant_folding", global_constant_folding), -- Make sure patterns are visible
        ("apply_outlining", apply_outlining False), -- despite the name does some inlining as well
        ("full_cleanup", cleanup Full),
        -- Post transform Optims & clean ups
        ("dead_argument_eliminator", dead_argument_eliminator), -- We have the final form now and can eliminate
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("full_cleanup", cleanup Full),
        -- From here on its mostly the necessary stuff
        -- Untupling Section --
        ("tupled_returns", tupled_returns),
        ("full_cleanup", cleanup Full),
        -- Implicit Injection Section --
        ("implicit_injection", implicit_injection),
        ("partial_cleanup", cleanup Partial),
        -- Cleanup of final code
        ("eq_chain_inline", eq_chain_inline), -- seems not to help test016 still keeps the eqChain
        ("full_cleanup", cleanup Full),
        -- Closure Gen Preparation Section --
        ("closure_gen", closure_gen),
        ("essential_cleanup", cleanup Essential),
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Cleanup of closure code
        -- Todo: Current Closure model needs an additional argument that not visible in the MKClosue signature thus this is a bade idea
        -- ("inlining_save_", inlining_save), -- some closures can be inlined
        -- Register Allocation Section --
        ("allocate_registers", allocate_registers)
    ]

-- Todo: finding the right chain is hard
--  An optim would be have some sub sections that are repeated until nothing changes
--   Would need a highly efficent eq of List (CairoName, CairoDef)
--     1. Same length
--     2. Same names
--     3. Same function types & same argument return Regs
--     4. Same body length
--     5. Same Instructions (for case we can shortut: Same num branches, Same Branch Lengths, then Same Branches)
aggressiveCompilerPhases : List (String,CairoCodePass)
aggressiveCompilerPhases = [
        -- Prepare Section & Initial Pass Section
        ("initial_integrity_check", check_def_integrity),
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("tail_branch_inline", tail_branch_inline),
        ("global_constant_folding", global_constant_folding), -- includes a local constant folding pass
        ("dead_argument_eliminator", dead_argument_eliminator), -- includes a dead code elimination pass
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Common Pattern Rewrites Section --
        ("eq_chain_inline", eq_chain_inline),
        ("partial_cleanup", cleanup Partial),
        -- Inlining Section
        ("inlining", aggressive_inlining Nothing True),
        ("full_cleanup", cleanup Full),
        -- Specialising
        ("specialising", aggressive_specialising Nothing True 5),
        ("full_cleanup", cleanup Full),
        -- Monadic Expression Optimisation (their pattern should be visible by now)
        ("global_constant_folding", global_constant_folding), -- Make sure patterns are visible
        ("apply_outlining", apply_outlining True), -- despite the name does some inlining as well
        ("full_cleanup", cleanup Full),
        -- Post transform Optims & clean ups
        ("dead_argument_eliminator", dead_argument_eliminator), -- We have the final form now and can eliminate
        ("dead_data_elimination",dead_data_eliminator), -- We have the final form now and can eliminate
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("full_cleanup", cleanup Full),
        -- From here on its mostly the necessary stuff
        -- Untupling Section --
        ("tupled_returns", tupled_returns),
        ("full_cleanup", cleanup Full),
        -- Implicit Injection Section --
        ("implicit_injection", implicit_injection),
        ("partial_cleanup", cleanup Partial),
        -- Cleanup of final code
        ("eq_chain_inline", eq_chain_inline), -- seems not to help test016 still keeps the eqChain
        ("full_cleanup", cleanup Full),
        -- Closure Gen Preparation Section --
        ("closure_gen", closure_gen),
        ("essential_cleanup", cleanup Essential),
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Cleanup of closure code
        -- Todo: Current Closure model needs an additional argument that not visible in the MKClosue signature thus this is a bade idea
        -- ("inlining_save_", inlining_save), -- some closures can be inlined
        -- Register Allocation Section --
        ("allocate_registers", allocate_registers)
    ]

public export
data OptimizationLevel : Type where
    Level0 : OptimizationLevel
    Level1 : OptimizationLevel
    Level2 : OptimizationLevel
    Level3 : OptimizationLevel


getActivePhases : OptimizationLevel -> List (String,CairoCodePass)
getActivePhases Level0 = minimalViablePhases
getActivePhases Level1 = intermediaryCompilerPhases
getActivePhases Level2 = standardCompilerPhases
getActivePhases Level3 = aggressiveCompilerPhases


export
compileIR : OptimizationLevel -> TargetType -> List (CairoName, CairoDef) -> Bool -> String -> IO String
compileIR optimLevel targetType cairocode True irFolder = do
  printIrToFile irFolder "start" 0 cairocode
  start <- clockTime Monotonic
  processed_code <- foldlM (executePhase True irFolder) (cairocode, 1) (getActivePhases optimLevel)
  end <- clockTime Monotonic
  let time = timeDifference end start
  putStrLn $ "Cairo backend took "++(show time)++" to run"
  pure $ generate_code targetType $ fst processed_code
compileIR optimLevel targetType cairocode False irFolder = do
  processed_code <- foldlM (executePhase False irFolder) (cairocode, 1) (getActivePhases optimLevel)
  pure $ generate_code targetType $ fst processed_code

public export
data CompilerInput : Type where
 CairoInput : List (CairoName, CairoDef) -> CompilerInput
 StarkNetInput : List ABIEntry -> List (CairoName, CairoDef) -> CompilerInput

export
compile : OptimizationLevel -> CompilerInput -> Bool -> String -> IO String
compile optimLevel (CairoInput blank_cairocode) = compileIR optimLevel Cairo ((entryDef main_def)::blank_cairocode)
    where main_def : CairoDef
          main_def = fromMaybe (assert_total $ idris_crash "Cairo main is missing") (lookup	cairo_main blank_cairocode)
compile optimLevel (StarkNetInput abi blank_cairocode) = compileIR optimLevel StarkNet ((generateAbiFunctions abi) ++ blank_cairocode)

