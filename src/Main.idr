module Main

import Core.Name.Namespace
import Core.Options
import Core.Context
import Compiler.Common
import Core.CompileExpr
import Compiler.ANF
import Compiler.VMCode
import Idris.Driver
import Data.List
import Data.String
import Data.Vect
import Data.Either
import Data.SortedSet
import Data.SortedMap
import Protocol.Hex
import System
import System.File
import Libraries.Utils.Path
import CommonDef
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
import CodeGen.CodeGen
import CodeGen.CurryingBasedClosures

import CodeGen.RegAlloc
import Optimisation.DeadCodeElimination
import Optimisation.DeadArgumentEliminator
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.GlobalStaticOptimizer
import Optimisation.Inliner
import Optimisation.OrderAndEliminateDefinitions

import Optimisation.Untupling
import CodeGen.InjectLinearImplicits
import RewriteRules.EqChainInline
import Primitives.Primitives

import Debug.Trace

generateMainCall : CairoDef -> CairoReg -> CairoReg -> List CairoInst
generateMainCall (FunDef [_] _ [_] _) resReg stateReg = [CALL [resReg] empty cairo_main [stateReg]]
generateMainCall (FunDef Nil _ [_] _) resReg stateReg = [CALL [reg 0] empty cairo_main [], APPLY resReg empty (reg 0) stateReg]
    where reg : Int -> CairoReg
          reg i = Unassigned (Just "main_call") i 0
generateMainCall _ _ _ = assert_total $ idris_crash "Unsupported Main signature"

genericEntryDef : LinearImplicit -> CairoDef -> (Name, CairoDef)
genericEntryDef io_implicit main_def = (entry_name, FunDef [] (singleton io_implicit io_ptr_reg) [] body)
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
entryDef : CairoDef -> (Name, CairoDef)
entryDef = genericEntryDef output_builtin

entryDefStarknet : CairoDef -> (Name, CairoDef)
entryDefStarknet = genericEntryDef syscall_builtin

-- Debuging helper Phases
trace_code_selective : ((Name, CairoDef) -> Bool) -> CairoCodePass
trace_code_selective fn cairocode = trace (show (filter fn cairocode)) cairocode

trace_code : CairoCodePass
trace_code cairocode = trace_code_selective (\_ => True) cairocode

-- Compilation Phases
parse_anf_code : List (Name, ANFDef) -> Core (List (Name, CairoDef))
parse_anf_code anfcode = map concat (traverse fromANFDef anfcode)


addRequiredPrimFnHelpers : CairoCodePass
addRequiredPrimFnHelpers cairocode = cairocode ++ findPrimFnDeps cairocode

{- 
replace_primfns : CairoCodePass
replace_primfns cairocode = snd $ runVisitTransformCairoDefs (pureTraversal rewritePrimFns) cairocode
    where rewritePrimFns : InstVisit CairoReg -> List (InstVisit CairoReg)
          rewritePrimFns inst@(VisitOp res linearImplicits (Add Bits8Type) args) = fromCairoInsts $ generatePrimFnCode (Add Bits8Type) res args linearImplicits
          rewritePrimFns inst = [inst]
-}

eliminate_unused_and_order_topological : CairoCodePass
eliminate_unused_and_order_topological cairocode = orderUsedDefs entry_name cairocode

eq_chain_inline : CairoCodePass
eq_chain_inline cairocode = eqChainInline cairocode

tupled_returns : CairoCodePass
tupled_returns cairocode = untupling cairocode

implicit_injection : CairoCodePass
implicit_injection cairocode = injectLinearImplicitsDefs cairocode

constant_folding : CairoCodePass
constant_folding cairocode = localStaticOptimizeDefs cairocode

dead_code_eliminator : CairoCodePass
dead_code_eliminator cairocode = map eliminateDeadCode cairocode

data CleanupMode : Type where
     Full : CleanupMode
     Partial : CleanupMode
     Essential : CleanupMode

cleanup : CleanupMode -> CairoCodePass
cleanup Full cairocode = dead_code_eliminator $ constant_folding $ eliminate_unused_and_order_topological cairocode
cleanup Partial cairocode = dead_code_eliminator $ constant_folding cairocode
cleanup Essential cairocode = map orderUnassignedRegIndexes cairocode

global_constant_folding : CairoCodePass
global_constant_folding cairocode = globalStaticOptimize entry_name cairocode

inlining_temporary : CairoCodePass
inlining_temporary cairocode = inlineDefs entry_name cairocode

dead_argument_eliminator : CairoCodePass
dead_argument_eliminator cairocode = eliminateDeadArgumentsDefs cairocode

closure_gen : CairoCodePass
closure_gen cairocode = preprocessClosures cairocode

allocate_registers : CairoCodePass
allocate_registers cairocode = reverse (snd (foldl allocateCairoDef (empty, []) cairocode))
     where allocateCairoDef : (SortedSet Name, List (Name, CairoDef)) -> (Name, CairoDef) -> (SortedSet Name, List (Name, CairoDef))
           allocateCairoDef (safeCalls, acc) (name, cairodef) = let (ncdef, newSafeCalls) = allocateCairoDefRegisters safeCalls (name, cairodef) in (newSafeCalls , (name,ncdef)::acc)

generate_code : Bool -> List (Name, CairoDef) -> String
generate_code isLib cairocode = generateCairoCode isLib entry_name cairocode


{-
debug : List (Name, CairoDef) -> List String
debug strs = strs >>= extract
    where extract : (Name, CairoDef) -> List String
          extract (name, ForeignDef (MkForeignInfo True _ _ _) _ _) = [cairoName name]
          extract _ = []
-}

executePhase : Bool -> List (Name, CairoDef) -> (String, CairoCodePass) -> IO (List (Name, CairoDef))
executePhase isVerbose cairocode (phaseName, phaseFunction) = do
  when isVerbose $ putStrLn phaseName
  pure $ phaseFunction cairocode

compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) -> ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs tmpDir outputDir term outfile =
  do 
     ds <- getDirectives (Other "cairo")
     let isStarknetLib = elem "starknetlib" ds
     let isVerbose = elem "verbose" ds
     
     cd <- getCompileData False ANF term
     -- Compile ANF to CairoCode
     blank_cairocode <- parse_anf_code cd.anf
     let main_def = fromMaybe (assert_total $ idris_crash "Cairo main is missing") (lookup	cairo_main blank_cairocode)
     let cairocode = (if isStarknetLib then (entryDefStarknet main_def) else (entryDef main_def))::blank_cairocode

     -- config
     let phases: List (String,CairoCodePass) = [
          -- Prepare Section & Initial Pass Section
          ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
          ("global_constant_folding", global_constant_folding), -- includes a local constant folding pass
          ("dead_argument_eliminator", dead_argument_eliminator), -- includes a dead code elimination pass
          ("dead_code_eliminator", dead_code_eliminator),
          ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
          -- Common Pattern Rewrites Section --
          ("eq_chain_inline", eq_chain_inline),
          ("partial_cleanup", cleanup Partial),
          -- Inlining Section
          ("inlining_temporary", inlining_temporary),
          ("full_cleanup", cleanup Full),
          ("dead_argument_eliminator", dead_argument_eliminator), -- inlining may reveal new dead arguments
          -- Untupling Section --
          ("tupled_returns", tupled_returns),
          ("full_cleanup", cleanup Full),
          -- Implicit Injection Section --
          ("implicit_injection", implicit_injection),
          ("partial_cleanup", cleanup Partial),
          -- Closure Gen Preparation Section --
          ("closure_gen", closure_gen),
          ("full_cleanup", cleanup Full),
          -- Primitives --
          ("addRequiredPrimFnHelpers", addRequiredPrimFnHelpers),
          -- ("replace_primfns", replace_primfns),
          -- Register Allocation Section --
          ("allocate_registers", allocate_registers)
     ]

     -- execute
     -- coreLift $ putStrLn (show cairocode)
     processed_code <- coreLift $ foldlM (executePhase isVerbose) cairocode phases
     -- coreLift $ putStrLn (show processed_code)
     let res = generate_code isStarknetLib processed_code

     -- produce output file
     let out = outputDir </> outfile
     Right () <- coreLift (writeFile out res)
       | Left err => throw (FileErr out err)
     when isVerbose $ coreLift $ putStrLn "Idris Compile Done"
     -- call formatter
     -- compile cairo file
     pure (Just out)

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute defs tmpDir term = do coreLift $ putStrLn "Maybe in an hour."

cairoCodegen : Codegen
cairoCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("cairo", cairoCodegen)]
