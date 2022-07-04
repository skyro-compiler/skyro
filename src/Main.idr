module Main

import Core.Name.Namespace
import Core.Options
import Core.Context
import Compiler.Common
import Core.CompileExpr
import Compiler.ANF
import Compiler.VMCode
import Compiler.NoMangle
import Idris.Driver
import Data.List
import Data.List1
import Data.String
import Data.Vect
import Data.Either
import Data.SortedSet
import Data.SortedMap
import Language.JSON
import Protocol.Hex
import System
import System.File
import System.Directory
import Libraries.Utils.Path
import CommonDef
import CairoCode.CairoCode
import CairoCode.CairoCodeSerializer
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
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
import RewriteRules.ApplyShift
import Primitives.Primitives
import ABI.Definitions
import ABI.Generator

import Debug.Trace
import System.Clock

generateMainCall : CairoDef -> CairoReg -> CairoReg -> List CairoInst
generateMainCall (FunDef [_] _ [_] _) resReg stateReg = [CALL [resReg] empty cairo_main [stateReg]]
generateMainCall (FunDef Nil _ [_] _) resReg stateReg = [CALL [reg 0] empty cairo_main [], APPLY resReg empty (reg 0) stateReg]
    where reg : Int -> CairoReg
          reg i = Unassigned (Just "main_call") i 0
generateMainCall _ _ _ = assert_total $ idris_crash "Unsupported Main signature"

genericEntryDef : LinearImplicit -> CairoDef -> (Name, CairoDef)
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

eliminate_unused_and_order_topological : CairoCodePass
eliminate_unused_and_order_topological cairocode = orderUsedDefs cairocode

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

dead_data_eliminator : CairoCodePass
dead_data_eliminator cairocode = deadDataEliminator cairocode

data CleanupMode = Full | Partial | Essential

cleanup : CleanupMode -> CairoCodePass
cleanup Full cairocode = dead_code_eliminator $ constant_folding $ eliminate_unused_and_order_topological cairocode
cleanup Partial cairocode = dead_code_eliminator $ constant_folding cairocode
cleanup Essential cairocode = map orderUnassignedRegIndexes cairocode

global_constant_folding : CairoCodePass
global_constant_folding cairocode = globalStaticOptimize cairocode

inlining_temporary : CairoCodePass
inlining_temporary cairocode = inlineDefs cairocode

inlining_save_temporary : CairoCodePass
inlining_save_temporary cairocode = inlineSaveDefs cairocode

apply_outlining : CairoCodePass
apply_outlining = applyOutlining

specialising_temporary : CairoCodePass
specialising_temporary cairocode = specialiseDefs cairocode

dead_argument_eliminator : CairoCodePass
dead_argument_eliminator cairocode = eliminateDeadArgumentsDefs cairocode

closure_gen : CairoCodePass
closure_gen cairocode = preprocessClosures cairocode

allocate_registers : CairoCodePass
allocate_registers cairocode = reverse (snd (foldl allocateCairoDef (empty, []) cairocode))
     where allocateCairoDef : (SortedSet Name, List (Name, CairoDef)) -> (Name, CairoDef) -> (SortedSet Name, List (Name, CairoDef))
           allocateCairoDef (safeCalls, acc) (name, cairodef) = let (ncdef, newSafeCalls) = allocateCairoDefRegisters safeCalls (name, cairodef) in (newSafeCalls , (name,ncdef)::acc)

-- todo: change to infere entry_name(s) instead of giving down
generate_code : TargetType -> List (Name, CairoDef) -> String
generate_code targetType cairocode = generateCairoCode targetType cairocode


{-
debug : List (Name, CairoDef) -> List String
debug strs = strs >>= extract
    where extract : (Name, CairoDef) -> List String
          extract (name, ForeignDef (MkForeignInfo True _ _ _) _ _) = [cairoName name]
          extract _ = []
-}

printIrToFile : String -> String -> Nat -> List (Name, CairoDef) -> IO ()
printIrToFile irFolder phaseName phaseNo res = do
  let phaseNo' = if phaseNo < 10 then "0\{show phaseNo}" else show phaseNo
  let out = irFolder </> "\{phaseNo'}_\{phaseName}.skyro"
  let representation = serializeProgram res
  -- Makes sure directory exists, but doesn't check it's a directory and not a file (unlikely to occur)
  folderExists <- exists irFolder
  Right () <- the (IO (Either FileError ())) (if folderExists then pure (Right ()) else createDir irFolder)
    | Left err => printLn (FileErr out err)
  Right () <- writeFile out representation
    | Left err => printLn (FileErr out err)
  pure ()

executePhase : Bool -> String -> (List (Name, CairoDef), Nat) -> (String, CairoCodePass) -> IO (List (Name, CairoDef), Nat)
executePhase True irFolder (cairocode, phaseNo) (phaseName, phaseFunction) = do
    putStrLn $ "Running phase: " ++ phaseName
    start <- clockTime Monotonic
    let result = phaseFunction cairocode
    end <- clockTime Monotonic
    let time = timeDifference end start
    putStrLn $ "Phase " ++ phaseName ++ " took "++(show time)++" to run"
    printIrToFile irFolder phaseName phaseNo result
    pure (result, phaseNo + 1)
executePhase False _ (cairocode, phaseNo) (phaseName, phaseFunction) = do
    let result = phaseFunction cairocode
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


-- Todo: finding the right chain is hard
--  An optim would be have some sub sections that are repeated until nothing changes
--   Would need a highly efficent eq of List (Name, CairoDef)
--     1. Same length
--     2. Same names
--     3. Same function types & same argument return Regs
--     4. Same body length
--     5. Same Instructions (for case we can shortut: Same num branches, Same Branch Lengths, then Same Branches)
compilerPhases : List (String,CairoCodePass)
compilerPhases = [
        -- Prepare Section & Initial Pass Section
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        ("global_constant_folding", global_constant_folding), -- includes a local constant folding pass
        ("dead_argument_eliminator", dead_argument_eliminator), -- includes a dead code elimination pass
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Common Pattern Rewrites Section --
        ("eq_chain_inline", eq_chain_inline),
        ("partial_cleanup", cleanup Partial),
        -- Inlining Section
        ("inlining_temporary", inlining_temporary),
        ("full_cleanup", cleanup Full),
        -- Specialising
        ("specialising_temporary", specialising_temporary),
        ("full_cleanup", cleanup Full),
        ("dead_argument_eliminator", dead_argument_eliminator),
        -- Inlining Section (We may be able to inline more after specialising)
        ("inlining_temporary", inlining_temporary),
        ("full_cleanup", cleanup Full),
        -- DeadDataElimination
        ("dead_data_elimination",dead_data_eliminator),
        ("full_cleanup", cleanup Full),
        -- Post transform Optims
        ("global_constant_folding", global_constant_folding), -- inlining may reveal new opportunities
        ("dead_argument_eliminator", dead_argument_eliminator), -- inlining may reveal new dead arguments
        ("eliminate_unused_and_order_topological", eliminate_unused_and_order_topological),
        -- Monadic Expression Optimisation (their pattern should be visible by now)
        ("apply_outlining", apply_outlining), -- despite the name does some inlining as well
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
        -- Cleanup of final code
        ("inlining_save_temporary", inlining_save_temporary), -- some closures can be inlined
        -- ("eq_chain_inline", eq_chain_inline), -- seems not to help test016 still keeps the eqChain
        ("full_cleanup", cleanup Full),
        -- Register Allocation Section --
        ("allocate_registers", allocate_registers)
    ]

tracedCompilerPhases : List (String,CairoCodePass)
tracedCompilerPhases = ("trace", trace_code)::compilerPhases

activePhases : List (String,CairoCodePass)
activePhases = compilerPhases

export
compileIR : TargetType -> List (Name, CairoDef) -> Bool -> String -> IO String
compileIR targetType cairocode True irFolder = do
  printIrToFile irFolder "start" 0 cairocode
  start <- clockTime Monotonic
  processed_code <- foldlM (executePhase True irFolder) (cairocode, 1) activePhases
  end <- clockTime Monotonic
  let time = timeDifference end start
  putStrLn $ "Cairo backend took "++(show time)++" to run"
  pure $ generate_code targetType $ fst processed_code
compileIR targetType cairocode False irFolder = do
  processed_code <- foldlM (executePhase False irFolder) (cairocode, 1) activePhases
  pure $ generate_code targetType $ fst processed_code



public export
data CompilerInput : Type where
 CairoInput : List (Name, CairoDef) -> CompilerInput
 StarkNetInput : List ABIEntry -> List (Name, CairoDef) -> CompilerInput

compile : CompilerInput -> Bool -> String -> IO String
compile (CairoInput blank_cairocode) = compileIR Cairo ((entryDef main_def)::blank_cairocode)
    where main_def : CairoDef
          main_def = fromMaybe (assert_total $ idris_crash "Cairo main is missing") (lookup	cairo_main blank_cairocode)
compile (StarkNetInput abi blank_cairocode) = compileIR StarkNet ((generateAbiFunctions abi) ++ blank_cairocode)

prepareCairoInput : List (Name, ANFDef) -> Core CompilerInput
prepareCairoInput anf = do
    blank_cairocode <- parse_anf_code anf
    pure (CairoInput blank_cairocode)

error : String -> a
error msg = assert_total $ idris_crash msg

getKey : String -> JSON -> JSON
getKey key obj@(JObject map) = case Data.List.lookup key map of
  Just value => value
  Nothing => error "Did not find: \{show key} in \{show obj}"
getKey _ j = error "Cant find key in \{show j}"

str : JSON -> String
str (JString s) = s
str j = error "Expected JString, got \{show j}"

array : String -> JSON -> List JSON
array key obj = case getKey key obj of
  JArray elems => elems
  j => error "Expected JArray, got \{show j}"

getStr : String -> JSON -> String
getStr key = str . getKey key

getNameString : JSON -> String
getNameString = str . getKey "name"

stringToName : String -> Name
stringToName str = NS (mkNamespace (buildNS (init fragments))) $ UN $ Basic (last fragments)
  where fragments : List1 String
        fragments = split (\c => c == '.') str
        buildNS : List String -> String
        buildNS [] = ""
        buildNS (n::[]) = n
        buildNS (n::m::ns) = n ++ "." ++ buildNS (m::ns)

getName : JSON -> Name
getName obj = stringToName (getNameString obj)

ensureArgLess : JSON -> a -> a
ensureArgLess json res = case (array "args" json) of
    Nil => res
    _ => error "unexpected type arguments"

mutual
    getArgs : SortedSet String -> JSON -> List ABIType
    getArgs bindings json = map (getArgType bindings) (array "args" json)

    getArgType : SortedSet String -> JSON -> ABIType
    getArgType bindings tyObj = case getStr "name" tyObj of
        "Common.Felt.Felt" => ensureArgLess tyObj (PrimType FeltType)
        "Common.Segment.Segment" => ensureArgLess tyObj SegmentType
        "Prelude.Types.Nat" => ensureArgLess tyObj (PrimType IntegerType)
        "$Primitive.Integer" => ensureArgLess tyObj (PrimType IntegerType)
        "$Primitive.Bits8" => ensureArgLess tyObj (PrimType Bits8Type)
        "$Primitive.Bits16" => ensureArgLess tyObj (PrimType Bits16Type)
        "$Primitive.Bits32" => ensureArgLess tyObj (PrimType Bits32Type)
        "$Primitive.Bits64" => ensureArgLess tyObj (PrimType Bits64Type)
        "$Primitive.Int" => ensureArgLess tyObj (PrimType IntType)
        "$Primitive.Int8" => ensureArgLess tyObj (PrimType Int8Type)
        "$Primitive.Int16" => ensureArgLess tyObj (PrimType Int16Type)
        "$Primitive.Int32" => ensureArgLess tyObj (PrimType Int32Type)
        "$Primitive.Int64" => ensureArgLess tyObj (PrimType Int64Type)
        other => if contains other bindings
            then ensureArgLess tyObj (Variable other)
            else NamedType (stringToName other) (getArgs bindings tyObj)

getType : SortedSet String -> JSON -> ABIType
getType bindings obj = getArgType bindings (getKey "type" obj)

getABIData : SortedSet String -> JSON -> ABIData
getABIData bindings obj = MkField (getNameString obj) (getType bindings obj)

getInputs : SortedSet String -> JSON -> List ABIData
getInputs bindings obj = map (getABIData bindings) (array "inputs" obj)

getOutput : SortedSet String -> JSON -> Maybe ABIData
getOutput bindings obj = Just $ getABIData bindings (getKey "output" obj)

getConstructor : SortedSet String -> JSON -> (List ABIData)
getConstructor bindings obj = map (getABIData bindings) (array "elems" obj)

extractTypeVars : List JSON -> (List String, List JSON)
extractTypeVars Nil = (Nil, Nil)
extractTypeVars (x::xs) = let tyObj = getKey "type" x in case getStr "name" tyObj of
    "$Special.Type" => let (tvs, args) = extractTypeVars xs in ensureArgLess tyObj ((getNameString x)::tvs, args)
    _ => (Nil, x::xs)

extractBindings : List (List JSON) -> (List String, List (List JSON))
extractBindings rawArg = case unifiedTVars of
    [tvars] => (tvars, map snd splitted)
    _ => error "type constructors need to have the same amount of type arguments"
    where splitted : List (List String, List JSON)
          splitted = map extractTypeVars rawArg
          unifiedTVars : List (List String)
          unifiedTVars = nub (map fst splitted)

getConstructors : JSON -> (List String, List (List ABIData))
getConstructors obj = let (bindings, realArgs) = extractBindings $ map (array "elems") (array "constructors" obj) in
    (bindings, map (map (getABIData (fromList bindings))) realArgs)


jsonToABIEntry : JSON -> ABIEntry
jsonToABIEntry obj = case getStr "type" obj of
  "Event"       => Event (getName obj)
  "StorageVar"  => StorageVar (getName obj)
  "View"        => ViewFunction (getName obj) (getInputs empty obj) (getOutput empty obj)
  "External"    => ExternalFunction (getName obj) (getInputs empty obj) (getOutput empty obj)
  "Constructor" => Constructor (getName obj) (getInputs empty obj)
  "L1Handler"   => L1Handler (getName obj) (getInputs empty obj)
  "Type"        => case getConstructors obj of
                     (tvars, [singleConstr]) => Struct (getName obj) tvars singleConstr
                     (tvars, ctrs) => Variant (getName obj) tvars ctrs
  t             => error "Unknown type: \{show t}" 

prepareStarkNetInput : Bool -> Ref Ctxt Defs -> List (Name, ANFDef) -> Core CompilerInput
prepareStarkNetInput verbose defs anf = do
    defs <- get Ctxt
    let ctxt = defs.gamma
    _ <- initNoMangle "cairo" (const True)
    noMangleNames <- getAllNoMangle
    noMangleStrings <- traverse (\name => full ctxt name >>= lookupNoMangle) noMangleNames
    when verbose $ coreLift $ putStrLn "noMangleStrings:" >> putStrLn (show noMangleStrings)
    let abiEntryStrings = catMaybes noMangleStrings
    let abiEntryJSON = catMaybes (map Language.JSON.parse abiEntryStrings)
    when verbose $ coreLift $  putStrLn "Parsed ABI entries:" >> traverse_ (putStrLn . show) abiEntryJSON
    let entries = map jsonToABIEntry abiEntryJSON
    blank_cairocode <- parse_anf_code anf
    pure (StarkNetInput entries blank_cairocode)


maybeTimed : Bool -> String -> Core a -> Core a
maybeTimed True msg res = do
    start <- coreLift $ clockTime Monotonic
    executedRes <- res
    end <- coreLift $ clockTime Monotonic
    let time = timeDifference end start
    coreLift $ putStrLn $ (msg ++ " took "++(show time)++" to run")
    pure executedRes
maybeTimed False _ res = res

compileFromIdris : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) -> ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileFromIdris defs tmpDir outputDir term outfile =
  do
     ds <- getDirectives (Other "cairo")
     let isVerbose = elem "verbose" ds
     cd <- maybeTimed isVerbose "Idris frontend" (getCompileData False ANF term)

     input <- maybeTimed isVerbose "SkyroIR preparations" (if elem "starknet" ds then prepareStarkNetInput isVerbose defs cd.anf else prepareCairoInput cd.anf)
     res <- coreLift $ compile input isVerbose (outputDir </> ".phases")

     -- produce output file
     let out = outputDir </> outfile
     Right () <- coreLift (writeFile out res)
       | Left err => throw (FileErr out err)
     when isVerbose $ coreLift $ putStrLn "Idris Compile Done"
     -- compile cairo file
     pure (Just out)

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute defs tmpDir term = do coreLift $ putStrLn "Maybe in an hour."

cairoCodegen : Codegen
cairoCodegen = MkCG compileFromIdris execute Nothing Nothing

export
main : IO ()
main = mainWithCodegens [("cairo", cairoCodegen)]
