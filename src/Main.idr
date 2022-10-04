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

import CairoCode.Name
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
import System.Clock
import Libraries.Utils.Path
import CommonDef

import Debug.Trace
import Compiler
import Idris.Transpiler

import CairoCode.CairoCode
import ABI.Definitions as Skyro
import Idris.ABI as Idris
import Idris.ABISpecializing
import Idris.Naming

parse_anf_code : List (Name, ANFDef) -> Core (List (CairoName, CairoDef))
parse_anf_code anfcode = map concat (traverse fromANFDef anfcode)

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

bool : JSON -> Bool
bool (JBoolean b) = b
bool j = error "Expected JBoolean, got \{show j}"

getBool : String -> JSON -> Bool
getBool key = bool . getKey key

isAbstract : JSON -> Bool
isAbstract = getBool "abstract"

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

stringToName : String -> CairoName
stringToName str = fromIdrisName $ NS (mkNamespace (buildNS (init fragments))) $ UN $ Basic (last fragments)
  where fragments : List1 String
        fragments = split (\c => c == '.') str
        buildNS : List String -> String
        buildNS [] = ""
        buildNS (n::[]) = n
        buildNS (n::m::ns) = n ++ "." ++ buildNS (m::ns)

getName : JSON -> CairoName
getName obj = stringToName (getNameString obj)

ensureArgLess : JSON -> a -> a
ensureArgLess json res = case (array "args" json) of
    Nil => res
    _ => error "unexpected type arguments"

mutual
    getArgs : SortedSet String -> JSON -> List Idris.ABIType
    getArgs bindings json = map (getArgType bindings) (array "args" json)

    getArgType : SortedSet String -> JSON -> Idris.ABIType
    getArgType bindings tyObj = case getStr "name" tyObj of
        "Common.Felt.Felt" => ensureArgLess tyObj (Idris.PrimType FeltType)
        "Common.Segment.Segment" => ensureArgLess tyObj Idris.SegmentType
        "Prelude.Types.Nat" => ensureArgLess tyObj (Idris.PrimType IntegerType)
        "$Primitive.Integer" => ensureArgLess tyObj (Idris.PrimType IntegerType)
        "$Primitive.Bits8" => ensureArgLess tyObj (Idris.PrimType Bits8Type)
        "$Primitive.Bits16" => ensureArgLess tyObj (Idris.PrimType Bits16Type)
        "$Primitive.Bits32" => ensureArgLess tyObj (Idris.PrimType Bits32Type)
        "$Primitive.Bits64" => ensureArgLess tyObj (Idris.PrimType Bits64Type)
        "$Primitive.Int" => ensureArgLess tyObj (Idris.PrimType IntType)
        "$Primitive.Int8" => ensureArgLess tyObj (Idris.PrimType Int8Type)
        "$Primitive.Int16" => ensureArgLess tyObj (Idris.PrimType Int16Type)
        "$Primitive.Int32" => ensureArgLess tyObj (Idris.PrimType Int32Type)
        "$Primitive.Int64" => ensureArgLess tyObj (Idris.PrimType Int64Type)
        other => if contains other bindings
            then ensureArgLess tyObj (Variable other)
            else NamedType (stringToName other) (getArgs bindings tyObj)

getType : SortedSet String -> JSON -> Idris.ABIType
getType bindings obj = getArgType bindings (getKey "type" obj)

getABIData : SortedSet String -> JSON -> Idris.ABIData
getABIData bindings obj = MkField (getNameString obj) (getType bindings obj)

getInputs : SortedSet String -> JSON -> List Idris.ABIData
getInputs bindings obj = map (getABIData bindings) (array "inputs" obj)

getOutput : SortedSet String -> JSON -> Maybe Idris.ABIData
getOutput bindings obj = Just $ getABIData bindings (getKey "output" obj)

getConstructor : SortedSet String -> JSON -> (List Idris.ABIData)
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

getConstructors : JSON -> (List String, List (List Idris.ABIData))
getConstructors obj = let (bindings, realArgs) = extractBindings $ map (array "elems") (array "constructors" obj) in
    (bindings, map (map (getABIData (fromList bindings))) realArgs)


jsonToABIEntry : JSON -> Idris.ABIEntry
jsonToABIEntry obj = case getStr "type" obj of
  "Event"       => Idris.Event (noMangle (getName obj))
  "StorageVar"  => Idris.StorageVar (noMangle (getName obj))
  "View"        => Idris.ViewFunction (getName obj) (isAbstract obj) (getInputs empty obj) (getOutput empty obj)
  "External"    => Idris.ExternalFunction (getName obj) (isAbstract obj) (getInputs empty obj) (getOutput empty obj)
  "Constructor" => Idris.Constructor (getName obj) (getInputs empty obj)
  "L1Handler"   => Idris.L1Handler (getName obj) (getInputs empty obj)
  "Type"        => case getConstructors obj of
                     (tvars, [singleConstr]) => Idris.Struct (getName obj) tvars singleConstr
                     (tvars, ctrs) => Idris.Variant (getName obj) tvars ctrs
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
    when verbose $ coreLift $ putStrLn "Parsed ABI entries:" >> traverse_ (putStrLn . show) abiEntryJSON
    let entries = spezializeEntries $ map jsonToABIEntry abiEntryJSON
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

getOptimLevel : List String -> OptimizationLevel
getOptimLevel ds = if (elem "quick" ds) || (elem "Quick" ds) || (elem "O0" ds) || (elem "o0" ds)
    then Level0
    else if (elem "dev" ds) || (elem "Dev" ds) || (elem "O1" ds) || (elem "o1" ds)
        then Level1
        else if (elem "prod" ds) || (elem "Prod" ds) || (elem "O2" ds) || (elem "o2" ds)
            then Level2
            else if (elem "aggressive" ds) || (elem "Aggressive" ds) || (elem "O3" ds) || (elem "o3" ds)
                then Level3
                else Level2

compileFromIdris : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) -> ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileFromIdris defs tmpDir outputDir term outfile =
  do
     ds <- getDirectives (Other "cairo")
     let isVerbose = elem "verbose" ds
     cd <- maybeTimed isVerbose "Idris frontend" (getCompileData False ANF term)
     input <- maybeTimed isVerbose "SkyroIR preparations" (if elem "starknet" ds then prepareStarkNetInput isVerbose defs cd.anf else prepareCairoInput cd.anf)
     res <- coreLift $ compile (getOptimLevel ds) input isVerbose (outputDir </> ".phases")
     -- produce output file
     let out = outputDir </> outfile
     Right () <- coreLift (writeFile out res)
       | Left err => throw (FileErr out err)
     when isVerbose $ coreLift $ putStrLn "Skyro Compile Done"
     pure (Just out)

-- Todo: What is this for -- is this for repl?
execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute defs tmpDir term = do coreLift $ putStrLn "Maybe in an hour."

cairoCodegen : Codegen
cairoCodegen = MkCG compileFromIdris execute Nothing Nothing

export
main : IO ()
main = mainWithCodegens [("cairo", cairoCodegen)]
