module CodeGen.CodeGen

import Core.Name.Namespace
import Core.Context
import Compiler.Common
import Core.CompileExpr
import Compiler.ANF
import Data.List
import Data.String
import Data.Vect
import Data.Either
import Data.SortedSet
import Data.SortedMap
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CairoCode.Traversal.Base
import CommonDef
import CodeGen.CodeGenHelper
import CodeGen.CurryingBasedClosures

import Primitives.Externals
import Primitives.Primitives
import Primitives.Common


%hide Prelude.toList

-- This is all for now maybe we need morw later
record CodeGenInfo where
    constructor MkCodeGenInfo
    -- to get the order right for foreign calls
    implicits: List LinearImplicit

extractCodeGenInfoFromDef : CairoDef ->  CodeGenInfo
extractCodeGenInfoFromDef (FunDef _ impls _ _) = MkCodeGenInfo $ keys impls
extractCodeGenInfoFromDef (ForeignDef (MkForeignInfo _ _ impls _ _) _ _) = MkCodeGenInfo impls

collectCodeGenInfo : List (Name, CairoDef) -> SortedMap Name CodeGenInfo
collectCodeGenInfo defs = fromList $ map (\(n,def) => (n, extractCodeGenInfoFromDef def)) defs

-- Helper for compiling calls
compileCall : Name -> CodeGenInfo -> List CairoReg -> LinearImplicitArgs -> List CairoReg -> String
compileCall n info rs linImpls args = """
     let (\{ regList }) = \{ cairoName n } (\{ paramList })
     \{ assigList }
     """
     where join : List String -> String
           join Nil = ""
           join (x::xs) = foldl1 (\s1,s2 => s1 ++ ", "++s2 ) (x::xs)
           manifestReg : CairoReg -> String
           manifestReg r = if isLocal r then (regName r) ++ "_tmp" else regName r
           implList : List (CairoReg, CairoReg)
           implList = map (\i => fromMaybe (assert_total $ idris_crash "missing implicit") (lookup i linImpls)) (implicits info)
           joinedRs : List CairoReg
           joinedRs = rs ++ (map snd implList)
           regList : String
           regList = join (map manifestReg joinedRs)
           paramList : String
           paramList = showSep ", " (map compileReg ((map fst implList) ++ args))
           implRes : List CairoReg
           implRes = map fst implList
           assigList : String
           assigList = concatMap (\r => (compileRegDecl r) ++ " = " ++ (compileReg r) ++"_tmp\n") (filter isLocal joinedRs)


compileConstructor : List String -> Int -> CairoReg -> String
compileConstructor values start reg = """
 #MKCON
 let (\{ compileReg reg }_ptr) = alloc()
 \{ compileRegDecl reg } = cast(\{ compileReg reg }_ptr,felt)
 \{ fst res }
 """
  where
    res : (String, Int)
    res = foldl (\(acc, cnt), comp => (acc ++ "assert [" ++ (compileReg reg) ++ " + " ++ show cnt ++ "] = " ++ comp ++ "\n", cnt+1)) ("", start) values

{- 
-- More efficient but not starknet compatible (because it uses hints)
compileConstructor : List String -> Int -> String -> String -> String -> String
compileConstructor values start defineReg regName postfix = """
 #MKCON
 \{ defineReg }
 %{ ids.\{regName} = segments.add() %}
 \{ fst res }
 \{ postfix }

 """
 where res : (String, Int)
       res = foldl (\(acc, cnt), comp => (acc ++ "assert [" ++ regName ++ " + " ++ show cnt ++ "] = " ++ comp ++ "\n", cnt+1)) ("", start) values
-}


mutual
     compileGeneralCase: SortedMap Name CodeGenInfo -> String -> String -> List CairoInst -> String -> String
     compileGeneralCase cInf value tagOrConst vminsts elseCase = """
        if \{ value } == \{ tagOrConst }:
            \{ concatMap (compileCairoInst cInf) vminsts }
        else:
            \{ elseCase }
        end

        """

     compileCase : SortedMap Name CodeGenInfo -> CairoReg -> (Int, List CairoInst) -> String -> String
     compileCase cInf reg (tag, vminsts) elseCase = compileGeneralCase cInf ("[" ++ compileReg reg ++ "]") (show tag) vminsts elseCase
     compileCases : SortedMap Name CodeGenInfo -> CairoReg -> List (Int, List CairoInst) -> Maybe (List CairoInst) -> String
     compileCases _ scr Nil Nothing = ""
     compileCases cInf scr Nil (Just def) = concatMap (compileCairoInst cInf) def
     compileCases cInf scr ((_,cs)::Nil) Nothing = concatMap (compileCairoInst cInf) cs
     compileCases cInf scr alts (Just def) = foldr (\c, acc => compileCase cInf scr c acc) (concatMap (compileCairoInst cInf) def) alts
     compileCases cInf scr ((_,cs)::alts) Nothing = foldr (\c, acc => compileCase cInf scr c acc) (concatMap (compileCairoInst cInf) cs) alts

     compileConstCase : SortedMap Name CodeGenInfo ->  CairoReg -> (CairoConst, List CairoInst) -> String -> String
     compileConstCase  cInf reg (constant, vminsts) elseCase = compileGeneralCase cInf (compileReg reg) (compileConst constant) vminsts elseCase
     compileConstCases : SortedMap Name CodeGenInfo ->  CairoReg -> List (CairoConst, List CairoInst) -> Maybe (List CairoInst) -> String
     compileConstCases _ reg Nil Nothing = ""
     compileConstCases cInf reg Nil (Just def) = concatMap (compileCairoInst cInf) def
     compileConstCases cInf reg ((_,cs)::Nil) Nothing = concatMap (compileCairoInst cInf) cs
     compileConstCases cInf reg alts (Just def) = foldr (\c, acc => compileConstCase cInf reg c acc) (concatMap (compileCairoInst cInf) def) alts
     compileConstCases cInf reg ((_,cs)::alts) Nothing = foldr (\c, acc => compileConstCase cInf reg c acc) (concatMap (compileCairoInst cInf) cs) alts

     compileCairoInst : SortedMap Name CodeGenInfo -> CairoInst -> String
     compileCairoInst _ (ASSIGN r v) = "\{ compileRegDecl r } = \{ compileReg v }\n"
     -- Todo: Add Unpacked Versions (They are basically just multi assignes)
     compileCairoInst _ (MKCON r (Just t) args) = compileConstructor (show t :: map compileReg args) 0 r 
     compileCairoInst _ (MKCON r Nothing args) = compileConstructor (map compileReg args) 1 r
     compileCairoInst _ (MKCLOSURE r n m args) = genMkClosure r n m args

     -- Todo: This does not work with closures pointing to %foreign as the impl param order may be wrong
     --       However, Closure system needs overhaul or defunct anyway
     --       If we leave as is, we need to make wrappers for foreign closures that reorder implicit args if necessary
     compileCairoInst _ (APPLY r linImpls f a) = genMkApply r linImpls f a
     compileCairoInst _ (MKCONSTANT r c) =
        if (isLocal r) then "\{ compileRegDecl r } = \{ compileConst c }\n"
        else if (isConst r) then  ""
        else compileConstRegDecl r ++ " = \{ compileConst c }\n"

     compileCairoInst cInf (CALL rs linImpls n args) = compileCall n (fromMaybe (assert_total $ idris_crash "missing function") (lookup n cInf) ) rs linImpls args
     -- compile primFns
     compileCairoInst cinf (OP r linImpls op args) = 
       case generatePrimFnCode op r args linImpls of
         Instructions insts =>  concatMap (compileCairoInst cinf) insts
         Raw code => code
     compileCairoInst _ (EXTPRIM rs linImpls n args) = externalCodeGen n rs linImpls args
     compileCairoInst cInf (CASE scr alts def) = compileCases cInf scr alts def
     compileCairoInst cInf (CONSTCASE scr alts def) = compileConstCases cInf scr alts def
     compileCairoInst _ (RETURN rs linImpls) = "return (" ++ join (map compileReg (rs ++ (values linImpls))) ++ ")\n"
        where join : List String -> String
              join Nil = ""
              join (x::xs) = foldl1 (\s1,s2 => s1 ++ ", "++s2 ) (x::xs)

     -- Project pos + 1 since pos + 0 is the tag
     compileCairoInst _ (PROJECT r val pos) = "\{ compileRegDecl r } = [\{ compileReg val } + \{ show (pos + 1) }]\n"
     compileCairoInst _ (NULL r ) = compileRegDecl r ++ " = 0\n"
     compileCairoInst _ (ERROR r str) = impossibleCase r (show str)

compileCairoDef : SortedMap Name CodeGenInfo -> Name -> CairoDef -> String
compileCairoDef cInf name def@(FunDef args linImplicits rets body) = """
     func \{ cairoName name }(\{ showSep ", " (map regName ((values linImplicits) ++ args)) }) -> (\{ showSep ", " (rets ++ (map implicitName (keys linImplicits))) }):
       \{if isNil collectedLocals then "" else ("alloc_locals\n" ++ compiledLocals)}
       \{concatMap (compileCairoInst cInf) body}
     end

     """
     where collectedLocals : List CairoReg
           collectedLocals = toList $ collectLocals (name, def)
           compiledLocals : String
           compiledLocals = concatMap (\reg => "local " ++ (compileReg reg) ++ "\n") collectedLocals

compileCairoDef _ name (ForeignDef info _ _) = code info

extractKnownBuiltin : LinearImplicit -> List String
extractKnownBuiltin (MKLinearImplicit "bitwise_ptr") = ["bitwise"]
extractKnownBuiltin (MKLinearImplicit "pedersen_ptr") = ["pedersen"]
extractKnownBuiltin (MKLinearImplicit "output_ptr") = ["output"]
extractKnownBuiltin (MKLinearImplicit "range_check_ptr") = ["range_check"]
extractKnownBuiltin (MKLinearImplicit "ecdsa_ptr") = ["ecdsa"]
extractKnownBuiltin _ = []

-- TODO Group by namespace, deduplicate functions names and generate mutli-imports
compileImports : SortedSet Import -> String
compileImports imports =
  showSep "\n" (map (\(MkImport ns f) => "from " ++ ns ++ " import " ++ f ) (toList imports))


builtinsPragma : List LinearImplicit -> String
builtinsPragma builtins = "%builtins " ++ showSep " " (builtins >>= extractKnownBuiltin)


addHeader : Bool -> List LinearImplicit -> SortedSet Import -> String -> String
addHeader isLib builtins imports defs =
"""
\{ if not isLib then builtinsPragma builtins else "" }
\{ compileImports imports }
# HACK: The dw 0 is here because the programStart: label used in the closure generators would not work if there are no imports
dw 0
programStart:
\{ defs }

"""

extractMainImplicits : Name -> List (Name, CairoDef) -> List LinearImplicit
extractMainImplicits _ Nil = assert_total $ idris_crash "no cairo_main found"
extractMainImplicits mainName ((name, (FunDef _ impls _ _))::xs) = 
    if mainName == name
        then keys impls
        else extractMainImplicits mainName xs
extractMainImplicits mainName (def::xs) = extractMainImplicits mainName xs


collectImports : List (Name, CairoDef) -> SortedSet Import
collectImports cairocode = snd $ runVisitConcatCairoDefs (pureTraversal importTraversal) cairocode
    where importTraversal : InstVisit CairoReg -> SortedSet Import
          importTraversal (VisitMkCon _ _ _) = singleton (MkImport "starkware.cairo.common.alloc" "alloc")
          importTraversal (VisitMkClosure _ _ _ _) = singleton (MkImport "starkware.cairo.common.alloc" "alloc")
          importTraversal (VisitForeignFunction _ fi _ _) = fi.imports
          importTraversal (VisitExtprim _ _ name _) = externalImports name
          importTraversal (VisitOp _ _ fn _) = primFnImports fn
          importTraversal _ = empty

export
generateCairoCode : Bool -> Name -> List (Name, CairoDef) -> String
generateCairoCode isLib mainName cairocode = addHeader isLib mainImplicits imports compiledDefs
    where mainImplicits : List LinearImplicit
          mainImplicits = extractMainImplicits mainName cairocode
          cInf : SortedMap Name CodeGenInfo
          cInf = collectCodeGenInfo cairocode
          imports : SortedSet Import
          imports = collectImports cairocode
          compiledDefs : String
          compiledDefs = concatMap (\(name, cairodef) => compileCairoDef cInf name cairodef ++ "\n\n") cairocode
          
