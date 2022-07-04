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

-- TODO: Make sure tmp names can not collide with function names and other regs -> find a protectod sepertor
--       Then in make CairoName & RegName an escape

-- This is all for now maybe we need morw later
record CodeGenInfo where
    constructor MkCodeGenInfo
    -- to get the order right for foreign calls
    implicits: List LinearImplicit
    params : List CairoReg

data RetInfo : Type where
   External : List CairoReg -> RetInfo
   Internal : List CairoReg -> RetInfo

extractCodeGenInfoFromDef : CairoDef ->  CodeGenInfo
extractCodeGenInfoFromDef (FunDef args impls _ _) = MkCodeGenInfo (keys impls) args
extractCodeGenInfoFromDef (ExtFunDef _ args impls _ _) = MkCodeGenInfo (keys impls) args
extractCodeGenInfoFromDef (ForeignDef (MkForeignInfo _ _ impls _ _) args _) = MkCodeGenInfo impls (map Param (fromZeroTo ((cast args)-1)))

collectCodeGenInfo : List (Name, CairoDef) -> SortedMap Name CodeGenInfo
collectCodeGenInfo defs = fromList $ map (\(n,def) => (n, extractCodeGenInfoFromDef def)) defs

-- Todo: Not yet used: However for complex const support (like BigIntegers) this has to be called before registers are used in code genn
--       The generated code needs to emmit the String (code) first and then use the returned CairoRegs instead of the original ones (argumnents)
--       This gives the Primitive module the opportunity to store the manifested value in a let
-- Todo: we probably need the unique string for register gen
manifestConstRegs : String -> List CairoReg -> (Maybe String, List CairoReg)
manifestConstRegs unique regs = result $ snd $ foldl (manifestReg (unique++"_manifest_")) (0,("",[])) regs
    where result : (String, List CairoReg) -> (Maybe String, List CairoReg)
          result ("",regs) = (Nothing, regs)
          result (code,regs) = (Just code, regs)
          manifestReg : String -> (Int, (String, List CairoReg)) -> CairoReg -> (Int, (String, List CairoReg))
          manifestReg uni (n, (code, acc)) r@(Const _) = case manifestConstReg (uni++(show n)) r of
            (Nothing, rn) => (n, (code, acc++[rn]))
            (Just c, rn) => (n+1, (code++c++"\n", acc++[rn]))
          manifestReg _ (n,(code, acc)) r = (n, (code, acc++[r]))

withManifests : String -> List CairoReg -> (List CairoReg -> String) -> String
withManifests unique regs body = case manifestConstRegs unique regs of
    (Nothing, regs') => body regs'
    (Just code, regs') => code ++ (body regs')

withManifest : String -> CairoReg -> (CairoReg -> String) -> String
withManifest unique reg body = case manifestConstRegs unique [reg] of
    (Nothing, [reg]) => body reg
    (Just code, [reg]) => code ++ (body reg)
    _ => assert_total $ idris_crash "Can not happen"

castCustomRegs : List CairoReg -> List CairoReg -> (String, List String)
castCustomRegs src trg = foldl castReg ("",[]) (zip src trg)
    where cast : CairoReg -> CairoReg -> String -> String
          cast reg rReg typ = "let " ++ (regName rReg) ++ "_cast_ = cast(" ++ compileReg reg ++ "," ++ typ ++ ")\n"
          castReg : (String, List String) -> (CairoReg, CairoReg) -> (String, List String)
          castReg (code, regs) (reg@(CustomReg _ (Just t1)), rReg@(CustomReg _ (Just t2))) = (code ++ (cast reg rReg t2), regs ++ [(compileReg rReg) ++ "_cast_" ])
          castReg (code, regs) (reg, rReg@(CustomReg _ (Just typ))) = (code ++ (cast reg rReg typ), regs ++ [(compileReg rReg) ++ "_cast_" ])
          castReg (code, regs) (reg, _) = (code, regs ++ [compileReg reg])

-- used for Cairo functions in runtime_lib
defaultCodeGenInfo : LinearImplicitArgs -> List CairoReg -> CodeGenInfo
defaultCodeGenInfo linImpls args = MkCodeGenInfo (keys linImpls) (snd $ foldl (\(c,acc),_ => (c+1, acc++[Param c])) (0,[]) args)


-- Helper for compiling calls
compileCall : Name -> Maybe CodeGenInfo -> List CairoReg -> LinearImplicitArgs -> List CairoReg -> String
compileCall n Nothing rs linImpls args = compileCall n (Just $ defaultCodeGenInfo linImpls args) rs linImpls args
compileCall n (Just info) rs linImpls args = """
     \{ fst paramCasts }
     let (\{ regList }) = \{ cairoName n } (\{ paramList })
     \{ assigList }
     """
     where join : List String -> String
           join Nil = ""
           join (x::xs) = foldl1 (\s1,s2 => s1 ++ ", "++s2 ) (x::xs)
           manifestReg : CairoReg -> String
           manifestReg r@(CustomReg _ (Just _)) = (regName r) ++ "_cast_"
           manifestReg r = if isLocal r then (regName r) ++ "_tmp_" else regName r
           implList : List (CairoReg, CairoReg)
           implList = map (\i => fromMaybe (assert_total $ idris_crash "missing implicit") (lookup i linImpls)) (implicits info)
           joinedRs : List CairoReg
           joinedRs = rs ++ (map snd implList)
           regList : String
           regList = join (map manifestReg joinedRs)
           paramCasts : (String, List String)
           paramCasts = castCustomRegs args (params info)
           paramList : String
           paramList = showSep ", " ((map compileReg (map fst implList)) ++ (snd paramCasts))
           implRes : List CairoReg
           implRes = map fst implList
           isSpecial : CairoReg -> Bool
           isSpecial (CustomReg _ (Just _)) = True
           isSpecial r = isLocal r
           specialAssig : CairoReg -> String
           specialAssig r@(CustomReg _ (Just _)) = (compileRegDeclRef r) ++ " = " ++ (compileReg r) ++"_cast_\n" -- Cast case
           specialAssig r = (compileRegDeclDirect r) ++ " = " ++ (compileReg r) ++"_tmp_\n" -- Local case
           assigList : String
           assigList = concatMap specialAssig (filter isSpecial joinedRs)

compileConstructor : List String -> CairoReg -> String
compileConstructor values reg = """
 #MKCON
 tempvar \{ ptrName } = new ( \{ showSep ", " values } )
 \{ compileRegDeclRef reg } = cast(\{ ptrName },felt)

 """
    where ptrName : String
          ptrName = compileReg reg ++ "_ptr_" ++ show (length values)

mutual
     compileGeneralCase: String -> SortedMap Name CodeGenInfo -> RetInfo -> String -> String -> List CairoInst -> String -> String
     compileGeneralCase unique cInf ext value tagOrConst vminsts elseCase = """
        if \{ value } == \{ tagOrConst }:
            \{ compileCairoInsts unique cInf ext vminsts }
        else:
            \{ elseCase }
        end

        """

     compileCase : String -> SortedMap Name CodeGenInfo -> RetInfo -> CairoReg -> (Int, List CairoInst) -> String -> String
     compileCase unique cInf ext reg (tag, vminsts) elseCase = compileGeneralCase unique cInf ext ("[" ++ compileReg reg ++ "]") (show tag) vminsts elseCase
     compileCases :  String -> SortedMap Name CodeGenInfo -> RetInfo -> CairoReg -> List (Int, List CairoInst) -> Maybe (List CairoInst) -> String
     compileCases _ _ _ scr Nil Nothing = ""
     compileCases unique cInf ext scr Nil (Just def) = compileCairoInsts unique cInf ext def
     compileCases unique cInf ext scr ((_,cs)::Nil) Nothing = compileCairoInsts unique cInf ext cs
     compileCases unique cInf ext scr alts (Just def) = snd $ foldr (\c, (n, acc) => (n+1, compileCase (unique ++ "_" ++ (show n)) cInf ext scr c acc)) (1, compileCairoInsts (unique ++ "_0") cInf ext def) alts
     compileCases unique cInf ext scr ((_,cs)::alts) Nothing = snd $ foldr (\c, (n, acc) => (n+1, compileCase (unique ++ "_" ++ (show n)) cInf ext scr c acc)) (1, compileCairoInsts (unique ++ "_0") cInf ext cs) alts

     compileConstCase : String -> SortedMap Name CodeGenInfo -> RetInfo -> CairoReg -> (CairoConst, List CairoInst) -> String -> String
     compileConstCase unique cInf ext reg (constant, vminsts) elseCase = compileGeneralCase unique cInf ext (compileReg reg) (compileConst constant) vminsts elseCase
     compileConstCases : String -> SortedMap Name CodeGenInfo -> RetInfo ->  CairoReg -> List (CairoConst, List CairoInst) -> Maybe (List CairoInst) -> String
     compileConstCases _ _ _ reg Nil Nothing = ""
     compileConstCases unique cInf ext reg Nil (Just def) = compileCairoInsts unique cInf ext def
     compileConstCases unique cInf ext reg ((_,cs)::Nil) Nothing = compileCairoInsts unique cInf ext cs
     compileConstCases unique cInf ext reg alts (Just def) = snd $ foldr (\c, (n, acc) => (n+1, compileConstCase (unique ++ "_" ++ (show n)) cInf ext reg c acc)) (1, compileCairoInsts (unique ++ "_0") cInf ext def) alts
     compileConstCases unique cInf ext reg ((_,cs)::alts) Nothing = snd $ foldr (\c, (n, acc)  => (n+1, compileConstCase (unique ++ "_" ++ (show n)) cInf ext reg c acc)) (1, compileCairoInsts (unique ++ "_0") cInf ext cs) alts

     compileCairoInst : String -> SortedMap Name CodeGenInfo -> RetInfo -> CairoInst -> String
     compileCairoInst unique _ _ (ASSIGN r v') = withManifest unique v' (\v => "\{ compileRegDecl r } = \{ compileReg v }\n")
     -- Todo: Add Unpacked Versions (They are basically just multi assignes)
     compileCairoInst unique _ _ (MKCON r (Just t) args') = withManifests unique args' (\args => compileConstructor (show t :: map compileReg args) r)
     compileCairoInst unique _ _ (MKCON r Nothing args') = withManifests unique args' (\args => compileConstructor (show 0 :: map compileReg args) r)
     compileCairoInst unique _ _ (MKCLOSURE r n m args') = withManifests unique args' (genMkClosure unique r n m)

     -- Todo: This does not work with closures pointing to %foreign as the impl param order may be wrong
     --       However, Closure system needs overhaul or defunct anyway
     --       If we leave as is, we need to make wrappers for foreign closures that reorder implicit args if necessary
     compileCairoInst unique _ _ (APPLY r linImpls f a') = withManifest unique a' (genMkApply unique r linImpls f)
     compileCairoInst unique _ _ (MKCONSTANT r c) = assignConstReg r c
     compileCairoInst _ _ _ (STARKNETINTRINSIC r implicits (EventSelector name) []) = """
        # STARKNETINTRINSIC EventSelector
        let \{ resReg } = \{ cairoName name }.SELECTOR
        \{ if (isLocal r) then (compileRegDeclDirect r) ++ " = " ++ resReg else "" }
        """
        where resReg : String
              resReg = if isLocal r then (regName r) ++ "_tmp_" else regName r
     compileCairoInst _ _ _ (STARKNETINTRINSIC r implicits (StorageVarAddr name) []) = """
        # STARKNETINTRINSIC StorageVarAddr
        let pedersen_ptr_dummy_ = cast(0,HashBuiltin*)
        let range_check_ptr_dummy_ = 0
        let (\{ resReg }) = \{ cairoName name }.addr{pedersen_ptr=pedersen_ptr_dummy_, range_check_ptr=range_check_ptr_dummy_}()
        \{ if (isLocal r) then (compileRegDeclDirect r) ++ " = " ++ resReg else "" }
        """
        where resReg : String
              resReg = if isLocal r then (regName r) ++ "_tmp_" else regName r
     compileCairoInst _ _ _ (STARKNETINTRINSIC _ _ _ _) = assert_total $ idris_crash "Unsupported StarkNetIntrinsic Signature"
     compileCairoInst unique cInf _ (CALL rs linImpls n args') = withManifests unique args' (compileCall n (lookup n cInf) rs linImpls)
     -- compile primFns
     compileCairoInst unique cinf ext (OP r linImpls op args') = withManifests unique args'
        (\args => case generatePrimFnCode op unique r args linImpls of
            Instructions insts => compileCairoInsts unique cinf ext insts
            Raw code => code
        )
     compileCairoInst unique _ _ (EXTPRIM rs linImpls n args') = withManifests unique args' (externalCodeGen n rs linImpls)
     compileCairoInst unique cInf ext (CASE scr alts def) = compileCases unique cInf ext scr alts def
     compileCairoInst unique cInf ext (CONSTCASE src' alts def) = withManifest unique src' (\src => compileConstCases unique cInf ext src alts def)
     compileCairoInst unique _ (Internal retRegs) (RETURN rs' linImpls) = withManifests unique rs' genReturn
        where genReturn : List CairoReg -> String
              genReturn rs = """
                \{fst retCasts}
                return (\{join ((snd retCasts) ++ (map compileReg (values linImpls)))})
                """
                where join : List String -> String
                      join Nil = ""
                      join (x::xs) = foldl1 (\s1,s2 => s1 ++ ", "++s2 ) (x::xs)
                      retCasts : (String, List String)
                      retCasts = castCustomRegs rs retRegs
     compileCairoInst unique _ (External retRegs) (RETURN rs' linImpls) = withManifests unique rs' genReturn
        where genReturn : List CairoReg -> String
              genReturn rs = """
                \{concatMap implAssig (toList linImpls)}
                \{fst retCasts}
                return (\{join (snd retCasts)})
                """
                where join : List String -> String
                      join Nil = ""
                      join (x::xs) = foldl1 (\s1,s2 => s1 ++ ", "++s2 ) (x::xs)
                      implAssig : (LinearImplicit, CairoReg) -> String
                      implAssig (impl, reg) = "let " ++ implicitName impl ++ " = " ++ (compileReg reg) ++ "\n"
                      retCasts : (String, List String)
                      retCasts = castCustomRegs rs retRegs

     -- Project pos + 1 since pos + 0 is the tag
     compileCairoInst unique _ _ (PROJECT r val' pos) =  withManifest unique val' (\val => "\{ compileRegDecl r } = [\{ compileReg val } + \{ show (pos + 1) }]\n")
     compileCairoInst _ _ _ (NULL r ) = compileRegDeclDirect r ++ " = 0\n"
     compileCairoInst _ _ _ (ERROR r str) = impossibleCase r str

     compileCairoInsts : String -> SortedMap Name CodeGenInfo -> RetInfo -> List CairoInst -> String
     compileCairoInsts unique cInf ext insts = snd $ foldl (\(n,code), inst => (n+1, code ++ (compileCairoInst (unique ++ "_" ++ (show n)) cInf ext inst))) (0,"") insts

compileCairoDefBody : SortedMap Name CodeGenInfo -> RetInfo -> Name -> CairoDef -> List CairoInst -> String
compileCairoDefBody cInf ext name def body = """
       \{if isNil collectedLocals then "" else ("alloc_locals\n" ++ compiledLocals)}
       \{compileCairoInsts unique cInf ext body}
     """
     where collectedLocals : List CairoReg
           collectedLocals = toList $ collectLocals (name, def)
           compiledLocals : String
           compiledLocals = concatMap (\reg => "local " ++ (compileReg reg) ++ "\n") collectedLocals
           unique : String
           unique = (cairoName name) ++ "_" ++ "names_"


customRegCasts : List CairoReg -> String
customRegCasts = concatMap (customRegCast)
    where customRegCast : CairoReg -> String
          customRegCast r@(CustomReg _ (Just _)) = "let " ++ (compileReg r)  ++ " = cast(" ++ (paramRegName r) ++",felt)\n"
          customRegCast _ = ""

compileCairoDef : SortedMap Name CodeGenInfo -> Name -> CairoDef -> String
compileCairoDef cInf name def@(FunDef args linImplicits rets body) = let allArgs = ((values linImplicits) ++ args) in """
     func \{ cairoName name }(\{ showSep ", " (map paramReg allArgs)}) -> (\{ showSep ", " ((map paramReg rets) ++ (map implicitName (keys linImplicits))) }):
        \{customRegCasts allArgs}
        \{compileCairoDefBody cInf (Internal rets) name def body}
     end

     """
compileCairoDef cInf name def@(ExtFunDef tags args linImplicits rets body) = let implParams = values linImplicits in """
     # ExtFunDef
     \{concatMap (\t => "\n" ++ t) tags}
     func \{ cairoName name }{\{ showSep ", " (map paramReg implParams)}}(\{ showSep ", " (map paramReg args)})\{returnType}:
         \{customRegCasts (implParams ++ args)}
         \{compileCairoDefBody cInf (External rets) name def body}
     end

     """
     where 
       returnType : String
       returnType = case rets of
           [] => ""
           rs => " -> (\{ showSep ", "  (map paramReg rs) })"

compileCairoDef _ name (ForeignDef info _ _) = code info

extractKnownBuiltin : LinearImplicit -> List String
extractKnownBuiltin (MKLinearImplicit "bitwise_ptr") = ["bitwise"]
extractKnownBuiltin (MKLinearImplicit "pedersen_ptr") = ["pedersen"]
extractKnownBuiltin (MKLinearImplicit "output_ptr") = ["output"]
extractKnownBuiltin (MKLinearImplicit "range_check_ptr") = ["range_check"]
extractKnownBuiltin (MKLinearImplicit "ecdsa_ptr") = ["ecdsa"]
extractKnownBuiltin _ = []


extractExtImplicits : List (Name, CairoDef) -> List LinearImplicit
extractExtImplicits Nil = empty
extractExtImplicits ((name, (ExtFunDef _ _ impls _ _))::xs) = (extractExtImplicits xs) ++ (keys impls)
extractExtImplicits (def::xs) = extractExtImplicits xs

-- TODO Group by namespace, deduplicate functions names and generate mutli-imports
compileImports : SortedSet Import -> String
compileImports imports =
    showSep "\n" (map compileImport (toList imports))
  where compileImport : Import -> String
        compileImport (MkImport ns f Nothing) = "from " ++ ns ++ " import " ++ f
        compileImport (MkImport ns f (Just r)) = "from " ++ ns ++ " import " ++ f ++ " as " ++ r

builtinsPragma : List LinearImplicit -> String
builtinsPragma builtins = "%builtins " ++ showSep " " (builtins >>= extractKnownBuiltin)

addHeader : TargetType -> List (Name, CairoDef) -> SortedSet Import -> String -> String
addHeader targetType rawDefs imports defs =
    """
    \{ the String (case targetType of Cairo => builtinsPragma (extractExtImplicits rawDefs) ; StarkNet => "%lang starknet") }
    # Just to see if the skyro runtime library import works
    \{ compileImports imports }
    \{ label }
    \{ defs }
    """
    where label: String
          label = if imports == empty
            then "# HACK: The dw 0 is here because the programStart: label would not work without\ndw 0\nprogramStart:"
            else "programStart:"


collectImports : List (Name, CairoDef) -> SortedSet Import
collectImports cairocode = snd $ runVisitConcatCairoDefs (pureTraversal importTraversal) cairocode
    where importTraversal : InstVisit CairoReg -> SortedSet Import
          importTraversal (VisitMkCon _ _ _) = singleton (MkImport "starkware.cairo.common.alloc" "alloc" Nothing)
          importTraversal (VisitMkClosure _ _ _ _) = singleton (MkImport "starkware.cairo.common.alloc" "alloc" Nothing)
          importTraversal (VisitForeignFunction _ fi _ _) = fi.imports
          importTraversal (VisitExtprim _ _ name _) = externalImports name
          importTraversal (VisitStarkNetIntrinsic _ _ (StorageVarAddr _) _) = singleton (MkImport "starkware.cairo.common.cairo_builtins" "HashBuiltin" Nothing)
          importTraversal (VisitOp _ _ fn _) = primFnImports fn
          importTraversal _ = empty

export
generateCairoCode : TargetType -> List (Name, CairoDef) -> String
generateCairoCode targetType cairocode = addHeader targetType cairocode imports compiledDefs
    where cInf : SortedMap Name CodeGenInfo
          cInf = collectCodeGenInfo cairocode
          imports : SortedSet Import
          imports = collectImports cairocode
          compiledDefs : String
          compiledDefs = concatMap (\(name, cairodef) => compileCairoDef cInf name cairodef ++ "\n\n") cairocode
          
