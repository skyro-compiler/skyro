module CodeGen.CurryingBasedClosures

import Core.Name.Namespace
import Core.Context
import CodeGen.CodeGenHelper
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Data.SortedMap
import Data.SortedSet
import CommonDef
import CairoCode.Traversal.Base
import Utils.Helpers

%hide Prelude.toList

allClosures : List (Name, CairoDef) -> SortedMap Name Int
allClosures defs = snd $ runVisitConcatCairoDefs (pureTraversal closureInfoTraversal) defs
    where closureInfoTraversal : InstVisit CairoReg -> SortedMap Name Int
          closureInfoTraversal (VisitMkClosure _ name missing _) = singleton name (cast missing)
          closureInfoTraversal _ = empty
          Semigroup Int where (<+>) = min

extractOrderedImpls : CairoDef -> List LinearImplicit
extractOrderedImpls (FunDef _ impls _ _) = keys impls
extractOrderedImpls (ExtFunDef _ _ impls _ _) = keys impls
extractOrderedImpls (ForeignDef (MkForeignInfo _ _ impls _ _) _ _) = impls

extractImpls : (Name, CairoDef) -> (Name, SortedSet LinearImplicit)
extractImpls (n, def) = (n, fromList $ extractOrderedImpls def)

extractClosureImplicits : List (Name, CairoDef) -> SortedSet LinearImplicit
extractClosureImplicits defs = snd $ runVisitConcatCairoDefs (pureTraversal closureImplicitsTraversal) defs
    where implicitLookup : SortedMap Name (SortedSet LinearImplicit)
          implicitLookup = fromList $ map extractImpls defs
          closureImplicitsTraversal : InstVisit CairoReg -> SortedSet LinearImplicit
          closureImplicitsTraversal (VisitMkClosure _ name _ _) = fromMaybe empty (lookup name implicitLookup)
          closureImplicitsTraversal _ = empty

deriveCurriedClosureName : Name -> Int -> Name
deriveCurriedClosureName name miss = MN ("curried__"++(cairoName name)) miss

generateCurriedBody : SortedMap LinearImplicit CairoReg -> Name -> Int -> List CairoInst
generateCurriedBody outerImpls callTarget params = projects ++ [MKCLOSURE retReg callTarget 1 (paramRegs ++ [(Param 1)]), RETURN [retReg] outerImpls]
    where retReg : CairoReg
          retReg = Unassigned (Just "ret") 0 0
          paramRegs : List CairoReg
          paramRegs = map (\r => Unassigned (Just "arg") r 0) (fromZeroTo (params - 1))
          projects : List CairoInst
          projects = zipWith (\r,i => PROJECT r (Param 0) (cast i)) paramRegs (fromZeroTo (params - 1) )

generateCallBody : SortedMap LinearImplicit CairoReg -> SortedSet LinearImplicit -> Name -> Int -> List CairoInst
generateCallBody outerImpls innerImpls callTarget params = projects ++ [CALL retRegs implRegs callTarget (paramRegs ++ [(Param 1)]), RETURN retRegs retImpls]
    where retRegs : List CairoReg
          retRegs = [Unassigned (Just "ret") 0 0]
          implRegs : SortedMap LinearImplicit (CairoReg,CairoReg)
          implRegs = mapMap (\(k,v) => (k, (v,Unassigned (Just (implicitName k)) 0 0))) (keyFilter (\k => contains k innerImpls) outerImpls)
          retImpls : SortedMap LinearImplicit CairoReg
          retImpls = foldl (\acc,(i,(_,r)) => insert i r acc) outerImpls (toList implRegs)
          paramRegs : List CairoReg
          paramRegs = map (\r => Unassigned (Just "arg") r 0) (fromZeroTo (params - 1))
          projects : List CairoInst
          projects = zipWith (\r,i => PROJECT r (Param 0) (cast i)) paramRegs (fromZeroTo (params - 1) )

generateClosureWrapperDefs : SortedSet LinearImplicit -> ((Name, CairoDef), Int) -> List (Name, CairoDef)
generateClosureWrapperDefs impls ((name, FunDef params callImpls [_] _), 1) = (deriveCurriedClosureName name 1, FunDef [Param 0, Param 1] nImpls [CustomReg "applied_ret" Nothing] body)::Nil
   where nImpls : SortedMap LinearImplicit CairoReg
         nImpls = fromList $ map (\i => (i, implicitReg i)) (toList impls)
         body : List CairoInst
         body = generateCallBody nImpls (fromList $ keys callImpls) name ((cast $ length params) - 1)

generateClosureWrapperDefs impls (def@(name, FunDef params callImpls [_] _), n) = (deriveCurriedClosureName name n, FunDef [Param 0, Param 1] nImpls [CustomReg "applied_ret" Nothing] body)::(generateClosureWrapperDefs impls (def, n-1))
   where nImpls : SortedMap LinearImplicit CairoReg
         nImpls = fromList $ map (\i => (i, implicitReg i)) (toList impls)
         body : List CairoInst
         body = generateCurriedBody nImpls (deriveCurriedClosureName name (n-1)) ((cast $ length params) - n)

generateClosureWrapperDefs impls ((name, ForeignDef (MkForeignInfo _ _ callImpls _ _) params 1), 1) =  (deriveCurriedClosureName name 1, FunDef [Param 0, Param 1] nImpls [CustomReg "applied_ret" Nothing] body)::Nil
    where nImpls : SortedMap LinearImplicit CairoReg
          nImpls = fromList $ map (\i => (i, implicitReg i)) (toList impls)
          body : List CairoInst
          body = generateCallBody nImpls (fromList callImpls) name ((cast params) - 1)

generateClosureWrapperDefs impls (def@(name, ForeignDef (MkForeignInfo _ _ callImpls _ _) params 1), n) =  (deriveCurriedClosureName name n, FunDef [Param 0, Param 1] nImpls [CustomReg "applied_ret" Nothing] body)::(generateClosureWrapperDefs impls (def, n-1))
    where nImpls : SortedMap LinearImplicit CairoReg
          nImpls = fromList $ map (\i => (i, implicitReg i)) (toList impls)
          body : List CairoInst
          body = generateCurriedBody nImpls (deriveCurriedClosureName name (n-1)) ((cast params) - n)

generateClosureWrapperDefs _ ((_, ExtFunDef _ _ _ _ _), _) = assert_total $ idris_crash "ClosureGen: Closure targets can not be external"
generateClosureWrapperDefs impls _ = assert_total $ idris_crash "ClosureGen: Closure targets must return a single value"

generateClosureWrappers : SortedSet LinearImplicit -> List (Name, CairoDef) -> List (Name, CairoDef)
generateClosureWrappers impls defs = affectedFunctions >>= (generateClosureWrapperDefs impls)
    where affectedFunctions : List ((Name, CairoDef), Int)
          affectedFunctions = map (\(n,m) => ((n, resolveDef n),m)) (toList $ allClosures defs)
            where defLookup : SortedMap Name CairoDef
                  defLookup = fromList defs
                  resolveDef : Name -> CairoDef
                  resolveDef name = fromMaybe (assert_total $ idris_crash "Currying: Should not happen") (lookup name defLookup)


replaceClosureTarget : List (Name, CairoDef) -> List (Name, CairoDef)
replaceClosureTarget defs = snd $ runVisitTransformCairoDefs (pureTraversal rewireTransform) defs
    where rewireTransform : InstVisit CairoReg -> List (InstVisit CairoReg)
          rewireTransform inst@(VisitMkClosure res name miss args) = [VisitMkClosure res (deriveCurriedClosureName name (cast miss)) 1 args]
          rewireTransform inst = [inst]



export
preprocessClosures : List (Name, CairoDef) -> List (Name, CairoDef)
preprocessClosures cairocode = (generateClosureWrappers impls cairocode) ++ nCairoCode
    where impls : SortedSet LinearImplicit
          impls = extractClosureImplicits cairocode
          nCairoCode : List (Name, CairoDef)
          nCairoCode = replaceClosureTarget cairocode


export
genMkClosure : String -> (res:CairoReg) -> Name -> (missing : Nat) -> (args : List CairoReg) -> String
genMkClosure unique reg name 1 args = """
    #MKCLOSURE
    const \{ targetAddr } = \{ targetName } - programStart
    tempvar \{ ptrName } = new ( \{ showSep ", " (targetAddr::(map compileReg args)) }  )
    \{ compileRegDeclRef reg } = cast(\{ ptrName },felt)

    """
    where targetName : String
          targetName = cairoName name
          targetAddr : String
          targetAddr = unique ++ "_addr_"
          ptrName : String
          ptrName = compileReg reg ++ "_ptr_" ++ show (length args)
-- if compileRegDeclRef not works with cast then use \{ compileRegDecl reg } = cast(\{ compileReg reg }_ptr_,felt)


genMkClosure _ _ name _ _ = assert_total $ idris_crash "CurriedClosureGen: Target \{cairoName name} is not in curried form"


-- Todo: if jmpPointName is twice the same it fails
--       it seems that this worked earlier just like const (maybe their was a cairo change)
--   Hack - fix implemented by using all avaiable infos
--   For real fix a unique string needs to be passed in
export
genMkApply : String -> (res:CairoReg) -> LinearImplicitArgs -> (f : CairoReg) -> (a : CairoReg) -> String
genMkApply unique r impls f a = """
    #APPLY closure
    \{ fst mf } tempvar dispatcher = [\{ snd mf }] - (\{jmpPointName} - programStart)
    \{ fst ma } \{concatMap fst mImpls}
    \{ concatMap (\(_,r) => "[ap] = \{ r } ; ap++\n") mImpls}
    [ap] = \{ snd mf }; ap++
    [ap] = \{ snd ma }; ap++
    \{jmpPointName}:
    call rel dispatcher
    \{ compileRegDeclRef r ++ " = [ap-" ++ show (1+numImpls) ++ "]" }
    \{ rImpls }
    """
    where jmpPointName : String
          jmpPointName = unique ++ "_jumpPoint_"
          mf : (String, String)
          mf = ensureManifested f "closure"
          ma : (String, String)
          ma = ensureManifested a "argument"
          mImpls : List (String, String)
          mImpls = map (\(i,(f,_)) => ensureManifested f ("manifest_"++(implicitName i)++"_")) (toList impls)
          numImpls : Int
          numImpls = cast $ length mImpls
          rImpls : String
          rImpls = snd $ foldl (\(idx,acc),(_,r) => (idx-1, acc ++ (compileRegDeclRef r) ++ " = [ap-" ++ show idx ++ "]\n") ) (numImpls,"") (values impls)

