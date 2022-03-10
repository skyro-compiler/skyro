module Optimisation.Inliner

import Data.SortedSet
import Data.SortedMap
import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Utils.Helpers
import CairoCode.Traversal.Base
import Optimisation.DeadCodeElimination

import Optimisation.StaticProcessing.IterativeBaseTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.OrderAndEliminateDefinitions
import CommonDef

import Debug.Trace

%hide Prelude.toList

isMachineName : Name -> Bool
isMachineName (NS _ innerName) = isMachineName innerName
isMachineName (PV innerName _)  = isMachineName innerName
isMachineName (DN _ innerName)  = isMachineName innerName
isMachineName (Nested _ innerName)  = isMachineName innerName
isMachineName (UN _ ) = False
isMachineName (MN _ _) = True
isMachineName _ = True

containsClosure : StaticInfo -> Bool
containsClosure (MKStaticInfo _ (Closure _ _)) = True
containsClosure (MKStaticInfo _ (Constructed inner)) = any (\infs => any containsClosure infs) (values inner)
containsClosure _ = False

inlineDecider : FunData -> Bool
inlineDecider (MKFunData name (FunDef _ _ _ _) _ _ args rs) = if name == cairo_main
    then True
    else (isMachineName name) || (any containsClosure (args ++ (map snd rs))) --  True

inlineDecider _ = False

inline : RegisterGen -> Name -> FunData -> (RegisterGen, List (InstVisit CairoReg))
inline regGen curName fd@(MKFunData name target@(FunDef params implsTrg _ insts) implsIn implsOut args rets) = (snd splitRegGen, returnElevated)
       where splitRegGen : (RegisterGen, RegisterGen)
             splitRegGen = splitRegisterGen regGen
             inlineRegGen : RegisterGen
             inlineRegGen = fst splitRegGen
             paramRegs : SortedMap CairoReg CairoReg
             paramRegs = fromList $ (zip params (map resolveInfToReg args))
                            ++ (map (\(impl,freg) => (freg, resolveImpl impl)) (toList $implsTrg))
                where resolveImpl : LinearImplicit -> CairoReg
                      resolveImpl lin = fromMaybe (assert_total $ idris_crash "Call is missing linear implicit param") (maybeMap resolveInfToReg (lookup lin implsIn))
             substituted : (Name, CairoDef)
             substituted = substituteDefRegisters subs (name, target)
                where subs : CairoReg -> Maybe CairoReg
                      subs (Const c) = Nothing
                      subs Eliminated = Nothing
                      subs reg = case lookup reg paramRegs of
                        (Just nReg) => Just nReg
                        Nothing => Just $ deriveRegister inlineRegGen reg
             -- todo: Note: For this to work our seamantics must be limited to have returns in tail positions
             --       - This holds for idris code
             --       - However, imperative programmers expect a different return semantic
             returnElevated : List (InstVisit CairoReg)
             returnElevated = snd $ runVisitConcatCairoDef (replaceReturn, ()) substituted
                where replaceReturn : InstVisit CairoReg ->  Traversal () (List (InstVisit CairoReg))
                      replaceReturn (VisitFunction _ _ _ _) = pure []
                      replaceReturn VisitEndFunction= pure []
                      replaceReturn (VisitReturn retRegs retImpls) = pure $ (zipWith (\a,r => VisitAssign (fst a) r) rets retRegs)  ++ map (\(lin,r) => VisitAssign (resolveImpl lin) r) (toList retImpls)
                        where resolveImpl : LinearImplicit -> CairoReg
                              resolveImpl lin = fromMaybe (assert_total $ idris_crash "Call is missing linear implicit return") (maybeMap fst (lookup lin implsOut))
                      replaceReturn inst = pure [inst]
inline regGen _ fd  = (regGen, genFunCall fd)

collectDependencies : (Name, CairoDef) -> SortedSet Name
collectDependencies def = snd $ runVisitConcatCairoDef (pureTraversal dependencyCollector) def
    where dependencyCollector : InstVisit CairoReg -> SortedSet Name
          dependencyCollector (VisitCall _ _ name _) = singleton name
          dependencyCollector _ = empty

isTerminal : (Name, CairoDef) -> Bool
isTerminal def = contains (fst def) (collectDependencies def)

localInlining : RegisterGen -> Name -> List (Name, CairoDef) -> List (Name, CairoDef)
localInlining regGen name allDefs = iterativeCallTransform regGen maybeInline cleanUp name allDefs
    where cleanUp : (Name, CairoDef) ->  (Name, CairoDef)
          cleanUp def = eliminateDeadCode $ localStaticOptimizeDef allDefs def
          maybeInline : RegisterGen -> Name -> FunData -> (RegisterGen, Maybe (List (InstVisit CairoReg)))
          maybeInline regGen intoName fd =  if isTerminal (fd.function, fd.target)
            then (regGen, Nothing)
            else if (inlineDecider fd)
                then let (nRegGen, res) = inline regGen intoName fd in (nRegGen, Just res)
                else (regGen, Nothing)

export
inlineDefs : Name -> List (Name, CairoDef) -> List (Name, CairoDef)
inlineDefs = localInlining (mkRegisterGen "inliner")

-- Note: even with Terminals we need still a upper limit because we mark funs with applies & MKClosures never as terminals
--       Further some crazy trampoline inlining could happen
