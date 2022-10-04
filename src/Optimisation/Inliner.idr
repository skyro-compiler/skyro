module Optimisation.Inliner

import Data.SortedSet
import Data.SortedMap
import Data.List
import Data.Maybe
import Data.String

import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Utils.Helpers
import CairoCode.Traversal.Base
import Optimisation.DeadCodeElimination
import RewriteRules.TailBranchFolder

import Optimisation.StaticProcessing.IterativeBaseTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.OrderAndEliminateDefinitions
import CommonDef

import Debug.Trace

%hide Prelude.toList

inline : RegisterGen -> Int -> CairoName -> FunData -> (RegisterGen, Maybe (List (InstVisit CairoReg)))
inline regGen inlineDepth curName fd@(MKFunData name target@(FunDef params implsTrg _ insts) implsIn implsOut args rets) = (snd splitRegGen, Just returnElevated)
       where splitRegGen : (RegisterGen, RegisterGen)
             splitRegGen = splitRegisterGen regGen
             substituted : (CairoName, CairoDef)
             substituted = let paramRegs = fromList $ (zip params (map resolveInfToReg args)) ++ (map (\(impl,freg) => (freg, resolveImplIn impl)) (toList implsTrg)) in
                substituteDefRegisters (subs (fst splitRegGen) paramRegs) (name, target)
                where resolveImplIn : LinearImplicit -> CairoReg
                      resolveImplIn lin = fromMaybe (assert_total $ idris_crash "Call is missing linear implicit param") (maybeMap resolveInfToReg (lookup lin implsIn))
                      increaseDepth : CairoReg -> CairoReg
                      increaseDepth (Unassigned p i d) = (Unassigned p i (d+inlineDepth))
                      -- Inliner Should run after RegAlloc so this should not happen
                      increaseDepth (Local i d) = (Local i (d+inlineDepth))
                      increaseDepth (Let i d) = (Let i (d+inlineDepth))
                      increaseDepth (Temp i d) = (Temp i (d+inlineDepth))
                      increaseDepth r = r
                      subs : RegisterGen -> SortedMap CairoReg CairoReg -> CairoReg -> Maybe CairoReg
                      subs _ _ (Const c) = Nothing
                      subs regGen paramRegs (Eliminated (Replacement reg)) = case (subs regGen paramRegs reg) of
                        (Just nReg@(Eliminated _)) => Just nReg
                        (Just nReg) => Just $ Eliminated (Replacement nReg)
                        Nothing => Nothing
                      subs _ _ (Eliminated _) = Nothing
                      subs regGen paramRegs reg = case lookup reg paramRegs of
                        Nothing => Just $ increaseDepth $ deriveRegister regGen reg
                        nReg => nReg
             -- todo: Note: For this to work our seamantics must be limited to have returns in tail positions
             --       - This holds for idris code
             --       - However, imperative programmers expect a different return semantic
             returnElevated : List (InstVisit CairoReg)
             returnElevated = snd $ runVisitConcatCairoDef (replaceReturn, ()) substituted
                where replaceReturn : InstVisit CairoReg ->  Traversal () (List (InstVisit CairoReg))
                      replaceReturn (VisitFunction _ _ _ _ _) = pure []
                      replaceReturn VisitEndFunction = pure []
                      replaceReturn (VisitReturn retRegs retImpls) = pure $ (zipWith (\a,r => VisitAssign (fst a) r) rets retRegs) ++ map (\(lin,r) => VisitAssign (resolveImplOut lin) r) (toList retImpls)
                        where resolveImplOut : LinearImplicit -> CairoReg
                              resolveImplOut lin = fromMaybe (assert_total $ idris_crash "Call is missing linear implicit return") (maybeMap fst (lookup lin implsOut))
                      replaceReturn inst = pure [inst]
inline regGen _ _ fd  = (regGen, Nothing)



-- Note: This replaces old cycle prevention
--       Currently the algorithm is recomputed after each inlining pass
--       Thus this sadly makes this O(n^2) [n = instructions] -- However in reality n is more likely to be near the number of functions (unless each instruction is a Call)
--       If this is a performance problem:
--          1. Have an edge set (all edges that where in call graph when coloring was made)
--          2. After inlining update the edge set add the edges from the inlined to the inliner
--          3. If an inline attempt is made inline X into Y and their is no edge (X,Y), recompute Colorgraph & edge Map
--        Note: This is still not linear but still way better (I do not think we can get better than that with the current algorithm)
--          However: the concrete complexity is not obvious to me maybe worst case still O(n^2) but if so even less likely then before

Color: Type
Color = Int

record GraphInfo where
    constructor MkGraphInfo
    cycleColor : SortedSet Color
    callHeight : Int -- we use -1 as in progress marker: Further this gives a nice 0 if incremented by 1 so cycle start with depth 0

Show GraphInfo where
    show (MkGraphInfo c1 h1) = "GraphInfo: "++(show c1)++" - "++ (show h1)

Semigroup GraphInfo where
    (<+>) (MkGraphInfo c1 h1) (MkGraphInfo c2 h2) = MkGraphInfo (foldl (\acc, e => insert e acc) c1 c2) (max h1 h2)

Monoid GraphInfo where
    neutral = MkGraphInfo empty 0

traverseGraph : Color -> SortedMap CairoName GraphInfo -> SortedMap CairoName CairoDef -> (CairoName, CairoDef) -> (GraphInfo , (Color, SortedMap CairoName GraphInfo))
traverseGraph colorGen inf _ def@(curName, ForeignDef _ _ _) = (neutral, (colorGen, insert curName neutral inf))
traverseGraph colorGen inf allDefs def@(curName,_) = case lookup curName inf of
        -- not yet processed node
        Nothing => let (nColorGen, preColor) = (colorGen+1, colorGen) in
                   let recSaveInf = insert curName (MkGraphInfo (singleton preColor) (-1)) inf in
                   let (afterColorGen, MkGraphInfo c d, finalInf) = foldl dependencyCollector (nColorGen, neutral, recSaveInf) (fromCairoDef def) in
                   let (afterInfo, postInfo) = (MkGraphInfo c (d+1), MkGraphInfo (delete preColor c) (d+1)) in
                   (postInfo, (afterColorGen, insert curName afterInfo finalInf))
        -- we detected a cycle
        (Just gInf@(MkGraphInfo c (-1))) => (gInf,(colorGen,inf))
        -- already finished node
        (Just _) => (neutral,(colorGen,inf))

    where dependencyCollector : (Color, GraphInfo, SortedMap CairoName GraphInfo) -> InstVisit CairoReg -> (Color, GraphInfo, SortedMap CairoName GraphInfo)
          dependencyCollector (colorGen, accInfo, cInf) (VisitCall _ _ name _) = case lookup name allDefs of
            Nothing => trace "Ups how can this happen" (colorGen, accInfo, cInf)
            (Just cDef) => let (gInf, (nCGen, nInf)) = traverseGraph colorGen cInf allDefs (name, cDef) in (nCGen, accInfo <+> gInf, nInf)
          dependencyCollector state _ = state

collectGraphInfo : SortedMap CairoName CairoDef -> SortedMap CairoName GraphInfo
collectGraphInfo allDefs = snd $ foldl traverseGraphHead (0, empty) (toList allDefs)
    where traverseGraphHead : (Color, SortedMap CairoName GraphInfo) -> (CairoName, CairoDef) -> (Color, SortedMap CairoName GraphInfo)
          traverseGraphHead (colorGen, inf) def = snd $ traverseGraph colorGen inf allDefs def

isRecursiveSave : SortedMap CairoName GraphInfo -> CairoName -> CairoName -> Bool
isRecursiveSave inf into from = case (lookup into inf, lookup from inf) of
    (Just (MkGraphInfo c1 h1), Just (MkGraphInfo c2 h2)) => c2 == empty || (intersection c1 c2 /= empty && h1 > h2)
    _ => False

-- Note: This was performant.
--  However:
--      1. Results could be suboptimal - resulting in semi inlined semi duplicated recursive functions
--      2. Require that a topological orderer did run before the inline pass
--      3. Are decider sensitive and a custom decider (like the one from apply_outline) could in theory run endlessly
-- isRecursiveSave : CairoName -> CairoName -> Bool
-- isRecursiveSave into from = into /= from

public export
InlineDecider : Type
InlineDecider = SortedMap CairoName CairoDef -> CairoName -> FunData -> Bool

-- Safety Measure against infinite loop Bugs
-- And allows to test stuff & find them
-- A finished Product should not need this
inlineThreshold : Nat
inlineThreshold = 0

underLimit : Nat -> Bool
underLimit n = if n < inlineThreshold || inlineThreshold == Z   -- We use Z to signale disabling of this feature
    then True
    else trace "Inline Limit Reached" False

recollectCollectGraphInfo : SortedMap CairoName GraphInfo ->  SortedMap CairoName CairoDef -> (CairoName, CairoDef) -> (CairoName, CairoDef) -> SortedMap CairoName GraphInfo
recollectCollectGraphInfo _ curDefs _ (name,def) = collectGraphInfo (insert name def curDefs)
{-
-- As it runs on every inline this can lead to a O(n^2) complexity as itself is already O(n)
-- Todo: This probably needs some updating of the graph to remove the inlined edge -- as it is just performance this is delayed
recollectCollectGraphInfo oldGraphInfo curDefs oDef nDef = if (collectDependency oDef) /= (collectDependency nDef)
            then collectGraphInfo (insert (fst nDef) (snd nDef) curDefs)
            else oldGraphInfo
    where dependencyCollector : InstVisit CairoReg -> SortedSet CairoName
          dependencyCollector (VisitCall _ _ name _) = singleton name
          dependencyCollector _ = empty
          -- Note: The Idris default implementation is slow, this is faster in the cases where it matters
          Semigroup (SortedSet CairoName) where
              (<+>) a b = if a == b
                  then a
                  else foldl (\acc, e => insert e acc) a b
          collectDependency : (CairoName, CairoDef) -> SortedSet CairoName
          collectDependency def = snd $ runVisitConcatCairoDef (pureTraversal dependencyCollector) def
-}

localInlining : Bool -> InlineDecider -> RegisterGen -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
localInlining tailBranchingActive inlineDecider regGen allDefs = iterativeCallTransform @{config} (regGen, (collectGraphInfo (fromList allDefs)), Z) allDefs
    where [config] IterativeTransformerConf (RegisterGen,  SortedMap CairoName GraphInfo, Nat) where
                cleanUp (rg, gInf, c) curDefs def = let tailDef = if tailBranchingActive then tailBranchDef def else def in
                    let nDef = eliminateDeadCode $ localStaticOptimizeDef' (insert (fst tailDef) (snd tailDef) curDefs) tailDef in
                    ((rg, recollectCollectGraphInfo gInf curDefs def nDef, c), nDef)
                funTransformer (rg, gInf, c) curDefs depth intoName fd = if (underLimit c) && (isRecursiveSave gInf intoName fd.function) && (inlineDecider curDefs intoName fd)
                    then let (nRegGen, res) = inline rg depth intoName fd in ((nRegGen,gInf, S c), (res,Nil))
                    else ((rg, gInf, c), (Nothing,Nil))

export
containsClosure : StaticInfo -> Bool
containsClosure (MKStaticInfo _ (Closure _ _)) = True
containsClosure (MKStaticInfo _ (Constructed inner)) = any (any containsClosure) (values inner)
containsClosure _ = False

-- Somehow Elab makes problem if we gen Machine generated names
--  As alternative we treat some namespaces as if they were machine generated
--  A real inline decider in the end will be more elaborate then on a per name basis anyway (so just temp)
isSpecialNamespace : CairoName -> Bool
isSpecialNamespace name = ["Main","ABI","Wrapper"] `isPrefixOf` (extractNamespace name)

isConstant : StaticInfo -> Bool
isConstant (MKStaticInfo _ (Const values)) = case (toList values) of
    [value] => True
    _ => False -- has more than one possible value
isConstant (MKStaticInfo _ (Constructed ctrs)) = case (values ctrs) of
    [fields] => all isConstant fields
    _ => False -- has more than one possible constructor
isConstant (MKStaticInfo _ (Closure (Just (name, miss)) args)) = all isConstant args
isConstant (MKStaticInfo _ (Field src (Just t) p)) = isConstant src -- if src is constant this should already have been resolved
isConstant _ = False

-- A good one would need a size metric instead of counting all as one
-- This is just some feel good metric
-- Todo: Make Configurable
smallInlineLimit : Nat -> Nat -> Nat
smallInlineLimit nargs nrs = 2*(nargs+nrs)+2

-- tail rec version (where possible)
fullSizeRec : Nat -> List CairoInst -> Nat
fullSizeRec acc Nil = acc
fullSizeRec acc ((CASE _ alts Nothing)::rest) = fullSizeRec (foldl fullSizeRec (acc+1) (map snd alts)) rest
fullSizeRec acc ((CASE _ alts (Just def))::rest) = fullSizeRec (foldl fullSizeRec (fullSizeRec (acc+1) def) (map snd alts)) rest
fullSizeRec acc ((CONSTCASE _ alts Nothing)::rest) = fullSizeRec (foldl fullSizeRec (acc+1) (map snd alts)) rest
fullSizeRec acc ((CONSTCASE _ alts (Just def))::rest) = fullSizeRec (foldl fullSizeRec (fullSizeRec (acc+1) def) (map snd alts)) rest
fullSizeRec acc (x::rest) = fullSizeRec (acc+1) rest

fullSize : List CairoInst -> Nat
fullSize ls = fullSizeRec 0 ls



eagerMachineInlineDecider : Maybe Nat -> SortedMap CairoName Nat -> SortedMap CairoName CairoDef -> CairoName -> FunData -> Bool
eagerMachineInlineDecider sizeLimit counts allDefs intoName (MKFunData name (FunDef _ impls _ body) appliedImpls _ args rs) = if (keys impls) /= (keys appliedImpls)
        then False
        else limitCheck && (isGenerated || hasClosureArgs || argsAreConstant || isSingleUse || isSmall)
    where isGenerated : Bool
          isGenerated = isMachineGenerated name || isSpecialNamespace name
          hasClosureArgs : Bool
          hasClosureArgs = any containsClosure (args ++ (map snd rs))
          argsAreConstant : Bool
          argsAreConstant = all isConstant args
          isSmall : Bool
          isSmall = (fullSize body) <= smallInlineLimit (length args) (length rs)
          isSingleUse : Bool
          isSingleUse = lookup name counts == (Just 1)
          limitCheck : Bool
          limitCheck = case (sizeLimit, lookup intoName allDefs) of
            (Just limit, Just (FunDef _ _ _ outerBody)) => fullSize outerBody <= limit
            (Just limit, Just (ExtFunDef _ _ _ _ outerBody)) => fullSize outerBody <= limit
            _ => False
eagerMachineInlineDecider _ _ _ _ _ = False

saveInlineDecider : SortedMap CairoName Nat -> SortedMap CairoName CairoDef -> CairoName -> FunData -> Bool
saveInlineDecider counts _ intoName (MKFunData name (FunDef _ impls _ body) appliedImpls _ args rs) = if (keys impls) /= (keys appliedImpls)
    then False
    else (isSingleUse || isSmall)
    where isSmall : Bool
          isSmall = (fullSize body) <= smallInlineLimit (length args) (length rs)
          isSingleUse : Bool
          isSingleUse = lookup name counts == (Just 1)

saveInlineDecider _ _ _ _ = False

countUsages : List (CairoName, CairoDef) -> SortedMap CairoName Nat
countUsages defs = snd $ runVisitConcatCairoDefs (pureTraversal amountCollector) defs
    where amountCollector : InstVisit CairoReg -> SortedMap CairoName Nat
          amountCollector (VisitCall _ _ name _) = singleton name 1
          amountCollector (VisitMkClosure _ name _ _) = singleton name 1
          amountCollector _ = empty
          Semigroup Nat where (<+>) = (+)
          Monoid Nat where neutral = 0

export
inlineCustomDefs : Bool -> InlineDecider -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
inlineCustomDefs tailBranchingActive decider defs = localInlining tailBranchingActive decider (mkRegisterGen "inliner") (map orderUnassignedRegIndexes defs)

export
inlineDefs : Maybe Nat -> Bool -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
inlineDefs sizeLimit tailBranchingActive defs = let decider = eagerMachineInlineDecider sizeLimit (countUsages defs) in inlineCustomDefs tailBranchingActive decider defs

export
inlineSaveDefs : Bool ->  List (CairoName, CairoDef) -> List (CairoName, CairoDef)
inlineSaveDefs tailBranchingActive defs = let decider = saveInlineDecider (countUsages defs) in inlineCustomDefs tailBranchingActive decider defs

