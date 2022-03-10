module RewriteRules.EqChainInline

import Data.SortedMap
import Data.SortedSet
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Core.Context
import Data.List
import CommonDef
import Primitives.Primitives

%hide Prelude.toList

-- Note: ValueTracker is not able to handle Case transforms so we use a direct version here
--       We cover not all cases as we want to detect and transform patterns and not do general optimisations
--       We assume that a constant fold has run before (otherwise it will not work with felts)
--       Currently code duplication is not limited
--        Todo: Build a limit
--        Todo: If limit reached do not do the transform or extract into Method

-- Transforms Boolean expressions with multiple if cascades into a single if cascade where possible
--   Or formulated otherwise:
--    fun x = if x == C1 || x == C2 then E1 else E2
--   Into:
--    fun C1 = E1
--    fun C2 = E1
--    fun _ = E2
-- The transformation is:
--  From: (Example has 2 sequntial ops where first has nesting 1 and second nesting 2 | However works for any number of sequential ops with any number of nesting)
--   a1 = p == C1
--   a2 = if a1 then True else p == C2
--   a3 = if a2 then E1 else E2
--  To:
--   a3 = if p == C1 then E1 else if p == C2 then E1 else E2

data ExtractedData : Type where
    ConstData : CairoConst -> ExtractedData
    OrEqChain : CairoReg -> List CairoConst -> ExtractedData

checkAndFilterReg : CairoReg -> Maybe (CairoReg, List CairoConst) -> Maybe (CairoReg, List CairoConst)
checkAndFilterReg _ Nothing = Nothing
checkAndFilterReg r1 res@(Just (r2, _)) = if r1 == r2 then res else Nothing

constEqLookup : CairoReg -> SortedMap CairoReg ExtractedData -> Maybe ExtractedData
constEqLookup (Const c) _ = Just $ ConstData c
constEqLookup r detection = lookup r detection

mutual
    analyzeMatchingCase : SortedMap CairoReg ExtractedData -> CairoReg -> List (CairoConst, List CairoInst) -> Maybe (List CairoInst) -> Maybe (CairoReg, List CairoConst)
    analyzeMatchingCase detection branchReg [(I 1,[MKCONSTANT tr (I 1)]),(I 0, [bF])] Nothing = checkAndFilterReg tr (analyzeFalseCase detection branchReg bF)
    analyzeMatchingCase detection branchReg [(I 0, [bF]),(I 1,[MKCONSTANT tr (I 1)])] Nothing = checkAndFilterReg tr (analyzeFalseCase detection branchReg bF)
    analyzeMatchingCase detection branchReg [(I 1,[MKCONSTANT tr (I 1)])] (Just [bF]) = checkAndFilterReg tr (analyzeFalseCase detection branchReg bF)
    analyzeMatchingCase detection branchReg [(I 0, [bF])] (Just [MKCONSTANT tr (I 1)]) = checkAndFilterReg tr (analyzeFalseCase detection branchReg bF)
    analyzeMatchingCase _ _ _ _ = Nothing

    analyzeFalseCase : SortedMap CairoReg ExtractedData -> CairoReg -> CairoInst -> Maybe (CairoReg, List CairoConst)
    analyzeFalseCase detection _ (MKCONSTANT tr (I 0)) = Just (tr, [])
    analyzeFalseCase detection branchReg (OP tr _ (EQ _) [a, b]) = if a == branchReg
        then process (constEqLookup b detection)
        else if b == branchReg
            then process (constEqLookup a detection)
            else Nothing
                where process : Maybe ExtractedData -> Maybe (CairoReg, List CairoConst)
                      process (Just (ConstData c)) = Just (tr, [c])
                      process _ = Nothing

    analyzeFalseCase detection branchReg (CONSTCASE r alts def) = process (constEqLookup r detection)
        where appendResult : List CairoConst -> Maybe (CairoReg, List CairoConst) -> Maybe (CairoReg, List CairoConst)
              appendResult cs (Just (resReg, cs2)) = Just (resReg, cs2 ++ cs)
              appendResult _ Nothing = Nothing
              process : Maybe ExtractedData -> Maybe (CairoReg, List CairoConst)
              process (Just (OrEqChain brReg cs)) = if branchReg == brReg
                then appendResult cs (analyzeMatchingCase detection branchReg alts def)
                else Nothing
              process _ = Nothing
    analyzeFalseCase _ _ _ = Nothing

analyzeCase : SortedMap CairoReg ExtractedData -> CairoInst -> SortedMap CairoReg ExtractedData
analyzeCase detection (CONSTCASE r alts def) = process (constEqLookup r detection)
    where buildResult : CairoReg -> List CairoConst -> Maybe (CairoReg, List CairoConst) -> SortedMap CairoReg ExtractedData
          buildResult brReg cs (Just (resReg, cs2)) = insert resReg (OrEqChain brReg (cs2 ++ cs)) detection
          buildResult _ _ Nothing = detection
          process : Maybe ExtractedData -> SortedMap CairoReg ExtractedData
          process (Just (OrEqChain brReg cs)) = buildResult brReg cs (analyzeMatchingCase detection brReg alts def)
          process _ = detection
analyzeCase detection _ = detection

mutual
    inlineOrEqChain : CairoInst -> SortedMap CairoReg ExtractedData -> (CairoInst, SortedMap CairoReg ExtractedData)
    inlineOrEqChain inst@(ASSIGN r s) detection = (inst, propagate $ constEqLookup s detection)
        where propagate : Maybe ExtractedData -> SortedMap CairoReg ExtractedData
              propagate Nothing = detection
              propagate (Just oec) = insert r oec detection

    inlineOrEqChain inst@(MKCONSTANT r c) detection = (inst, insert r (ConstData c) detection)
    inlineOrEqChain inst@(OP r _ (EQ _) [a, b]) detection = (inst, process (constEqLookup a detection) (constEqLookup b detection))
        where process : Maybe ExtractedData -> Maybe ExtractedData -> SortedMap CairoReg ExtractedData
              process (Just (ConstData (I 1))) (Just chain@(OrEqChain _ _)) = insert r chain detection
              process (Just chain@(OrEqChain _ _)) (Just (ConstData (I 1))) = insert r chain detection
              process (Just (ConstData c)) _ = insert r (OrEqChain b [c]) detection
              process _ (Just (ConstData c)) = insert r (OrEqChain a [c]) detection
              process _ _ = detection

    inlineOrEqChain inst@(OP r _ (BOr IntType) [a, b]) detection = (inst, process (constEqLookup a detection) (constEqLookup b detection))
        where process : Maybe ExtractedData -> Maybe ExtractedData -> SortedMap CairoReg ExtractedData
              process (Just (OrEqChain r1 c1)) (Just (OrEqChain r2 c2)) = if r1 == r2
                then insert r (OrEqChain r1 (c1 ++ c2)) detection
                else detection
              process _ _ = detection
    inlineOrEqChain (CASE r alts def) detection = (CASE r (map (\(i,b) => (i, processInsts detection b)) alts) (map (processInsts detection) def), detection)
    -- for safety as im unsure how ANF behaves in that case
    inlineOrEqChain (CONSTCASE r [(i,b)] Nothing) detection = (CONSTCASE r [(i, processInsts detection b)] Nothing, detection)
    inlineOrEqChain (CONSTCASE r [] (Just b)) detection = (CONSTCASE r [] (Just (processInsts detection b)), detection)
    inlineOrEqChain inst@(CONSTCASE r alts def) detection = (process (constEqLookup r detection), analyzeCase detection inst)
      where processedAlts : List (CairoConst, List CairoInst)
            processedAlts = map (\(c,b) => (c, processInsts detection b)) alts
            processedDef : Maybe (List CairoInst)
            processedDef = map (processInsts detection) def
            trueCase : List CairoInst
            trueCase = fromMaybe (fromMaybe (assert_total $ idris_crash "if without true case not allowed") def) (lookup (I 1) (fromList processedAlts))
            falseCase : List CairoInst
            falseCase = fromMaybe (fromMaybe (assert_total $ idris_crash "if without false case not allowed") def) (lookup (I 0) (fromList processedAlts))
            process : Maybe ExtractedData -> CairoInst
            -- Todo: add size limit on true but for that we need complexity/size functions
            process (Just (OrEqChain r2 cs)) = CONSTCASE r2 (map (\c => (c, trueCase)) (toList $ SortedSet.fromList cs)) (Just falseCase)
            process _ = CONSTCASE r processedAlts processedDef

    inlineOrEqChain inst detection = (inst, detection)

    processInsts: SortedMap CairoReg ExtractedData -> List CairoInst -> List CairoInst
    processInsts state insts = snd $ foldl (\(s,acc),i => let (ni,ns) = inlineOrEqChain i s in (ns, acc ++ [ni])) (state, []) insts


eqChainInlineDef : (Name, CairoDef) -> (Name, CairoDef)
eqChainInlineDef (name, FunDef params implicits rets body) = (name, FunDef params implicits rets (processInsts empty body))
eqChainInlineDef def = def

export
eqChainInline : List (Name, CairoDef) -> List (Name, CairoDef)
eqChainInline defs = map eqChainInlineDef defs
