module RewriteRules.ApplyShift

import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Maybe
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CairoCode.Name
import CommonDef
import Utils.Helpers
import CairoCode.Traversal.Base
import Optimisation.OrderAndEliminateDefinitions
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.StaticProcessing.IterativeBaseTransformer
import Optimisation.DeadCodeElimination
import Optimisation.Inliner

import Debug.Trace

%hide Prelude.toList

-- The prime purpose of this is to optimize Monadic expressions
--  as well as similar patterns that return computations instead of executing them directly
--  this is superior to just inlining as it can handle recursive monadic expressions which inlining can not
--  It is based on inlining, but transforms returned computations into direct executions to create more optimisation oppertunities

-- Note: This is quite sensitive as it requires the clearly visible structures
--          Thus it should run after the primary inlining and after the dead data, dead argument & spezialiser
--          However, it can not handle implicits and tuples (yet) thus should run before them

-- Some Monadic Computations end up with large Closure chains
--  Sometimes Idris does shift the application into the body
--  Sometimes it does not (for these cases we do it)
--   Without this monadic recursive expressions can get ugly
-- Moves Applies on a Call result into the Call (enables optimisation)
--   Transforms:
--    x = name(...)         //Only if name has no impls & x is used exactly once (in r = x a)
--    r = x a
--   Into:
--    r = shift_name(...,a) <-- shift_name is derived from name
--   Where:
--    shift_name(...,a) has same code as name but:
--        return x
--      is replaced with:
--        r = x a
--        return r
-- Then: does static optimization + inlining and repeats the process

shiftName : CairoName -> CairoName
shiftName = incrementalExtendName "argument_shifted"

findCandidates : CairoName -> List (InstVisit CairoReg) -> SortedMap CairoName (SortedSet CairoReg)
findCandidates ctxName = search empty
    where recordCandidate : CairoName -> CairoReg -> SortedMap CairoName (SortedSet CairoReg) -> SortedMap CairoName (SortedSet CairoReg)
          recordCandidate name reg cands = case lookup name cands of
            Nothing => insert name (singleton reg) cands
            (Just regs) => insert name (insert reg regs) cands
          search : SortedMap CairoName (SortedSet CairoReg) -> List (InstVisit CairoReg) -> SortedMap CairoName (SortedSet CairoReg)
          -- Todo: extend to multi return:
          --   1 allows this to be used after untupling
          --   2 allows this to be used if source lang has multi return

          -- this case is necessary to prevent endless loop
          search acc ((VisitCall [r] impls1 name _)::(VisitApply r2 impls2 f _)::(VisitReturn [r3] _)::rest) = if impls1 == empty && impls2 == empty && r == f && (r2 /= r3 || (shiftName name) == ctxName)
            then search (recordCandidate name r acc) rest
            else search acc rest
          search acc ((VisitCall [r] impls1 name _)::(VisitApply _ impls2 f _)::rest) = if impls1 == empty && impls2 == empty && r == f
            then search (recordCandidate name r acc) rest
            else search acc rest
          search acc ((VisitCall _ _ _ _)::(VisitApply _ _ _ _)::rest) = search acc (trace "Missed due to multi return" rest)
          -- this is reenebales corner cases that would be missed do to endless loop prevention helper
          search acc ((VisitMkClosure r1 _ _ _)::(VisitReturn [r2] _)::rest) = if r1 == r2
            then search (recordCandidate ctxName r1 acc) rest
            else search acc rest
          search acc (x::xs) = search acc xs
          search acc Nil = acc

-- todo: shall we use generalized traversal here
-- This counts the usages of the registers to make sure it is not used anywhere else (as it will vanish)
validateCandidate : List (InstVisit CairoReg) -> (CairoName, (SortedSet CairoReg)) -> (CairoName, SortedSet CairoReg)
validateCandidate body (name, regs) = (name, fromList $ keys $ valueFilter (==1) (foldl checkInst empty body))
    where checkReg : SortedMap CairoReg Int -> CairoReg -> SortedMap CairoReg Int
          checkReg count reg = if contains reg regs
            then case lookup reg count of
                Nothing => insert reg 1 count
                (Just c) => insert reg (c+1) count
            else count
          checkRegs : SortedMap CairoReg Int -> List CairoReg -> SortedMap CairoReg Int
          checkRegs count regs = foldl checkReg count regs
          -- todo: this would be simpler with a generalizer
          checkInst : SortedMap CairoReg Int -> InstVisit CairoReg -> SortedMap CairoReg Int
          checkInst count (VisitAssign _ a) = checkReg count a
          checkInst count (VisitMkCon _ _ args) = checkRegs count args
          checkInst count (VisitMkClosure _ _ _ args) = checkRegs count args
          checkInst count (VisitApply _ _ f a) = checkRegs count [f,a]
          checkInst count (VisitCall _ _ _ args) = checkRegs count args
          checkInst count (VisitOp _ _ _ args) = checkRegs count args
          checkInst count (VisitExtprim _ _ _ args) = checkRegs count args
          checkInst count (VisitStarkNetIntrinsic _ _ _ args) = checkRegs count args
          checkInst count (VisitCase a) = checkReg count a
          checkInst count (VisitProject _ a _) = checkReg count a
          checkInst count (VisitReturn args _) = checkRegs count args
          checkInst count _ = count

validateCandidates : SortedSet CairoName -> List (InstVisit CairoReg) -> SortedMap CairoName (SortedSet CairoReg) -> SortedMap CairoName (SortedSet CairoReg)
validateCandidates validTargets body cands = fromList $ filter (\(k,v) => v /= empty && contains k validTargets) (map (validateCandidate body) (toList cands))

isShifted : CairoName -> Bool
isShifted (Extension "argument_shifted" _ _) = True
isShifted _ = False

transformCallSite : List (InstVisit CairoReg) -> SortedMap CairoName (SortedSet CairoReg) -> (Bool, List (InstVisit CairoReg))
transformCallSite body targets = replace False Nil body
    where replace : Bool -> List (InstVisit CairoReg) -> List (InstVisit CairoReg) -> (Bool, List (InstVisit CairoReg))
          replace changed acc ((inst1@(VisitCall [r] impls1 name args))::(inst2@(VisitApply r2 impls2 f a))::xs) = if isValid
                then replace True ((VisitCall [r2] empty (shiftName name) (args++[a]))::acc) xs
                else replace changed (inst2::inst1::acc) xs
            where isValid : Bool
                  isValid = case lookup name targets of
                    Nothing => False
                    (Just regs) => if contains r regs
                        then impls1 == empty && impls2 == empty && r == f
                        else False
          -- Note: This is only save if it is guaranteed that the target always reutrns a closure
          --          Sadly parameterized functions and dependent types do allow functions that sometimes do and sometimes don't
          --          Dataflow analysis may help here however I doubt that our is powerfull enough to be of substetial use here as closures are its weakspot
          --   We could a more weak version that targets ones with an explicit MkClosure with missing 1 at each return
          -- replace changed acc (inst@(VisitMkClosure r name miss args)::x) =  case lookup name targets of
          --    Nothing = replace changed (inst::acc) xs
          --    (Just _) = replace True ((VisitMkClosure r (shiftName name) (S miss) args)::acc) xs
          replace changed acc (x::xs) = replace changed (x::acc) xs
          replace changed acc Nil = (changed, reverse acc)

dbgString : (CairoName, CairoDef) -> String
dbgString (name, def) = if isShifted name
  then ("Searching in: "++ (show name)) ++ " - "++ (show def)
  else ("Searching in: "++ (show name))

processDef : SortedSet CairoName -> (CairoName, CairoDef) -> (SortedSet CairoName, (Bool, (CairoName, CairoDef)))
processDef validTargets def = let body = fromCairoDef def in
    let targets = (validateCandidates validTargets body (findCandidates (fst def) body)) in
    let (changed, newBody) = transformCallSite body targets in
    let shiftNames = fromList $ keys targets in
    (shiftNames, (changed, toCairoDef newBody))

generateShiftedDef : RegisterGen -> (CairoName, CairoDef) -> (RegisterGen, (CairoName, CairoDef))
generateShiftedDef regGen def@(name, (FunDef params impls rets body)) = if impls /= empty
        then assert_total $ idris_crash "applyOutline must run before implicit injection"
        else let reg = fst applyParam in
             let visits = fromCairoDef (shiftName name, FunDef (params++[reg]) empty rets body) in
             let ((nRg,_), nInsts) = foldl transformInst ((snd applyParam,0), Nil) visits in
             let shiftDef = toCairoDef $ reverse nInsts in
             (nRg, shiftDef)
    where applyParam : (CairoReg, RegisterGen)
          applyParam = nextRegister regGen 0
          transformInst : ((RegisterGen,Int), List (InstVisit CairoReg)) -> InstVisit CairoReg -> ((RegisterGen,Int), List (InstVisit CairoReg))
          transformInst ((rg,d), acc) (VisitReturn [f] impls) = if impls /= empty
                then assert_total $ idris_crash "applyOutline must run before implicit injection"
                else let (nreg, nrg) = nextRegister rg d in
                     ((nrg, d), (VisitReturn [nreg] empty)::(VisitApply nreg empty f (fst applyParam))::acc)
          transformInst (rgd, acc) inst@(VisitReturn _ _) = trace "Missed because of multi return" (rgd, inst::acc)
          transformInst ((rg,d), acc) inst@(VisitCase _) = ((rg, d+1), inst::acc)
          transformInst ((rg,d), acc) VisitCaseEnd = ((rg, d-1), VisitCaseEnd::acc)
          transformInst (rgd, acc) inst = (rgd, inst::acc)
generateShiftedDef _ _ = assert_total $ idris_crash "Can not shift external or foreign functions"

generateShiftedDefs : RegisterGen -> SortedMap CairoName CairoDef -> SortedSet CairoName -> (RegisterGen, List (CairoName, CairoDef))
generateShiftedDefs regGen allDefs shiftNames = let shiftDefs = map (\n => (n, (fromMaybe (assert_total $ idris_crash "Unkonwn Name") (lookup n allDefs)))) (toList shiftNames) in
        let newShiftDefs = filter (\(n,_) => isNothing (lookup (shiftName n) allDefs)) shiftDefs in
        foldl generate (regGen, Nil) newShiftDefs
    where generate : (RegisterGen, List (CairoName, CairoDef)) -> (CairoName, CairoDef) -> (RegisterGen, List (CairoName, CairoDef))
          generate (rg,acc) def = let (nRg,nDef) = generateShiftedDef rg def in (nRg, nDef::acc)


-- we inline into the newely generated methods
--  goal is to lift up applies to resolve recursive structures
--  for now - we need to target only functions that take in closures as these contain the open applies
customInliner : Bool -> List (CairoName, CairoDef)  -> List (CairoName, CairoDef)
customInliner tailBranchingActive = inlineCustomDefs tailBranchingActive decider
    where decider : SortedMap CairoName CairoDef -> CairoName -> FunData -> Bool
          decider _ intoName (MKFunData name _ _ _ args _) = isShifted intoName
              && intoName /= (shiftName name) -- we do not inline the unshifted as we plan to outline them (inlining them would be contra productive)
              && any containsClosure args

processDefs : RegisterGen -> List (CairoName, CairoDef) -> (RegisterGen, (Bool, List (CairoName, CairoDef)))
processDefs regGen defs = let validTargets = fromList $ map fst (filter isStdFun defs) in
                   let (shiftNames, (changed, nDefs)) = foldl (processEntry validTargets) (empty,(False,Nil)) defs in
                   if not changed then (regGen, (False, defs)) else
                   let allDefs = fromList nDefs in
                   let (nRg, genDefs) = generateShiftedDefs regGen allDefs shiftNames in
                   -- We need to process them again as the shifted in apply may be shifted immediately recursively
                   --  We can not do this in the first iter because the apply is not theire yet
                   --  We could do everything afterwards but that complicates the design -- todo: still consider this
                   -- Todo: as an alternative we can do this in the next pass - if we prevent generation of already generated shifted-defs
                   -- Todo: simply try removing this the ctxException may have been enough
                   -- let genDefs2 = map (processGen shiftNames) genDefs in
                   (nRg, (empty /= genDefs, genDefs ++ nDefs))
    where isStdFun : (CairoName, CairoDef) -> Bool
          isStdFun (_, FunDef _ _ _ _) = True
          isStdFun _ = False
          -- processGen : SortedSet CairoName -> (CairoName, CairoDef) -> (CairoName, CairoDef)
          -- processGen shiftNames def = snd $ snd $ processDef shiftNames def
          processEntry : SortedSet CairoName -> (SortedSet CairoName, (Bool, List (CairoName, CairoDef))) -> (CairoName, CairoDef) -> (SortedSet CairoName, (Bool, List (CairoName, CairoDef)))
          processEntry validTargets (sAcc, (oldC,dAcc)) def = let (shiftNames, (newC, nDef)) = processDef validTargets def in (union sAcc shiftNames, (oldC || newC, nDef::dAcc))

-- Get rid of no longer used defs
-- Make a generall optimisation pass to turn applies into calls
-- Make an inlining pass to turn calls into applies (but limited to custom inliner)
optimizeAfterIter : Bool -> List (CairoName, CairoDef)  -> List (CairoName, CairoDef)
optimizeAfterIter tailBranchingActive = (customInliner tailBranchingActive) . localStaticOptimizeDefs . orderUsedDefs

processDefsIterative : Bool -> RegisterGen -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
processDefsIterative tailBranchingActive regGen defs = case processDefs regGen defs of
    (_, (False, nDefs)) => orderUsedDefs nDefs
    (nRg, (True, nDefs)) => processDefsIterative tailBranchingActive nRg (optimizeAfterIter tailBranchingActive nDefs)

-- Todo: As Preparation a returnInwardsShift & applyUpwardsShift would be nice
--       returnInwardsShift = move returns into branches if they are tail pos
--       applyUpwardsShift = move apply nearer to the call
--         alternative (better) = CallDownShift = move call down until result is used or branch ends / starts
--       Otherwise a simple rewrite rule may miss
--   Note: if code is generated by idris it is probably not necessary in most cases (especially if a programmer writes nice code)
export
applyOutlining : Bool -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
applyOutlining tailBranchingActive = processDefsIterative tailBranchingActive (mkRegisterGen "applyShifting")
