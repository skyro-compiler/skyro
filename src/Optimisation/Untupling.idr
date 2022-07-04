module Optimisation.Untupling

import Data.SortedSet
import Data.SortedMap
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Core.Context
import Data.List
import CommonDef
import Primitives.Externals
import CairoCode.Traversal.Base
import CairoCode.Traversal.Composition
import Utils.Lens
import CairoCode.Traversal.ValueTracker
import Utils.Helpers
import Debug.Trace
import Optimisation.DataFlowAnalyser

%hide Prelude.toList

-- Todo: Rename to ReturnUntupler
-- Todo: Make ParamUntupler : Only if tupled then called then untupled (& tupled is not needed except by projets)
--       We need ensure that we not untuple over more than one call border (otherwise it gets more expensive)

-- Collects all functions that are underApplied
underAppliedFunctionsDefs : List (Name, CairoDef) -> SortedSet Name
underAppliedFunctionsDefs defs = snd $ runVisitConcatCairoDefs (pureTraversal underApplyCollectorTraversal) defs
    where underApplyCollectorTraversal : InstVisit CairoReg -> SortedSet Name
          underApplyCollectorTraversal (VisitMkClosure _ name _ _) = singleton name
          underApplyCollectorTraversal _ = empty

-- Collects all functions that are fullyApplied
fullyAppliedFunctionsDefs : List (Name, CairoDef) -> SortedSet Name
fullyAppliedFunctionsDefs defs = snd $ runVisitConcatCairoDefs (pureTraversal fullApplyCollectorTraversal) defs
    where fullApplyCollectorTraversal : InstVisit CairoReg -> SortedSet Name
          fullApplyCollectorTraversal (VisitCall _ _ name _) = singleton name
          fullApplyCollectorTraversal _ = empty

-- Data to represent Tupling Information internally
data UntupleInfo : Type where
 Undecided : UntupleInfo                                -- It is not known yet if this can be untupled or not
 Candidate : Int -> List UntupleInfo -> UntupleInfo     -- It is a Candidate for being untupled nothing speaks against it for now
 Untouched : UntupleInfo                                -- This can or should not be Untupled, either something prevents or we are not sure (recursion)

Show UntupleInfo where
    show Undecided = "Undecided"
    show Untouched = "Untouched"
    show (Candidate n args) = assert_total $ "Candidate("++(show n)++"|"++(separate "," (map show args))++")"


toUntupleInfo : TupleStructure -> UntupleInfo
toUntupleInfo (Tupled t fields) = Candidate t (map toUntupleInfo fields)
toUntupleInfo ReturnValue = Untouched

untupledExtPrimDefs : List (Name, CairoDef) -> SortedMap Name UntupleInfo
untupledExtPrimDefs defs = fromList ((toList $ snd $ runVisitConcatCairoDefs (pureTraversal allExistingExtPrims) defs) >>= resolveUtInfo)
    where allExistingExtPrims : InstVisit CairoReg -> SortedSet Name
          allExistingExtPrims (VisitExtprim _ _ name _) = singleton name
          allExistingExtPrims _ = empty
          resolveUtInfo : Name -> List (Name, UntupleInfo)
          resolveUtInfo name = case (externalTupleSig name) of
            Nothing => Nil
            (Just ts) => [(name, toUntupleInfo ts)]

-- Collects tail Constructs and tail Calls (including EXTPRIM)

mergeUntupleInfo : UntupleInfo -> UntupleInfo -> UntupleInfo
mergeUntupleInfo Untouched _ = Untouched
mergeUntupleInfo _ Untouched = Untouched
mergeUntupleInfo Undecided b = b
mergeUntupleInfo a Undecided = a
mergeUntupleInfo (Candidate t1 fs1) (Candidate t2 fs2) = if t1 /= t2 || (length fs1) /= (length fs2)
    then Untouched
    else Candidate t1 (zipWith mergeUntupleInfo fs1 fs2)

Semigroup UntupleInfo where (<+>) = mergeUntupleInfo
Monoid UntupleInfo where neutral = Undecided

-- Todo: Can we use the global tracking Infrastructure to do this better?
--       Or Alternatively we could build this on the Dataflow Analysis (but that one is overly conservative)
--          However because of that it is less likely to do unecessary unpacking and repackings

extractUntupleInfoDef : SortedMap Name UntupleInfo -> (Name, CairoDef) -> Maybe UntupleInfo
-- Ignore already untupled
extractUntupleInfoDef resolved def@(_, FunDef _ _ [_] _) = snd (runVisitConcatCairoDef (traversal $ valueCollector idLens (dbgDef def) prepareB (passThroughImpls $ defaultNoImplValBind (\_ => Untouched) tupledReturnTracker) returnCollector) def)
    where dbgDef : (Name, CairoDef) -> CairoReg -> UntupleInfo
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" Undecided
          prepareB : CairoReg -> UntupleInfo -> UntupleInfo
          prepareB _ ut = ut
          tupledReturnTracker : (v:InstVisit UntupleInfo) -> Traversal (ScopedBindings UntupleInfo) (Maybe (NoImplValBindType v UntupleInfo))
          tupledReturnTracker (VisitAssign _ a) = pure $ Just $ a
          tupledReturnTracker (VisitMkCon _ tag args) = pure $ Just $ Candidate (fromMaybe 0 tag) args
          tupledReturnTracker (VisitCall [r] _ name _ ) = pure $ Just [fromMaybe Undecided (lookup name resolved)]
          tupledReturnTracker (VisitExtprim [r] _ name _ ) = pure $ Just [fromMaybe Undecided (lookup name resolved)]
          tupledReturnTracker _ = pure $ Nothing
          returnCollector : InstVisit UntupleInfo -> Traversal (ScopedBindings UntupleInfo) (Maybe UntupleInfo)
          returnCollector (VisitReturn [singleRes] _) = pure $ Just singleRes
          returnCollector (VisitReturn _ _) = pure $ Just Untouched -- already untupled
          returnCollector _ = pure Nothing
          Semigroup (Maybe UntupleInfo) where
            (<+>) Nothing res = res
            (<+>) res Nothing = res
            (<+>) (Just res1) (Just res2)  = Just (res1 <+> res2)
          Monoid (Maybe UntupleInfo) where neutral = Nothing
extractUntupleInfoDef _ (_, ForeignDef (MkForeignInfo _ ut _ _ _) _ 1) = map toUntupleInfo ut
extractUntupleInfoDef _ _  = Nothing


-- Here is the iterative tupler analysis

-- Like merge Info but changes are only allowed from: Undecided -> Candidate -> Untouched
--  Ensures that the iterative algorithm terminates
--  The Bool is false if (snd (mergeInfoUp old new)) == old and true otherwise
mergeInfoUp : (old:UntupleInfo) -> (new:UntupleInfo) -> (Bool, UntupleInfo)
mergeInfoUp a Undecided = (False, a)
mergeInfoUp Undecided b = (True, b)
mergeInfoUp Untouched _ = (False, Untouched)
mergeInfoUp _ Untouched = (True, Untouched)
mergeInfoUp (Candidate t1 fs1) (Candidate t2 fs2) = if t1 /= t2 || (length fs1) /= (length fs2)
    then (True, Untouched)
    else (any fst zipped, Candidate t1 (map snd zipped))
  where zipped : List (Bool, UntupleInfo)
        zipped = zipWith mergeInfoUp fs1 fs2

runFindTuplingTargetDef : SortedMap Name UntupleInfo -> (Name, CairoDef) -> (Bool, SortedMap Name UntupleInfo)
runFindTuplingTargetDef info d@(name,def) = (reinsertInfo (mergeInfo (extractUntupleInfoDef info d)))
    where mergeInfo : Maybe UntupleInfo -> Maybe (Bool, UntupleInfo)
          mergeInfo Nothing = Nothing
          mergeInfo (Just inf) = Just (mergeInfoUp (fromMaybe Undecided (lookup name info)) inf)
          reinsertInfo : Maybe (Bool, UntupleInfo) -> (Bool, SortedMap Name UntupleInfo)
          reinsertInfo (Just (mod, inf)) = (mod, insert name inf info)
          reinsertInfo Nothing = (False, info)

runFindTuplingTargetDefs : SortedMap Name UntupleInfo -> List (Name, CairoDef) -> (Bool, SortedMap Name UntupleInfo)
runFindTuplingTargetDefs info defs = foldl processDef (False,info) defs
    where processDef : (Bool, SortedMap Name UntupleInfo) -> (Name, CairoDef) -> (Bool, SortedMap Name UntupleInfo)
          processDef (mod, inf) def = let (lmod, ninf) = runFindTuplingTargetDef inf def in (mod || lmod, ninf)

-- runs runFindTuplingTargetDefs until nothing changed
iterFindTuplingTargetDefs : SortedMap Name UntupleInfo -> List (Name, CairoDef) -> SortedMap Name UntupleInfo
iterFindTuplingTargetDefs info defs = if fst singleRun
    then iterFindTuplingTargetDefs (snd singleRun) defs
    else snd singleRun
    where singleRun : (Bool, SortedMap Name UntupleInfo)
          singleRun = runFindTuplingTargetDefs info defs

-- Here comes the test if the Callers profits from an untupled representation
findUnprofitableUntuplingTargets : List (Name, CairoDef) -> SortedSet Name
findUnprofitableUntuplingTargets defs = snd (runVisitConcatCairoDefs (traversal $ valueCollector idLens dbgDef prepareB (passThroughImpls $ defaultNoImplValBind (\_ => empty) tupledCallResultTracker) tupledUseFinder) defs)
    where dbgDef : CairoReg -> SortedSet Name
          dbgDef reg = trace "Register not bound" empty
          prepareB : CairoReg -> SortedSet Name -> SortedSet Name
          prepareB _ ns = ns
          Semigroup (SortedSet Name) where (<+>) = union
          Monoid (SortedSet Name) where neutral = empty
          tupledCallResultTracker : (v:InstVisit (SortedSet Name)) -> Traversal (ScopedBindings (SortedSet Name)) (Maybe (NoImplValBindType v (SortedSet Name)))
          -- We track through assigns
          tupledCallResultTracker (VisitAssign _ a) = pure $ Just $ a
          -- These are the sources
          --  Note: Despite Extprim being a source we need to untuple it if possible as the target signature may dictate it
          --        Same for ForeignFuns, however we filter them out later instead of here
          tupledCallResultTracker (VisitCall [_] _ name _ ) = pure $ Just [singleton name]
          -- tupledCallResultTracker (VisitExtprim [_] _ name _ ) = pure $ Just [singleton name]
          -- If a composite escapes then the whole thing escapes (Note: when untupling is used after other optimized thte result of thesewill always escape)
          --  However this way we have less order constraints
          tupledCallResultTracker (VisitMkCon _ _ args) = pure $ Just $ foldl union empty args
          tupledCallResultTracker (VisitMkClosure _ _ _ args) = pure $ Just $ foldl union empty args
          -- No need to track the rest as these escape the name anyway and lead to an entry from the tupledUseFinder anyway
          tupledCallResultTracker _ = pure $ Nothing
          -- Helper as used ofthen
          fuseAllTupled : SortedMap LinearImplicit ((SortedSet Name), CairoReg) -> List (SortedSet Name) -> SortedSet Name
          fuseAllTupled impls args = foldl union empty (args ++ (map fst (values impls)))

          tupledUseFinder : InstVisit (SortedSet Name) -> Traversal (ScopedBindings (SortedSet Name)) (SortedSet Name)
          -- if used as an argument (or implicit) in a call or operation it is needed tupled
          tupledUseFinder (VisitCall _ impls _ args) = pure $ fuseAllTupled impls args
          tupledUseFinder (VisitExtprim _ impls _ args) = pure $ fuseAllTupled impls args
          tupledUseFinder (VisitStarkNetIntrinsic _ impls _ args) = pure $ fuseAllTupled impls args
          tupledUseFinder (VisitOp _ impls _ args) = pure $ fuseAllTupled impls args
          tupledUseFinder (VisitApply _ impls f a) = pure $ fuseAllTupled impls [f, a]
          -- if used for branching we need tupled (in theory we could rely on dataflow to eliminate if only tag is used and untupled would be kn)
          --   Todo: if we have an example try to remove these and see how the result looks)
          tupledUseFinder (VisitCase br) = pure $ br
          -- The rest does not escape
          --  Note we do not treat return as escape, otherwise untupling of nested call hierarchies would always be rejected
          --  However the most essential here is that project does not escape
          tupledUseFinder _ = pure $ empty


-- Here is the Closure rewiring

record TupGenRes where
  constructor MkTupGenRes
  regGen: RegisterGen
  regs: List CairoReg
  code: List CairoInst


-- Generates code to build the tuple described by UntupleInfo and assign it to trg.
--  src contains the fields, however it may contain more the rest is returned

generateRetupling : RegisterGen -> (depth:Int) -> UntupleInfo -> (resReg: CairoReg) -> TupGenRes
generateRetupling regGen depth (Candidate tag fields) resReg = produceRes (foldl processField ([], MkTupGenRes regGen [] []) fields)
    where processField : (List CairoReg, TupGenRes) -> UntupleInfo -> (List CairoReg, TupGenRes)
          processField (acc, MkTupGenRes regGen sources code) info = let (MkTupGenRes newRegGen newSources newCode) = generateRetupling (snd fieldReg) depth info (fst fieldReg)
            in (acc ++ [fst fieldReg], MkTupGenRes newRegGen (sources ++ newSources) (code ++ newCode))
            where fieldReg : (CairoReg, RegisterGen)
                  fieldReg = nextRegister regGen depth
          produceRes : (List CairoReg, TupGenRes) -> TupGenRes
          produceRes (fieldRegs, MkTupGenRes regGen sources code) = MkTupGenRes regGen sources (code ++ [MKCON resReg (Just tag) fieldRegs])

generateRetupling regGen _ _ resReg = MkTupGenRes regGen [resReg] []

deriveUntupledName : Name -> Name
deriveUntupledName name = MN ("tupled_"++(cairoName name)) 0 --Todo: A nice prefix function in common def

generateReTupledClosure : Name -> List LinearImplicit -> List CairoReg -> UntupleInfo -> (Name, CairoDef)
generateReTupledClosure name linImpls args info = let (MkTupGenRes newNextReg sources code) = generateRetupling (snd retReg) 0 info (fst retReg)
        in (deriveUntupledName name, FunDef args implicitParams [CustomReg "tupledRet" Nothing] (((CALL sources callLinearImplicits name args)::code) ++ [RETURN [(fst retReg)] returnLinearImplicits]))
    where retReg : (CairoReg, RegisterGen)
          retReg = nextRegister (mkRegisterGen "retupling") 0
          implicitRegs : List CairoReg
          implicitRegs = snd $ foldl (\(n,acc), _ => (n+1, (Unassigned (Just "implicit") n 0)::acc)) (1, []) linImpls
          implicitParams : SortedMap LinearImplicit CairoReg
          implicitParams = fromList $ map (\i => (i, CustomReg (implicitName i) Nothing)) linImpls
          callLinearImplicits : SortedMap LinearImplicit (CairoReg, CairoReg)
          callLinearImplicits = fromList $ map (\(i,r) => (i, (fromMaybe (debugElimination "Untupling") (lookup i implicitParams), r))) (zip linImpls implicitRegs)
          returnLinearImplicits : SortedMap LinearImplicit CairoReg
          returnLinearImplicits = fromList $ zip linImpls implicitRegs

generateReTupledClosureDef : Name -> CairoDef -> UntupleInfo -> (Name, CairoDef)
generateReTupledClosureDef name (FunDef args linImpls _ _) info = generateReTupledClosure name (keys linImpls) args info
generateReTupledClosureDef name (ForeignDef i Z _) info = generateReTupledClosure name (implicits i) [] info
generateReTupledClosureDef name (ForeignDef i (S remArgs) _) info = generateReTupledClosure name (implicits i) (map Param (fromZeroTo (cast remArgs))) info
generateReTupledClosureDef _ (ExtFunDef _ _ _ _ _) _ = assert_total $ idris_crash "External functions are invalid closure targets"


rewireUntupledClosures : SortedMap Name UntupleInfo -> List (Name, CairoDef) -> List (Name, CairoDef)
rewireUntupledClosures inf defs = (mapMaybe genRetuplingFun (toList allUntupledClosures)) ++ (snd $ runVisitTransformCairoDefs (pureTraversal rewireTransform) defs)
    where allUntupledClosures : SortedSet Name
          allUntupledClosures = intersection (keySet inf) (underAppliedFunctionsDefs defs)
          defLookup : SortedMap Name CairoDef
          defLookup = fromList defs
          genRetuplingFun : Name -> Maybe (Name, CairoDef)
          genRetuplingFun name = pure (generateReTupledClosureDef name !(lookup name defLookup) !(lookup name inf))
          rewireTransform : InstVisit CairoReg -> List (InstVisit CairoReg)
          rewireTransform inst@(VisitMkClosure res name miss args) = if contains name allUntupledClosures
                then [VisitMkClosure res (deriveUntupledName name) miss args]
                else [inst]
          rewireTransform inst = [inst]

-- Here is the code transformer based on the analysis
generateUntupling : RegisterGen -> (depth:Int) -> UntupleInfo -> (src: CairoReg) -> TupGenRes
generateUntupling regGen depth (Candidate _ fields) src = processFields regGen 0 fields
    where processFields : RegisterGen -> Nat -> List UntupleInfo -> TupGenRes
          processFields regGen _ Nil = MkTupGenRes regGen [] []
          processFields regGen pos (f::fs) = MkTupGenRes rem.regGen (unpacked.regs++rem.regs) ((PROJECT (fst nReg) src pos)::(unpacked.code++rem.code))
             where nReg : (CairoReg, RegisterGen)
                   nReg = nextRegister regGen depth
                   unpacked : TupGenRes
                   unpacked = generateUntupling (snd nReg) depth f (fst nReg)
                   rem : TupGenRes
                   rem = processFields (unpacked.regGen) (pos+1) fs

generateUntupling nextReg _ _ src = MkTupGenRes nextReg [src] []

untupledRets : UntupleInfo -> Int
untupledRets (Candidate tag fields) = foldl (\acc,sub => acc + untupledRets sub) 0 fields
untupledRets _ = 1

adaptReturn : Maybe UntupleInfo -> (Name, CairoDef) -> (Name, CairoDef)
adaptReturn (Just Undecided) nd = nd
adaptReturn (Just Untouched) nd = nd
adaptReturn (Just uinf) (name, ForeignDef linImpls argsN 1) = (name, ForeignDef linImpls argsN (cast (untupledRets uinf)))
adaptReturn (Just uinf) (name, FunDef params implicits [_] body) = (name, FunDef params implicits retNames body)
    where retNames : List CairoReg
          retNames = map (\i => CustomReg ("r_"++(show i)) Nothing) (fromZeroTo ((untupledRets uinf)-1))
adaptReturn _ def = def

untupleDef : SortedMap Name UntupleInfo -> (Name, CairoDef) -> (Name, CairoDef)
untupleDef info def@(name,_) = adaptReturn (lookup name info) (orderUnassignedRegIndexes (snd $ runVisitTransformCairoDef (rawTraversal untuplerTransform (mkRegisterGen "untupling", 0)) def))
    where untuplerTransform : InstVisit CairoReg -> Traversal (RegisterGen,Int) (List (InstVisit CairoReg))
          untuplerTransform inst@(VisitCall (oldRet::Nil) linImpls target args) = case (lookup target info) of
            Nothing => pure [inst]
            (Just Untouched) => pure [inst]
            (Just utinfo) => do
                (regGen, depth) <- readState
                let (MkTupGenRes newRegGen sources code) = generateRetupling regGen depth utinfo oldRet
                _ <- writeState (newRegGen, depth)
                pure ((VisitCall sources linImpls target args)::(fromCairoInsts code))
          untuplerTransform inst@(VisitExtprim (oldRet::Nil) linImpls target args) = case (lookup target info) of
            Nothing => pure [inst]
            (Just Untouched) => pure [inst]
            (Just utinfo) => do
                (regGen, depth) <- readState
                let (MkTupGenRes newRegGen sources code) = generateRetupling regGen depth utinfo oldRet
                _ <- writeState (newRegGen, depth)
                pure ((VisitExtprim sources linImpls target args)::(fromCairoInsts code))
          untuplerTransform inst@(VisitReturn (oldRet::Nil) linImpls) = case (lookup name info) of
            Nothing => pure [inst]
            (Just Untouched) => pure [inst]
            (Just utinfo) => do
                (regGen, depth) <- readState
                let (MkTupGenRes newRegGen targets code) = generateUntupling regGen depth utinfo oldRet
                _ <- writeState (newRegGen, depth)
                pure ((fromCairoInsts code) ++ [VisitReturn targets linImpls])
          untuplerTransform inst@(VisitCase reg) = map (\_ => [inst]) (updateStateL rightLens (+1))
          untuplerTransform VisitCaseEnd = map (\_ => [VisitCaseEnd]) (updateStateL rightLens (\x => x-1))
          untuplerTransform inst = pure [inst]

isInternal : SortedMap Name CairoDef -> Name -> Bool
isInternal allDefs name = case lookup name allDefs of
    Nothing => trace "Ups should not happen" False -- Should never happen
    (Just (ForeignDef _ _ _)) => False
    (Just _) => True

export
untupling : List (Name, CairoDef) -> List (Name, CairoDef)
untupling defs = let allDefs = fromList defs in
                 let directlyCalledTargets = fullyAppliedFunctionsDefs defs in
                 let untupledCallInfo = iterFindTuplingTargetDefs empty (filter (\(n,_) => contains n directlyCalledTargets) defs) in
                 let unprofitableDefs = findUnprofitableUntuplingTargets defs in
                 let unprofitableInternalDefs = setFilter (isInternal allDefs) unprofitableDefs in
                 let profitableUntupledCallInfo = mapFilter (\(n,_) => not $ contains n unprofitableInternalDefs) untupledCallInfo in
                 let untuplingTargets = mergeLeft (untupledExtPrimDefs defs) profitableUntupledCallInfo in
                 rewireUntupledClosures untuplingTargets (map (untupleDef untuplingTargets) defs)
