module CairoCode.Traversal.ValueTracker

import Data.SortedSet
import Data.SortedMap
import Data.Maybe
import Data.List
import CairoCode.CairoCode
-- import Core.Context
import CairoCode.Traversal.Base
import CairoCode.Traversal.Composition
import CairoCode.Traversal.Defaults
import Utils.Helpers
import Utils.Lens
import Debug.Trace


%hide Prelude.toList

public export
ValBindType : InstVisit a -> Type -> Type
ValBindType (VisitFunction _ _ _ _ _) a = (List a, SortedMap LinearImplicit a)
ValBindType (VisitForeignFunction _ _ _ _) a = ()
ValBindType (VisitAssign _ _) a = a
ValBindType (VisitMkCon _ _ _) a = a
ValBindType (VisitMkClosure _ _ _ _) a = a
ValBindType (VisitApply _ _ _ _) a = (a, SortedMap LinearImplicit a)
ValBindType (VisitMkConstant _ _) a = a
ValBindType (VisitCall _ _ _ _) a = (List a, SortedMap LinearImplicit a)
ValBindType (VisitOp _ _ _ _) a = (a, SortedMap LinearImplicit a)
ValBindType (VisitExtprim _ _ _ _) a = (List a, SortedMap LinearImplicit a)
ValBindType (VisitStarkNetIntrinsic _ _ _ _) a = (a, SortedMap LinearImplicit a)
ValBindType (VisitCase _) a = ()
ValBindType (VisitConBranch _) a = Maybe a
ValBindType (VisitConstBranch _) a = Maybe a
ValBindType VisitBranchEnd a = ()
ValBindType VisitCaseEnd a = ()
ValBindType (VisitProject _ _ _) a = a
ValBindType (VisitReturn _ _) a = ()
ValBindType (VisitNull _) a = a
ValBindType (VisitError _ _) a = a
ValBindType VisitEndFunction a = ()

public export
NoImplValBindType : InstVisit a -> Type -> Type
NoImplValBindType (VisitApply _ _ _ _) a = a
NoImplValBindType (VisitCall _ _ _ _) a = List a
NoImplValBindType (VisitOp _ _ _ _) a = a
NoImplValBindType (VisitExtprim _ _ _ _) a = List a
NoImplValBindType (VisitStarkNetIntrinsic _ _ _ _) a = a
NoImplValBindType inst a = ValBindType inst a

export
passThroughImpls : ((v:InstVisit a) -> Traversal s (NoImplValBindType v a)) -> ((v:InstVisit a) -> Traversal s (ValBindType v a))
passThroughImpls fn = processImpls
    where procImpls : (v:InstVisit a) -> SortedMap LinearImplicit (a, CairoReg) -> Traversal s (NoImplValBindType v a, SortedMap LinearImplicit a)
          procImpls inst linImps = do
              res <- fn inst
              pure (res, mapValueMap fst linImps)
          processImpls : (v:InstVisit a) -> Traversal s (ValBindType v a)
          processImpls inst@(VisitApply _ linImpls _ _) = procImpls inst linImpls
          processImpls inst@(VisitCall _ linImpls _ _) = procImpls inst linImpls
          processImpls inst@(VisitOp _ linImpls _ _) = procImpls inst linImpls
          processImpls inst@(VisitExtprim _ linImpls _ _) = procImpls inst linImpls
          processImpls inst@(VisitStarkNetIntrinsic _ linImpls _ _) = procImpls inst linImpls
          -- Sadly idris needs full pattern for the case where: NoImplValBindType inst a = ValBindType inst a
          processImpls inst@(VisitFunction _ _ _ _ _) = fn inst
          processImpls inst@(VisitForeignFunction _ _ _ _) = fn inst
          processImpls inst@(VisitAssign _ _) = fn inst
          processImpls inst@(VisitMkCon _ _ _) = fn inst
          processImpls inst@(VisitMkClosure _ _ _ _) = fn inst
          processImpls inst@(VisitMkConstant _ _) = fn inst
          processImpls inst@(VisitCase _) = fn inst
          processImpls inst@(VisitConBranch _) = fn inst
          processImpls inst@(VisitConstBranch _) = fn inst
          processImpls inst@VisitBranchEnd = fn inst
          processImpls inst@VisitCaseEnd = fn inst
          processImpls inst@(VisitProject _ _ _) = fn inst
          processImpls inst@(VisitReturn _ _) = fn inst
          processImpls inst@(VisitNull _) = fn inst
          processImpls inst@(VisitError _ _) = fn inst
          processImpls inst@VisitEndFunction = fn inst

export
data BindingScope : Type -> Type where
     CaseScope : CairoReg -> SortedMap CairoReg a -> BindingScope a
     BlockScope : SortedMap CairoReg a -> BindingScope a

Show (BindingScope a) where
  show (CaseScope reg _) = "Case " ++ (show reg)
  show (BlockScope _ ) = "Block"

public export
ScopedBindings : Type -> Type
ScopedBindings a = List (BindingScope a)

findBinding : CairoReg -> ScopedBindings a -> Maybe (Int, a)
findBinding _ Nil = Nothing
findBinding reg ((CaseScope _ _)::xs) = map (\(d,res) => (d+1, res)) (findBinding reg xs)
findBinding reg ((BlockScope binds)::xs) = case lookup reg binds of
    Nothing => map (\(d,res) => (d+1, res)) (findBinding reg xs)
    (Just res) => Just (0,res)

findCaseReg : ScopedBindings a -> Maybe CairoReg
findCaseReg Nil = Nothing
findCaseReg ((CaseScope a _)::xs) = Just a
findCaseReg ((BlockScope _)::xs) = findCaseReg xs

allCaseRegs : ScopedBindings a -> List CairoReg
allCaseRegs Nil = Nil
allCaseRegs ((CaseScope a _)::xs) = a::(allCaseRegs xs)
allCaseRegs ((BlockScope _)::xs) = allCaseRegs xs

addBinding : CairoReg -> a -> ScopedBindings a -> ScopedBindings a
addBinding reg val ((BlockScope binds)::xs) = (BlockScope (insert reg val binds))::xs
addBinding _ _ _ = assert_total $ idris_crash "Can not add binding to empty or case Scope"

allCaseBindings : ScopedBindings a -> List a
allCaseBindings binds = allCaseRegs binds >>= (\reg => flatten $ findBinding reg binds)
    where flatten : Maybe (Int, a) -> List a
          flatten Nothing = Nil
          flatten (Just (_, av)) = [av]

findCaseBinding : ScopedBindings a -> Maybe (Int, a)
findCaseBinding binds = (findCaseReg binds >>= (\reg => findBinding reg binds))

export
getBinding : CairoReg -> Traversal (ScopedBindings a) (Maybe a)
getBinding reg = do
    state <- readState
    let res = findBinding reg state
    pure $ map snd res

export
getAllCaseReg : Traversal (ScopedBindings a) (List CairoReg)
getAllCaseReg = pure $ allCaseRegs !readState

export
getAllCaseBindings : Traversal (ScopedBindings a) (List a)
getAllCaseBindings = pure $ allCaseBindings !readState

export
getCaseReg : Traversal (ScopedBindings a) (Maybe CairoReg)
getCaseReg = pure $ findCaseReg !readState

export
getCaseBinding : Traversal (ScopedBindings a) (Maybe a)
getCaseBinding = do
    state <- readState
    let res = findCaseBinding state
    pure $ map snd res

export
getDistance : CairoReg -> Traversal (ScopedBindings a) (Maybe Int)
getDistance reg = do
    state <- readState
    let res = findBinding reg state
    pure $ map (\(dist,_) => dist) res

export
extractDepth : (ScopedBindings a) -> Int
extractDepth bindings = div (cast $ length bindings) 2

export
getDepth : Traversal (ScopedBindings a) Int
getDepth = pure $ extractDepth !readState

export
bindReg : CairoReg -> a -> Traversal (ScopedBindings a) ()
bindReg reg val = updateState (addBinding reg val)

descendCase : CairoReg -> Traversal (ScopedBindings a) ()
descendCase reg = updateState update
    where update : ScopedBindings a -> ScopedBindings a
          update old@((BlockScope binds)::xs) = (CaseScope reg binds)::old
          update _ = assert_total $ idris_crash "Wrong stack structure for case descending"

descendBranch : Traversal (ScopedBindings a) ()
descendBranch = updateState update
    where update : ScopedBindings a -> ScopedBindings a
          update old@((CaseScope _ _)::(BlockScope binds)::xs) = (BlockScope binds)::old
          update _ = assert_total $ idris_crash "Wrong stack structure for branch descending"

public export
interface Semigroup a => BranchAware a where
    leaveScope : Int -> a -> a
    leaveScope _ v = v

ascendBranch : BranchAware a => Traversal (ScopedBindings a) ()
ascendBranch = updateState update
    where update : ScopedBindings a -> ScopedBindings a
          update (((BlockScope blockBinds)::(CaseScope cv caseBinds)::xs)) = (CaseScope cv (blockBinds <+> caseBinds))::xs
          update _ = assert_total $ idris_crash "Wrong stack structure for branch ascending"

ascendCase : BranchAware a => Traversal (ScopedBindings a) ()
ascendCase = updateState update
    where update : ScopedBindings a -> ScopedBindings a
          update (((CaseScope cv caseBinds)::(BlockScope _)::xs)) = (BlockScope $ liftBindings caseBinds)::xs
                where liftBindings : SortedMap CairoReg a -> SortedMap CairoReg a
                      liftBindings = mapValueMap (leaveScope (div (cast $ length xs) 2))
          update _ = assert_total $ idris_crash "Wrong stack structure for case ascending"

{-
 Executes looks up bindings for registers and replace with the bound value then use tracker to compute the bindings for the instruction and adds them to the lexical scope
 -- Light Version
 start - value (Reg) & state -> substitute (Reg-> a) |- value (a) & state -> tracker => bindResult - value -> _
                                | ---------------------use same binding state ------------------|
 --- Full Version ---
 start - value (Reg) & state ---------------> manage lexical scope - value (Reg) -> _
     | - value (Reg) -> substitute (Reg-> a) <- state -----------|
                        | - value (a) & state -> tracker => bindResult - value -> _
                                                                     | - state -> end
-}
export
valueTracker : BranchAware a => Lens os (ScopedBindings a) -> (CairoReg -> a) -> (CairoReg -> a -> a) -> ((v:InstVisit a) -> Traversal os (ValBindType v a)) -> (InstVisit CairoReg -> Traversal os ())
valueTracker lens defaultCase prepareBinding tracker = seqTraversal handleCase (substituteInstVisitValue substitute doTracking)
    where lift : Traversal (ScopedBindings a) b -> Traversal os b
          lift = composeState lens 
          substitute : CairoReg -> Traversal os a
          substitute r@(Eliminated _) = map (prepareBinding r) (tracker (VisitNull r))
          substitute inst@(Const c) = map (prepareBinding inst) (tracker (VisitMkConstant inst c))
          substitute reg = map (prepareBinding reg) (map (fromMaybe (defaultCase reg)) (lift $ getBinding reg))
          bindSingle : CairoReg -> a -> Traversal os ()
          bindSingle r v = lift $ bindReg r v
          bindAll : List (CairoReg, a) -> Traversal os ()
          bindAll binds = foldlM (\_,(r,v) => bindSingle r v) () binds
          getPlainImplBindings : SortedMap LinearImplicit CairoReg -> SortedMap LinearImplicit a -> List (CairoReg, a)
          getPlainImplBindings implRegs implVals = map (\linImpl => genMayBind (lookup linImpl implRegs) (lookup linImpl implVals)) (keys implRegs)
            where genMayBind: Maybe CairoReg -> Maybe a -> (CairoReg, a)
                  genMayBind (Just reg) (Just v) = (reg, v)
                  genMayBind _ _ = assert_total $ idris_crash "No impl Binding was provided"
          getImplBindings : SortedMap LinearImplicit (a, CairoReg) -> SortedMap LinearImplicit a -> List (CairoReg, a)
          getImplBindings implRegs implVals = getPlainImplBindings (mapValueMap snd implRegs) implVals
          handleCase : InstVisit CairoReg -> Traversal os ()
          handleCase (VisitCase caseReg) = lift $ descendCase caseReg
          handleCase _ = pure ()
          rebindCaseReg : Maybe a -> Traversal os ()
          rebindCaseReg Nothing = pure ()
          rebindCaseReg (Just av) = lift getCaseReg >>= (\mReg => fromMaybe (pure ()) (map (\reg => bindSingle reg av) mReg))
          doTracking : InstVisit a -> Traversal os ()
          doTracking inst@(VisitFunction _ _ params impls _) = do
            _ <- writeStateL lens ((BlockScope empty)::Nil)    -- start with a fresh block (we can not use descend as this expect a parent vlock
            (pramVs, implVs) <- tracker inst
            bindAll ((zip params pramVs) ++ getPlainImplBindings impls implVs)
          doTracking inst@(VisitForeignFunction _ _ _ _ ) = writeStateL lens ((BlockScope empty)::Nil)  -- start with a fresh block (we can not use descend as this expect a parent vlock
          doTracking inst@(VisitAssign res _) = tracker inst >>= bindSingle res
          doTracking inst@(VisitMkCon res _ _) = tracker inst >>= bindSingle res
          doTracking inst@(VisitMkClosure res _ _ _) = tracker inst >>= bindSingle res
          doTracking inst@(VisitApply res impls _ _) = tracker inst >>= (\(resV, implVs) => bindAll ((res,resV)::(getImplBindings impls implVs)))
          doTracking inst@(VisitMkConstant res _) = tracker inst >>= bindSingle res
          doTracking inst@(VisitCall res impls _ _) = tracker inst >>= (\(resV, implVs) => bindAll ((zip res resV) ++ (getImplBindings impls implVs)))
          doTracking inst@(VisitOp res impls _ _) = tracker inst >>= (\(resV, implVs) => bindAll ((res,resV)::(getImplBindings impls implVs)))
          doTracking inst@(VisitExtprim res impls _ _) = tracker inst >>= (\(resV, implVs) => bindAll ((zip res resV) ++ (getImplBindings impls implVs)))
          doTracking inst@(VisitStarkNetIntrinsic res impls _ _) = tracker inst >>= (\(resV, implVs) => bindAll ((res, resV)::(getImplBindings impls implVs)))
          doTracking (VisitCase caseReg) = pure () -- Already handled by handleCase
          doTracking inst@(VisitConBranch _) = (lift descendBranch) >>= (\_ => tracker inst >>= rebindCaseReg)
          doTracking inst@(VisitConstBranch _) = (lift descendBranch) >>= (\_ => tracker inst >>= rebindCaseReg)
          doTracking VisitBranchEnd = lift ascendBranch
          doTracking VisitCaseEnd = lift ascendCase
          doTracking inst@(VisitProject res _ _) = tracker inst >>= (bindSingle res)
          doTracking inst@(VisitReturn _ _ ) = tracker inst -- Maybe the tracker wants to record the return in the state
          doTracking inst@(VisitNull res) = tracker inst >>= (bindSingle res)
          doTracking inst@(VisitError res _ ) = tracker inst >>= (bindSingle res)
          doTracking VisitEndFunction = writeStateL lens Nil

export
initialTrackerState : ScopedBindings a
initialTrackerState = Nil

{-
 Uses valueTracker to manage bindings and then executes collector on substituted values
 -- Light Version
 start - value (Reg) & state -> valueTracker - value (Reg) -> substitute (Reg-> a) - value (a) & state -> collector - value (a) & state -> end
                                | --use same binding state ---|
 --- Full Version ---
 start - value (Reg) & state -------------> valueTracker (tracker) - value -> _
     | - value (Reg) -> substitute (Reg-> a) <- state -|
                        | - value (a) & state -> collector - value (b) & state -> end
-}
export
valueCollector : BranchAware a => Lens os (ScopedBindings a) -> (CairoReg -> a) -> (CairoReg -> a -> a) -> ((v:InstVisit a) -> Traversal os (ValBindType v a))  -> (InstVisit a -> Traversal os b) -> (InstVisit CairoReg -> Traversal os b)
valueCollector lens defaultCase prepareBinding tracker collector = seqTraversal (valueTracker lens defaultCase prepareBinding tracker) (substituteInstVisitValue substitute collector)
    where substitute : CairoReg -> Traversal os a
          substitute r@(Eliminated _) = map (prepareBinding r) (tracker (VisitNull r))
          substitute inst@(Const c) = map (prepareBinding inst) (tracker (VisitMkConstant inst c))
          substitute reg = map (prepareBinding reg) (map (fromMaybe (defaultCase reg)) (composeState lens (getBinding reg)))
{-
 A value tracker with an added transformation step in front of the tracking which is used to produce the result and tracking input
                                                    | --------------------------- use same binding state --------------------------- |
 start - value (Reg) & state --> substitute (Reg-> a) - state & value (a) -> transformer - state & [value (Reg)] -> for each value : valueTracker (tracker) - [value] -> _
                                                                                       | - [value (Reg)] ------> end <------ state ------------ |
-}
export
valueTransformer : BranchAware a => Lens os (ScopedBindings a) -> (CairoReg -> a) -> (CairoReg -> a -> a) -> ((v:InstVisit a) -> Traversal os (ValBindType v a)) -> (InstVisit a -> Traversal os (List (InstVisit CairoReg))) -> (InstVisit CairoReg -> Traversal os (List (InstVisit CairoReg)))
valueTransformer lens defaultCase prepareBinding tracker transformer = traverseTransform (substituteInstVisitValue substitute transformer) plainTracker
    where substitute : CairoReg -> Traversal os a
          substitute r@(Eliminated _) = map (prepareBinding r) (tracker (VisitNull r))
          substitute inst@(Const c) = map (prepareBinding inst) (tracker (VisitMkConstant inst c))
          substitute reg = map (prepareBinding reg) (map (fromMaybe (defaultCase reg)) (composeState lens (getBinding reg)))
          plainTracker : InstVisit CairoReg -> Traversal os ()
          plainTracker = valueTracker lens defaultCase prepareBinding tracker

export
defaultNoImplValBind : (CairoReg -> a) -> ((v1:InstVisit a) -> Traversal s (Maybe (NoImplValBindType v1 a))) -> ((v2:InstVisit a) -> Traversal s (NoImplValBindType v2 a))
defaultNoImplValBind defaultGen specific = (\inst => map (fromMaybe (fallback inst)) (specific inst))
    where fallback : (v1:InstVisit a) -> NoImplValBindType v1 a
          fallback (VisitFunction _ _ params impl _) = (map defaultGen params, fromList $  map (\(k,v) => (k, defaultGen v))(toList impl))
          fallback (VisitForeignFunction _ _ _ _)  = ()
          fallback (VisitAssign res _)  = defaultGen res
          fallback (VisitMkCon res _ _)  = defaultGen res
          fallback (VisitMkClosure res _ _ _) = defaultGen res
          fallback (VisitApply res impl _ _) = defaultGen res
          fallback (VisitMkConstant res _) = defaultGen res
          fallback (VisitCall res impl _ _) = map defaultGen res
          fallback (VisitOp res impl _ _) = defaultGen res
          fallback (VisitExtprim res impl _ _) = map defaultGen res
          fallback (VisitStarkNetIntrinsic res impl _ _) = defaultGen res
          fallback (VisitCase _)  = ()
          fallback (VisitConBranch _) = Nothing
          fallback (VisitConstBranch _) = Nothing
          fallback VisitBranchEnd = ()
          fallback VisitCaseEnd = ()
          fallback (VisitProject res _ _) = defaultGen res
          fallback (VisitReturn _ _) = ()
          fallback (VisitNull res) = defaultGen res
          fallback (VisitError res _) = defaultGen res
          fallback VisitEndFunction = ()

export
defaultValBind : (CairoReg -> a) -> ((v1:InstVisit a) -> Traversal s (Maybe (ValBindType v1 a))) -> ((v2:InstVisit a) -> Traversal s (ValBindType v2 a))
defaultValBind defaultGen specific = (\inst => map (fromMaybe (fallback inst)) (specific inst))
    where fallback : (v1:InstVisit a) -> ValBindType v1 a
          fallback (VisitFunction _ _ params impl _) = (map defaultGen params, mapValueMap defaultGen impl)
          fallback (VisitForeignFunction _ _ _ _)  = ()
          fallback (VisitAssign res _)  = defaultGen res
          fallback (VisitMkCon res _ _)  = defaultGen res
          fallback (VisitMkClosure res _ _ _) = defaultGen res
          fallback (VisitApply res impl _ _) = (defaultGen res, mapValueMap (defaultGen . snd) impl)
          fallback (VisitMkConstant res _) = defaultGen res
          fallback (VisitCall res impl _ _) = (map defaultGen res, mapValueMap (defaultGen . snd) impl)
          fallback (VisitOp res impl _ _) = (defaultGen res,  mapValueMap (defaultGen . snd) impl)
          fallback (VisitExtprim res impl _ _) = (map defaultGen res,  mapValueMap (defaultGen . snd) impl)
          fallback (VisitStarkNetIntrinsic res impl _ _) = (defaultGen res,  mapValueMap (defaultGen . snd) impl)
          fallback (VisitCase _)  = ()
          fallback (VisitConBranch _) = Nothing
          fallback (VisitConstBranch _) = Nothing
          fallback VisitBranchEnd = ()
          fallback VisitCaseEnd = ()
          fallback (VisitProject res _ _) = defaultGen res
          fallback (VisitReturn _ _) = ()
          fallback (VisitNull res) = defaultGen res
          fallback (VisitError res _) = defaultGen res
          fallback VisitEndFunction = ()

-- To make the signature of generalizeTrack more readable
public export
ParamInit : Type -> Type
ParamInit a = Maybe LinearImplicit -> CairoReg -> a

public export
ResGeneral : Type -> Type -> Type
ResGeneral s a = (ret: List CairoReg) -> (params:List a) -> Traversal s (List a)

public export
ImplicitGeneral : Type -> Type -> Type
ImplicitGeneral s a = SortedMap LinearImplicit (a, CairoReg) -> Traversal s (SortedMap LinearImplicit a)

export
generalizeTrack : ParamInit a -> ResGeneral s a -> ImplicitGeneral s a -> ((v:(InstVisit a)) -> Traversal s (ValBindType v a))
generalizeTrack paramInit resGen implGen = generalized
    where failHead : List a -> a
          failHead (x::xs) = x
          failHead _ = assert_total $ idris_crash "Expected non empty list"
          generalized : (v:(InstVisit a)) -> Traversal s (ValBindType v a)
          generalized (VisitFunction _ _ params impls _) = pure (map (paramInit Nothing) params, mapMap (\(impl,reg) => (impl, paramInit (Just impl) reg)) impls)
          generalized (VisitForeignFunction _ _ _ _) = pure ()
          generalized (VisitAssign res reg) = map failHead (resGen [res] [reg])
          generalized (VisitMkCon res _ args) = map failHead (resGen [res] args)
          generalized (VisitMkClosure res _ _ args) = map failHead (resGen [res] args)
          generalized (VisitApply res linImpls clo arg) = pure (failHead !(resGen [res] [clo,arg]), !(implGen linImpls))
          generalized (VisitMkConstant res _) = map failHead (resGen [res] [])
          generalized (VisitCall res linImpls _ args) = pure (!(resGen res args), !(implGen linImpls))
          generalized (VisitOp res linImpls _ args) = pure (failHead !(resGen [res] args), !(implGen linImpls))
          generalized (VisitExtprim res linImpls _ args) = pure (!(resGen res args), !(implGen linImpls))
          generalized (VisitStarkNetIntrinsic res linImpls _ args) = pure (failHead !(resGen [res] args), !(implGen linImpls))
          generalized (VisitCase _) = pure ()
          generalized (VisitConBranch _) = pure Nothing
          generalized (VisitConstBranch _) = pure Nothing
          generalized VisitBranchEnd = pure ()
          generalized VisitCaseEnd = pure ()
          generalized VisitEndFunction = pure ()
          generalized (VisitReturn _ _) = pure ()
          generalized (VisitProject res src _) = map failHead (resGen [res] [src])
          generalized (VisitNull res) = map failHead (resGen [res] [])
          generalized (VisitError res _) = map failHead (resGen [res] [])
