module CairoCode.Traversal.Defaults

import Core.Context
import CairoCode.Traversal.Composition
import CairoCode.CairoCode
import CairoCode.Traversal.Base
import Utils.Lens
import Data.SortedMap

%hide Prelude.toList

export
generalize : ((rets:List CairoReg) -> SortedMap LinearImplicit (a, CairoReg) -> (params:List a) -> b) -> (InstVisit a -> b)
generalize fn = generalized
    where generalized : InstVisit a -> b
          generalized (VisitFunction _ _ _ _) = fn [] empty []
          generalized (VisitForeignFunction _ _ _ _) = fn [] empty []
          generalized (VisitAssign res reg) = fn [res] empty [reg]
          generalized (VisitMkCon res _ args) = fn [res] empty args
          generalized (VisitMkClosure res _ _ args) = fn [res] empty args
          generalized (VisitApply res linImpls clo arg) = fn [res] linImpls [clo,arg]
          generalized (VisitMkConstant res _) = fn [res] empty []
          generalized (VisitCall res linImpls _ args) = fn res linImpls args
          generalized (VisitOp res linImpls _ args) = fn [res] linImpls args
          generalized (VisitExtprim res linImpls _ args) = fn res linImpls args
          generalized (VisitReturn res _) = fn [] empty res -- Todo: Shall we Map implicits and pass in? to LinearImplicit -> (CairoReg, Eliminated)
          generalized (VisitProject res src _) = fn [res] empty [src]
          generalized (VisitNull res) = fn [res] empty []
          generalized (VisitError res _) = fn [res] empty []
          generalized (VisitCase arg) = fn [] empty [arg]
          generalized _ = fn [] empty []

-- Executes fn and if defined (Just) returns the value, otherwise (Nothing) returns a list with the input value
export
instFallback : (InstVisit a -> Traversal s (Maybe (List (InstVisit a)))) -> (InstVisit a -> Traversal s (List (InstVisit a)))
instFallback fn = (\inst => map (fromMaybe [inst]) (fn inst))


-- A wrapper that does nothing for control instructions and forwards the rest
export
ignoreControl : (InstVisit a -> Traversal s (List (InstVisit a))) -> (InstVisit a -> Traversal s (List (InstVisit a)))
ignoreControl fn = forwardControls
    where forwardControls : InstVisit a -> Traversal s (List (InstVisit a))
          forwardControls inst@(VisitFunction _ _ _ _) = pure [inst]
          forwardControls inst@(VisitForeignFunction _ _ _ _) = pure [inst]
          forwardControls VisitEndFunction = pure [VisitEndFunction]
          forwardControls inst@(VisitCase _ ) = pure [inst]
          forwardControls inst@(VisitConBranch _) = pure [inst]
          forwardControls inst@(VisitConstBranch _) = pure [inst]
          forwardControls VisitBranchEnd = pure [VisitBranchEnd]
          forwardControls VisitCaseEnd = pure [VisitCaseEnd]
          forwardControls inst = fn inst

export
substituteInstVisitValue : (a -> Traversal s b) -> (InstVisit b -> Traversal s c) -> (InstVisit a -> Traversal s c)
substituteInstVisitValue subst fn = (\inst => (substitute inst) >>= fn)
    where substituteMany : List a -> Traversal s (List b)
          substituteMany Nil = pure $ Nil
          substituteMany (x::xs) = pure $ (!(subst x))::(!(substituteMany xs))
          substLinImpls : SortedMap LinearImplicit (a, CairoReg) -> Traversal s (SortedMap LinearImplicit (b, CairoReg))
          substLinImpls linImpls = map fromList (traverse (\(impl,(from,to)) => pure (impl,(!(subst from),to))) (toList linImpls))
          substRetImpls : SortedMap LinearImplicit a -> Traversal s (SortedMap LinearImplicit b)
          substRetImpls linImpls = map fromList (traverse (\(impl,from) => pure (impl,!(subst from))) (toList linImpls))
          substitute : (InstVisit a -> Traversal s (InstVisit b))
          substitute (VisitFunction name params linImpls rets) = pure $ VisitFunction name params linImpls rets
          substitute (VisitForeignFunction name inf args rets) = pure $ VisitForeignFunction name inf args rets
          substitute (VisitAssign res src) = pure $ VisitAssign res !(subst src)
          substitute (VisitMkCon res tag args) = pure $ VisitMkCon res tag !(substituteMany args)
          substitute (VisitMkClosure res name miss args) = pure $ VisitMkClosure res name miss !(substituteMany args)
          substitute (VisitApply res linImpls clo arg) = pure $ VisitApply res !(substLinImpls linImpls) !(subst clo) !(subst arg)
          substitute (VisitMkConstant res const) = pure $ VisitMkConstant res const
          substitute (VisitCall res linImpls name args) = pure $ VisitCall res !(substLinImpls linImpls) name !(substituteMany args)
          substitute (VisitOp res linImpls primFn args) = pure $ VisitOp res !(substLinImpls linImpls) primFn !(substituteMany args)
          substitute (VisitExtprim res linImpls name args) = pure $ VisitExtprim res !(substLinImpls linImpls) name !(substituteMany args)
          substitute (VisitCase reg) = pure $ VisitCase !(subst reg)
          substitute (VisitConBranch tag) = pure $ VisitConBranch tag
          substitute (VisitConstBranch const) = pure $ VisitConstBranch const
          substitute VisitBranchEnd = pure $ VisitBranchEnd
          substitute VisitCaseEnd = pure $ VisitCaseEnd
          substitute (VisitProject res val pos) = pure $ VisitProject res !(subst val) pos
          substitute (VisitReturn vals linImpls) = pure $ VisitReturn !(substituteMany vals) !(substRetImpls linImpls)
          substitute (VisitNull res) = pure $ VisitNull res
          substitute (VisitError res err) = pure $ VisitError res err
          substitute VisitEndFunction = pure $ VisitEndFunction
