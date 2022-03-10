module CairoCode.CairoCodeUtils

import Core.Name.Namespace
import Compiler.Common
import Core.Context
import Data.List
import Data.String
import Data.Vect
import Data.Either
import Data.SortedSet
import Data.SortedMap
import  Utils.Helpers

import CommonDef
import CairoCode.CairoCode
import CairoCode.Traversal.Base
import CairoCode.Traversal.Defaults

%hide Prelude.toList

public export
Substitutions : Type
Substitutions = CairoReg -> Maybe CairoReg

substituteRegister : Substitutions -> CairoReg -> CairoReg
substituteRegister subst reg = fromMaybe reg (subst reg)

substituteRegisters : Substitutions -> List CairoReg -> List CairoReg
substituteRegisters subst regs = map (substituteRegister subst) regs

substituteLinearImplicits : Substitutions -> LinearImplicitArgs -> LinearImplicitArgs
substituteLinearImplicits subs linImpls = mapValueMap (\(f,t) => (substituteRegister subs f, substituteRegister subs t)) linImpls

substituteRetLinearImplicits : Substitutions -> SortedMap LinearImplicit CairoReg -> SortedMap LinearImplicit CairoReg
substituteRetLinearImplicits subs linImpls = mapValueMap (substituteRegister subs) linImpls

export
substituteDefRegisters : Substitutions -> (Name, CairoDef) -> (Name, CairoDef)
substituteDefRegisters subst def = snd $ runVisitTransformCairoDef (pureTraversal substituteTransform) def
    where substituteTransform : InstVisit CairoReg -> List (InstVisit CairoReg)
          substituteTransform (VisitFunction name params linImpls rets) = [VisitFunction name (substituteRegisters subst params) (substituteRetLinearImplicits subst linImpls) rets]
          substituteTransform (VisitAssign res reg) = [VisitAssign (substituteRegister subst res) (substituteRegister subst reg)]
          substituteTransform (VisitMkCon res tag args) = [VisitMkCon (substituteRegister subst res) tag (substituteRegisters subst args)]
          substituteTransform (VisitMkClosure res name miss args) = [VisitMkClosure (substituteRegister subst res) name miss (substituteRegisters subst args)]
          substituteTransform (VisitApply res linImpls f arg) = [VisitApply (substituteRegister subst res) (substituteLinearImplicits subst linImpls) (substituteRegister subst f) (substituteRegister subst arg)]
          substituteTransform (VisitMkConstant res const) = [VisitMkConstant (substituteRegister subst res) const]
          substituteTransform (VisitCall res linImpls name args) = [VisitCall (substituteRegisters subst res) (substituteLinearImplicits subst linImpls) name (substituteRegisters subst args)]
          substituteTransform (VisitOp res linImpls fn args) = [VisitOp (substituteRegister subst res) (substituteLinearImplicits subst linImpls) fn (map (substituteRegister subst) args)]
          substituteTransform (VisitExtprim res linImpls name args) = [VisitExtprim (substituteRegisters subst res) (substituteLinearImplicits subst linImpls) name (substituteRegisters subst args)]
          substituteTransform (VisitReturn res linImpls) = [VisitReturn (substituteRegisters subst res) (substituteRetLinearImplicits subst linImpls)]
          substituteTransform (VisitProject res reg pos) = [VisitProject (substituteRegister subst res) (substituteRegister subst reg) pos]
          substituteTransform (VisitNull res) = [VisitNull (substituteRegister subst res)]
          substituteTransform (VisitError res err) = [VisitError (substituteRegister subst res) err]
          substituteTransform (VisitCase reg) = [VisitCase (substituteRegister subst reg)]
          substituteTransform visit = [visit]


extractRegs : List CairoReg -> LinearImplicitArgs -> List CairoReg
extractRegs regs linImpls = (regs ++ ((toList linImpls) >>= (\(_,(f,t)) => [f,t])))

public export
RegisterGen : Type
RegisterGen = (String, Int)

-- Assumes String is unique between orderUnassignedRegIndexes runs
export
mkRegisterGen : String -> RegisterGen
mkRegisterGen p =  (p, 0)

export
subRegisterGen : CairoReg -> String -> RegisterGen
subRegisterGen reg p = mkRegisterGen ((show reg) ++ "_" ++ p)

export
deriveRegister : RegisterGen -> CairoReg -> CairoReg
deriveRegister (p1,_) (Unassigned (Just p2) i d) = Unassigned (Just (p1 ++ "_u_" ++ p2)) i d
deriveRegister (p1,_) (Unassigned Nothing i d) = Unassigned (Just (p1 ++ "_u")) i d
deriveRegister (p,_) (Param i) = Unassigned (Just (p ++ "_p")) i 0
deriveRegister (p,_) (NamedParam pn) = Unassigned (Just (p ++ "_np_" ++ pn)) 0 0
deriveRegister (p,_) (Local i d) = Unassigned (Just (p ++ "_lc")) i d
deriveRegister (p,_) (Let i d) = Unassigned (Just (p ++ "_lt")) i d
deriveRegister (p,_) (Temp i d) = Unassigned (Just (p ++ "_t")) i d
deriveRegister (p,_) (Const c) = Unassigned (Just (p ++ "_c_" ++ (show c))) 0 0
deriveRegister (p,_) Eliminated = Unassigned (Just (p ++ "_e")) 0 0

export
splitRegisterGen : RegisterGen -> (RegisterGen, RegisterGen)
splitRegisterGen (p, n) = (("\{p}:\{show n}",0), (p, n+1))

export
nextRegister : RegisterGen -> (depth:Int) -> (CairoReg, RegisterGen)
nextRegister (p,i) d = (Unassigned (Just p) i d,(p,i+1))

export
branchRegisterGen: Show a => Maybe a -> RegisterGen -> RegisterGen
branchRegisterGen Nothing (p,i) = ("\{p}_\{show i}_def" ,0)
branchRegisterGen (Just c) (p,i) = ("\{p}_\{show i}_\{show c}",0)

SeqRegAlloc : Type
SeqRegAlloc = (RegisterGen, SortedMap CairoReg CairoReg)

prepareRegDefSubst : CairoReg -> Traversal SeqRegAlloc ()
prepareRegDefSubst reg@(Unassigned _ _ d) = updateState (\(gen, subst) => updatedIfMissing (gen, subst) (lookup reg subst))
    where updatedIfMissing : SeqRegAlloc -> Maybe CairoReg -> SeqRegAlloc
          updatedIfMissing (gen, subst) Nothing = let (nReg, nextGen) = nextRegister gen d in (nextGen, insert reg nReg subst)
          updatedIfMissing state _ = state
prepareRegDefSubst _ = pure ()

export
orderUnassignedRegIndexes : (Name, CairoDef) -> (Name, CairoDef)
orderUnassignedRegIndexes def =  substituteDefRegisters (\r => lookup r substitution) def
    where seqRegNumberCollector : (rets:List CairoReg) -> SortedMap LinearImplicit (CairoReg, CairoReg) -> (params:List CairoReg) -> Traversal SeqRegAlloc ()
          seqRegNumberCollector regs impls _ = foldlM (\_,reg => prepareRegDefSubst reg) () (extractRegs regs impls)
          substitution: SortedMap CairoReg CairoReg
          substitution = snd $ runVisitCairoDef (rawTraversal (generalize seqRegNumberCollector) (mkRegisterGen "root",empty)) def

export
isLocal : CairoReg -> Bool
isLocal (Local _ _) = True
isLocal (Unassigned _ _ _) = True -- we treat undefined as locals: Reason -- Everything works without RegAlloc
isLocal _ = False

export
isConst : CairoReg -> Bool
isConst (Const _) = True
isConst _ = False

export
isLet : CairoReg -> Bool
isLet (Let _ _) = True
isLet _ = False

export
collectLocals : (Name, CairoDef) -> SortedSet CairoReg
collectLocals def = snd $ runVisitConcatCairoDef (pureTraversal $ generalize general) def
    where general : (rets:List CairoReg) -> LinearImplicitArgs -> (params:List CairoReg) -> SortedSet CairoReg
          general regs impls _ = fromList $ filter isLocal (extractRegs regs impls)


export
countDefInsts : (Name, CairoDef) -> Nat
countDefInsts def = snd $ runVisitConcatCairoDef (pureTraversal $ generalize general) def
    where general : (rets:List CairoReg) -> LinearImplicitArgs -> (params:List CairoReg) -> Nat
          general _ _ _ = 1
          Semigroup Nat where
            (<+>) a b = a + b
          Monoid Nat where
            neutral = Z

export
countDefsInsts : List (Name, CairoDef) -> Nat
countDefsInsts defs = sum $ map countDefInsts defs
