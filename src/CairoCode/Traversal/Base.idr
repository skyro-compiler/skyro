module CairoCode.Traversal.Base

import CairoCode.CairoCode
import CairoCode.Name
import Data.SortedSet
import Data.SortedMap
import Data.List
import Data.Maybe
import Utils.Lens
import Utils.Helpers
import Debug.Trace

export
data TraversalRes : Type -> Type -> Type  where
  MkTraversalRes : s -> a -> TraversalRes s a

export
data Traversal : Type -> Type -> Type where
  MkTraversal : (s -> TraversalRes s a) -> Traversal s a

export
runTraversal : Traversal s a -> s -> TraversalRes s a
runTraversal (MkTraversal f) = f

getState : TraversalRes s a -> s
getState (MkTraversalRes s a) = s

getValue : TraversalRes s a -> a
getValue (MkTraversalRes s a) = a

export
readState : Traversal s s
readState = MkTraversal (\s => MkTraversalRes s s)

export
writeState : s -> Traversal s ()
writeState sv = MkTraversal (\_ => MkTraversalRes sv ())

export
updateState : (s -> s) -> Traversal s ()
updateState fn = MkTraversal (\s => MkTraversalRes (fn s) ())

-- Note: is only here because needs access to MkTraversal & MkTraversalRes & runTraversal
export
composeState : Lens os is -> Traversal is a -> Traversal os a
composeState lens it = MkTraversal (\osv => let MkTraversalRes is av = runTraversal it (lens.get osv) in MkTraversalRes (lens.set osv is) av)

public export
Functor (Traversal s) where
 map fn (MkTraversal ma) = MkTraversal
    (\s => let MkTraversalRes s' a = ma s in MkTraversalRes s' (fn a))

public export
Applicative (Traversal s) where
    pure a = MkTraversal (\s => MkTraversalRes s a)
    (<*>) (MkTraversal mf) (MkTraversal ma) = MkTraversal
        (\s => let MkTraversalRes s' f = mf s in
        let MkTraversalRes s'' a = ma s' in MkTraversalRes s'' (f a))

public export
Monad (Traversal s) where
    (MkTraversal ma) >>= f = MkTraversal
        (\s => let MkTraversalRes s' a = ma s in runTraversal (f a) s')

public export
data InstVisit : Type -> Type where
      VisitFunction : CairoName -> Maybe (List String) -> (params: List CairoReg) -> (implicits: SortedMap LinearImplicit CairoReg) -> (rets: List CairoReg) -> InstVisit a
      VisitForeignFunction : CairoName -> (info : ForeignInfo) -> (args:Nat) -> (rets:Nat) -> InstVisit a
      VisitAssign : (res:CairoReg) -> a -> InstVisit a
      VisitMkCon : (res:CairoReg) -> Maybe Int -> (args : List a) -> InstVisit a
      VisitMkClosure: (res:CairoReg) -> CairoName -> (missing : Nat) -> (args : List a) -> InstVisit a
      VisitApply : (res:CairoReg) -> (implicits: SortedMap LinearImplicit (a, CairoReg)) -> (f : a) -> (arg : a) -> InstVisit a
      VisitMkConstant : (res:CairoReg) -> CairoConst -> InstVisit a
      VisitCall : List CairoReg -> (implicits: SortedMap LinearImplicit (a, CairoReg)) -> CairoName -> (args : List a) -> InstVisit a
      VisitOp : (res:CairoReg) -> (implicits: SortedMap LinearImplicit (a, CairoReg)) -> CairoPrimFn -> List a -> InstVisit a
      VisitExtprim : List CairoReg -> (implicits: SortedMap LinearImplicit (a, CairoReg)) -> CairoName -> List a -> InstVisit a
      VisitStarkNetIntrinsic : CairoReg -> (implicits: SortedMap LinearImplicit (a, CairoReg))  -> StarkNetIntrinsic -> List a -> InstVisit a
      VisitCase : a -> InstVisit a
      VisitConBranch : Maybe Int -> InstVisit a
      VisitConstBranch : Maybe CairoConst -> InstVisit a
      VisitBranchEnd : InstVisit a
      VisitCaseEnd : InstVisit a
      VisitProject : (res:CairoReg) -> (value : a) -> (pos : Nat) -> InstVisit a
      VisitReturn : List a -> SortedMap LinearImplicit a -> InstVisit a
      VisitNull : (res:CairoReg) -> InstVisit a
      VisitError : (res:CairoReg) -> String -> InstVisit a
      VisitEndFunction : InstVisit a

export
Show a => Show (InstVisit a) where
   show (VisitFunction _ _ _ _ _) = "VisitFunction"
   show (VisitForeignFunction _ _ _ _) = "VisitForeignFunction"
   show (VisitAssign _ _ ) = "VisitAssign"
   show (VisitMkCon _ _ _ ) = "VisitMkCon"
   show (VisitMkClosure _ _ _ _) = "VisitMkClosure"
   show (VisitApply _ _ _ _) = "VisitApply"
   show (VisitMkConstant _ _ ) = "VisitMkConstant"
   show (VisitCall _ _ _ _) = "VisitCall"
   show (VisitOp _ _ _ _) = "VisitOp"
   show (VisitExtprim _ _ _ _) = "VisitExtprim"
   show (VisitStarkNetIntrinsic _ _ _ _) = "VisitStarkNetIntrinsic"
   show (VisitCase _) = "VisitCase"
   show (VisitConBranch _ ) = "VisitConBranch"
   show (VisitConstBranch _ ) = "VisitConstBranch"
   show VisitBranchEnd = "VisitBranchEnd"
   show VisitCaseEnd = "VisitCaseEnd"
   show (VisitProject _ _ _) = "VisitProject"
   show (VisitReturn _ _ ) = "VisitReturn"
   show (VisitNull _ ) = "VisitNull"
   show (VisitError _ _ ) = "VisitError"
   show VisitEndFunction = "VisitEndFunction"

mutual
    export
    fromCairoInst : CairoInst -> List (InstVisit CairoReg)
    fromCairoInst (ASSIGN res src) = [VisitAssign res src]
    fromCairoInst (MKCON res tag args) = [VisitMkCon res tag args]
    fromCairoInst (MKCLOSURE res name missing args) = [VisitMkClosure res name missing args]
    fromCairoInst (APPLY res implicits f a) = [VisitApply res implicits f a]
    fromCairoInst (MKCONSTANT res const) = [VisitMkConstant res const]
    fromCairoInst (CALL res implicits name args) = [VisitCall res implicits name args]
    fromCairoInst (OP res implicits fn args) = [VisitOp res implicits fn args]
    fromCairoInst (EXTPRIM res implicits name args) = [VisitExtprim res implicits name args]
    fromCairoInst (STARKNETINTRINSIC res implicits intr args) = [VisitStarkNetIntrinsic res implicits intr args]
    fromCairoInst (CASE reg alts def) = (VisitCase reg)::(
        (alts >>= (\(t,b) => fromBlock (VisitConBranch (Just t)) b (VisitBranchEnd))) ++
        (fromMaybe [] (map (\b => fromBlock (VisitConBranch Nothing) b (VisitBranchEnd)) def)) ++
        [VisitCaseEnd])
    fromCairoInst (CONSTCASE reg alts def) =  (VisitCase reg)::(
        (alts >>= (\(c,b) => fromBlock (VisitConstBranch (Just c)) b (VisitBranchEnd))) ++
        (fromMaybe [] (map (\b => fromBlock (VisitConstBranch Nothing) b (VisitBranchEnd)) def)) ++
        [VisitCaseEnd])
    fromCairoInst (PROJECT res value pos) = [VisitProject res value pos]
    fromCairoInst (RETURN res implicits) = [VisitReturn res implicits]
    fromCairoInst (NULL res) = [VisitNull res]
    fromCairoInst (ERROR res err) = [VisitError res err]

    fromBlock : InstVisit CairoReg -> List CairoInst -> InstVisit CairoReg -> List (InstVisit CairoReg)
    fromBlock start body end = start::(foldr (\inst,acc => (fromCairoInst inst) ++ acc) [end] body)

export
fromCairoInsts : List CairoInst -> List (InstVisit CairoReg)
fromCairoInsts insts = foldr (\inst,acc => (fromCairoInst inst) ++ acc) [] insts

export
fromCairoDef : (CairoName, CairoDef) -> List (InstVisit CairoReg)
fromCairoDef (name, FunDef params implicits rets body) = fromBlock (VisitFunction name Nothing params implicits rets) body VisitEndFunction
fromCairoDef (name, ExtFunDef tags params implicits rets body) = fromBlock (VisitFunction name (Just tags) params implicits rets) body VisitEndFunction
fromCairoDef (name, ForeignDef info args ret) = [VisitForeignFunction name info args ret, VisitEndFunction]

liftRegLevel : Int -> CairoReg -> CairoReg
liftRegLevel limit r@(Unassigned n no l) = if l > limit then (Unassigned n no (l-1)) else r
liftRegLevel limit r@(Local no l) = if l > limit then (Local no (l-1)) else r
liftRegLevel limit r@(Let no l) = if l > limit then (Let no (l-1)) else r
liftRegLevel limit r@(Temp no l) = if l > limit then (Temp no (l-1)) else r
liftRegLevel _ r = r

liftRegLevels : Int -> List CairoReg -> List CairoReg
liftRegLevels limit = map (liftRegLevel limit)

liftImplicitArgs : Int -> LinearImplicitArgs -> LinearImplicitArgs
liftImplicitArgs limit args = mapValueMap (\(r1,r2) => (liftRegLevel limit r1, liftRegLevel limit r2)) args

mutual
    liftAltRegs : Int -> List (a, List CairoInst) -> List (a, List CairoInst)
    liftAltRegs limit = map (\(s,is) => (s, map (liftInstRegLevel limit) is))

    liftDefRegs : Int ->  Maybe (List CairoInst) ->  Maybe (List CairoInst)
    liftDefRegs limit Nothing = Nothing
    liftDefRegs limit (Just is) = Just $ map (liftInstRegLevel limit) is

    liftInstRegLevel : Int -> CairoInst -> CairoInst
    liftInstRegLevel limit (ASSIGN r arg) = ASSIGN (liftRegLevel limit r) (liftRegLevel limit arg)
    liftInstRegLevel limit (MKCONSTANT r c) = MKCONSTANT (liftRegLevel limit r) c
    liftInstRegLevel limit (OP r impls fn args) = OP (liftRegLevel limit r) (liftImplicitArgs limit impls) fn (liftRegLevels limit args)
    liftInstRegLevel limit (MKCON r tag args) = MKCON (liftRegLevel limit r) tag (liftRegLevels limit args)
    liftInstRegLevel limit (PROJECT r v pos) = PROJECT (liftRegLevel limit r) (liftRegLevel limit v) pos
    liftInstRegLevel limit (MKCLOSURE r n m args) = MKCLOSURE (liftRegLevel limit r) n m (liftRegLevels limit args)
    liftInstRegLevel limit (APPLY r impls fn arg) = APPLY (liftRegLevel limit r) (liftImplicitArgs limit impls) (liftRegLevel limit fn) (liftRegLevel limit arg)
    liftInstRegLevel limit (CALL rs impls n args) = CALL (liftRegLevels limit rs) (liftImplicitArgs limit impls) n (liftRegLevels limit args)
    liftInstRegLevel limit (EXTPRIM rs impls n args) = EXTPRIM (liftRegLevels limit rs) (liftImplicitArgs limit impls) n (liftRegLevels limit args)
    liftInstRegLevel limit (STARKNETINTRINSIC r impls n args) = STARKNETINTRINSIC (liftRegLevel limit r) (liftImplicitArgs limit impls) n (liftRegLevels limit args)
    liftInstRegLevel limit (CASE r alts def) = CASE (liftRegLevel limit r) (liftAltRegs limit alts) (liftDefRegs limit def)
    liftInstRegLevel limit (CONSTCASE r alts def) = CONSTCASE (liftRegLevel limit r) (liftAltRegs limit alts) (liftDefRegs limit def)
    liftInstRegLevel limit (RETURN rs impls) = RETURN (liftRegLevels limit rs) (mapValueMap (liftRegLevel limit) impls)
    liftInstRegLevel limit (NULL r) = NULL (liftRegLevel limit r)
    liftInstRegLevel limit (ERROR r e) = ERROR (liftRegLevel limit r) e

caseInlineOptim : Int -> CairoInst -> List CairoInst
caseInlineOptim _ (CASE reg [] Nothing) = []
caseInlineOptim d (CASE reg [alt] Nothing) = map (liftInstRegLevel d) (snd alt)
caseInlineOptim d (CASE reg Nil (Just def)) = map (liftInstRegLevel d) def
caseInlineOptim _ inst@(CASE reg alts Nothing) = if all (\(i,b) => isNil b) alts then [] else [inst]
caseInlineOptim _ inst@(CASE reg alts (Just [])) = if all (\(i,b) => isNil b) alts then [] else [inst]
caseInlineOptim _ (CONSTCASE reg [] Nothing) = []
caseInlineOptim d (CONSTCASE reg [alt] Nothing) = map (liftInstRegLevel d) (snd alt)
caseInlineOptim d (CONSTCASE reg Nil (Just def)) = map (liftInstRegLevel d) def
caseInlineOptim _ inst@(CONSTCASE reg alts Nothing) = if all (\(c,b) => isNil b) alts then [] else [inst]
caseInlineOptim _ inst@(CONSTCASE reg alts (Just [])) = if all (\(c,b) => isNil b) alts then [] else [inst]
-- it would be nice if this is possible for CASE with defaults as well - but there is not enough info here
caseInlineOptim d orig@(CONSTCASE (Const c1) [(c2, insts)] (Just _)) = if c1 == c2
    then map (liftInstRegLevel d) insts
    else [orig]
caseInlineOptim _ other = [other]

extractDefaultBranch : List a -> Maybe a
extractDefaultBranch Nil = Nothing
extractDefaultBranch (b::Nil) = Just b
extractDefaultBranch _ = assert_total $ idris_crash "More than one default branch found"

mutual
    toCairoCase : Int -> CairoReg -> List (InstVisit CairoReg) -> (CairoInst, List (InstVisit CairoReg))
    toCairoCase d reg ((VisitConBranch t)::xs) = buildRes $ processNextBranch t (toCairoInsts (d+1) xs Nil)
        where processNextBranch : Maybe Int -> (List CairoInst, List (InstVisit CairoReg)) -> (List (Maybe Int, List CairoInst), List (InstVisit CairoReg))
              processNextBranch t (body, VisitCaseEnd::xs) = ([(t,body)],xs)
              processNextBranch t (body, (VisitConBranch nt)::xs) = let (res,rem) = processNextBranch nt (toCairoInsts (d+1) xs Nil) in ((t,body)::res,rem)
              processNextBranch _ _ = assert_total $ idris_crash "Illegal Const Visitor Pattern"
              buildRes : (List (Maybe Int, List CairoInst), List (InstVisit CairoReg)) -> (CairoInst, List (InstVisit CairoReg))
              buildRes (branches, rem) = (CASE reg alts def, rem)
                where alts : List (Int, List CairoInst)
                      alts = branches >>= (\(t,b) => fromMaybe [] (map (\rt => [(rt,b)]) t))
                      def : Maybe (List CairoInst)
                      def = extractDefaultBranch (map (\(_,b) => b) (filter (\(t,_) => isNothing t) branches))

    toCairoCase d reg ((VisitConstBranch c)::xs) = buildRes $ processNextBranch c (toCairoInsts (d+1) xs Nil)
        where processNextBranch : Maybe CairoConst -> (List CairoInst, List (InstVisit CairoReg)) -> (List (Maybe CairoConst, List CairoInst), List (InstVisit CairoReg))
              processNextBranch c (body, VisitCaseEnd::xs) = ([(c,body)],xs)
              processNextBranch c (body, (VisitConstBranch nc)::xs) = let (res,rem) = processNextBranch nc (toCairoInsts (d+1) xs Nil) in ((c,body)::res,rem)
              processNextBranch _ _ = assert_total $ idris_crash "Illegal ConCase Visitor Pattern"
              buildRes : (List (Maybe CairoConst, List CairoInst), List (InstVisit CairoReg)) -> (CairoInst, List (InstVisit CairoReg))
              buildRes (branches, rem) = (CONSTCASE reg alts def, rem)
                where alts : List (CairoConst, List CairoInst)
                      alts = branches >>=  (\(c,b) => fromMaybe [] (map (\rc => [(rc,b)]) c))
                      def : Maybe (List CairoInst)
                      def = extractDefaultBranch (map (\(_,b) => b) (filter (\(c,_) => isNothing c ) branches))

    toCairoCase _ _ _ = assert_total $ idris_crash "Illegal ConstCase Visitor Pattern"

    -- tail recursive over accumulator
    toCairoInsts : Int -> List (InstVisit CairoReg) -> List CairoInst -> (List CairoInst, List (InstVisit CairoReg))
    toCairoInsts _ (VisitBranchEnd::xs) acc = (reverse acc, xs)
    toCairoInsts _ (VisitEndFunction::Nil) acc = (reverse acc, Nil)
    toCairoInsts d ((VisitAssign res src)::xs) acc = toCairoInsts d xs ((ASSIGN res src)::acc)
    toCairoInsts d ((VisitMkCon res tag args)::xs) acc = toCairoInsts d xs ((MKCON res tag args)::acc)
    toCairoInsts d ((VisitMkClosure res name missing args)::xs) acc = toCairoInsts d xs ((MKCLOSURE res name missing args)::acc)
    toCairoInsts d ((VisitApply res implicits f a)::xs) acc = toCairoInsts d xs ((APPLY res implicits f a)::acc)
    toCairoInsts d ((VisitMkConstant res const)::xs) acc = toCairoInsts d xs ((MKCONSTANT res const)::acc)
    toCairoInsts d ((VisitCall res implicits name args)::xs) acc = toCairoInsts d xs ((CALL res implicits name args)::acc)
    toCairoInsts d ((VisitOp res implicits fn args)::xs) acc = toCairoInsts d xs ((OP res implicits fn args)::acc)
    toCairoInsts d ((VisitExtprim res implicits name args)::xs) acc = toCairoInsts d xs ((EXTPRIM res implicits name args)::acc)
    toCairoInsts d ((VisitStarkNetIntrinsic res implicits intr args)::xs) acc = toCairoInsts d xs ((STARKNETINTRINSIC res implicits intr args)::acc)
    toCairoInsts d ((VisitCase reg)::(VisitCaseEnd)::xs) acc = toCairoInsts d xs acc
    toCairoInsts d ((VisitCase reg)::xs) acc = let (cI, rem) = toCairoCase d reg xs in toCairoInsts d rem ((reverse $ caseInlineOptim d cI) ++ acc)
    toCairoInsts d ((VisitProject res value pos)::xs) acc = toCairoInsts d xs ((PROJECT res value pos)::acc)
    toCairoInsts d ((VisitReturn res implicits)::xs) acc = toCairoInsts d xs ((RETURN res implicits)::acc)
    toCairoInsts d ((VisitNull res)::xs) acc = toCairoInsts d xs ((NULL res)::acc)
    toCairoInsts d ((VisitError res err)::xs) acc = toCairoInsts d xs ((ERROR res err)::acc)
    toCairoInsts _ _ _ = assert_total $ idris_crash "Illegal Visitor Pattern"

extractResult : (List CairoInst, List (InstVisit CairoReg)) -> List CairoInst
extractResult (is, Nil) = is
extractResult _ = assert_total $ idris_crash "Not fully parsed"

export
toCairoDef : List (InstVisit CairoReg) -> (CairoName, CairoDef)
toCairoDef ((VisitForeignFunction name info args ret)::VisitEndFunction::Nil) = (name, ForeignDef info args ret)
toCairoDef ((VisitFunction name (Just tags) params implicits rets)::VisitEndFunction::Nil) = (name, ExtFunDef tags params implicits rets [])
toCairoDef ((VisitFunction name Nothing params implicits rets)::xs) = (name, FunDef params implicits rets (extractResult (toCairoInsts 0 xs [])))
toCairoDef ((VisitFunction name (Just tags) params implicits rets)::xs) = (name, ExtFunDef tags params implicits rets (extractResult (toCairoInsts 0 xs [])))
toCairoDef _ = assert_total $ idris_crash "Visitor Pattern must start with a function declaration"

export
visitCairoDef : (InstVisit CairoReg -> Traversal s ()) -> (CairoName, CairoDef) -> Traversal s ()
visitCairoDef fn def = foldlM (\_,iv => fn iv) () (fromCairoDef def)

export
visitCairoDefs : (InstVisit CairoReg -> Traversal s ()) -> List (CairoName, CairoDef) -> Traversal s ()
visitCairoDefs fn defs = foldlM (\_,def => visitCairoDef fn def) () defs

export
runVisitCairoDef : (InstVisit CairoReg -> Traversal s (), s) -> (CairoName, CairoDef) -> s
runVisitCairoDef (fn, init) def = getState $ runTraversal (visitCairoDef fn def) init

export
runVisitCairoDefs : (InstVisit CairoReg -> Traversal s (), s) -> List (CairoName, CairoDef) -> s
runVisitCairoDefs (fn, init) defs = getState $ runTraversal (visitCairoDefs fn defs) init

export
visitConcatCairoDef : Monoid m => (InstVisit CairoReg -> Traversal s m) -> (CairoName, CairoDef) -> Traversal s m
visitConcatCairoDef fn def = foldlM (\acc,iv => map (acc <+>) (fn iv)) neutral (fromCairoDef def)

export
visitConcatCairoDefs : Monoid m => (InstVisit CairoReg -> Traversal s m) -> List (CairoName, CairoDef) -> Traversal s m
visitConcatCairoDefs fn defs  = foldlM (\acc,def => map (acc <+>) (visitConcatCairoDef fn def)) neutral defs

export
runVisitConcatCairoDef : Monoid m => (InstVisit CairoReg -> Traversal s m, s) -> (CairoName, CairoDef) -> (s, m)
runVisitConcatCairoDef (fn, init) def = let res = runTraversal (visitConcatCairoDef fn def) init in (getState res, getValue res)

export
runVisitConcatCairoDefs : Monoid m => (InstVisit CairoReg -> Traversal s m, s) -> List (CairoName, CairoDef) -> (s, m)
runVisitConcatCairoDefs (fn, init) defs = let res = runTraversal (visitConcatCairoDefs fn defs) init in (getState res, getValue res)

export
runVisitTransformCairoDef : (InstVisit CairoReg -> Traversal s (List (InstVisit CairoReg)), s) -> (CairoName, CairoDef) -> (s, (CairoName, CairoDef))
runVisitTransformCairoDef (fn, init) def = let res = runTraversal (visitConcatCairoDef fn def) init in (getState res, toCairoDef $ getValue res)

export
runVisitTransformCairoDefs : (InstVisit CairoReg -> Traversal s (List (InstVisit CairoReg)), s) -> List (CairoName, CairoDef) -> (s, List (CairoName, CairoDef))
runVisitTransformCairoDefs (fn, init) defs = foldl (\(s,acc),def => let (ns,res) = runVisitTransformCairoDef (fn,s) def in (ns, acc ++ [res])) (init,[]) defs

export
lift : (InstVisit a -> b) -> (InstVisit a -> Traversal s b)
lift fn = (\inst => pure $ fn inst)


-- This is the standard and just here for completness
-- use-examples: runVisitCairoDef (rawTraversal myTraverser myInitialState) def
--               runVisitConcatCairoDef (rawTraversal myTraverser myInitialState)  def
--               runVisitTransformCairoDef (traversal myTransformer myInitialState) def

export
rawTraversal : (InstVisit CairoReg -> Traversal s a) -> s -> (InstVisit CairoReg -> Traversal s a, s)
rawTraversal fn s = (fn, s)

-- This is the standard case with a monoidic state
-- use-examples: runVisitCairoDef (traversal myTraverser) def
--               runVisitConcatCairoDef (traversal myTraverser) def
--               runVisitTransformCairoDef (traversal myTransformer) def
export
traversal : Monoid s => (InstVisit CairoReg -> Traversal s a) -> (InstVisit CairoReg -> Traversal s a, s)
traversal fn = (fn, neutral)

-- This is the statelessTraversal and just here for completness
-- use-examples: runVisitCairoDef (pureTraversal myTraverser) def
--               runVisitConcatCairoDef (pureTraversal myTraverser)  def
--               runVisitTransformCairoDef (pureTraversal myTransformer) def

export
pureTraversal : (InstVisit a -> b) -> (InstVisit a -> Traversal () b, ())
pureTraversal fn = (lift fn, ())

-- Helper to work with lenses (L is for lense)
export
readStateL : Lens w p -> Traversal w p
readStateL lens = map lens.get readState

export
updateStateL : Lens w p -> (p -> p) -> Traversal w ()
updateStateL lens fn = updateState (\wv => lens.update wv fn)

export
writeStateL : Lens w p -> p -> Traversal w ()
writeStateL lens pv = updateStateL lens (\_ => pv)

stateCompL : Lens w p -> (p -> (p,r)) -> Traversal w r
stateCompL lens fn = do
    sv <- readStateL lens
    let (nsv, res) = fn sv
    _ <- writeStateL lens nsv
    pure res
