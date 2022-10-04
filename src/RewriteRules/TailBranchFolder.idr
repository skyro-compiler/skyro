module RewriteRules.TailBranchFolder

import Utils.Helpers
import CairoCode.CairoCode
import CairoCode.Name
import CairoCode.CairoCodeUtils
import Data.SortedMap
import Data.SortedSet
import Data.Maybe

%hide Prelude.toList

-- This is a really aggresive tail brancher just to see the effect

insertReg : CairoReg -> SortedSet CairoReg -> SortedSet CairoReg
insertReg (Const _) regs = regs
insertReg (Eliminated _) regs = regs
insertReg reg regs = insert reg regs

insertRegs : List CairoReg -> SortedSet CairoReg -> SortedSet CairoReg
insertRegs rs regs = foldr insertReg regs rs

insertImpls : LinearImplicitArgs -> SortedSet CairoReg -> SortedSet CairoReg
insertImpls impls regs = foldl (\acc,(_,t) => insertReg t acc) regs (values impls)

findInlinedRegs : List CairoInst -> SortedSet CairoReg -> SortedSet CairoReg
findInlinedRegs ((ASSIGN reg _)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((MKCONSTANT reg _)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((OP reg impls _ _)::xs) regs = findInlinedRegs xs (insertReg reg (insertImpls impls regs))
findInlinedRegs ((MKCON reg _ _)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((PROJECT reg _ _)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((MKCLOSURE reg _ _ _)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((APPLY reg impls _ _)::xs) regs = findInlinedRegs xs (insertReg reg (insertImpls impls regs))
findInlinedRegs ((CALL rs impls _ _)::xs) regs = findInlinedRegs xs (insertRegs rs (insertImpls impls regs))
findInlinedRegs ((EXTPRIM rs impls _ _)::xs) regs = findInlinedRegs xs (insertRegs rs (insertImpls impls regs))
findInlinedRegs ((STARKNETINTRINSIC reg impls _ _)::xs) regs = findInlinedRegs xs (insertReg reg (insertImpls impls regs))
findInlinedRegs ((NULL reg)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((ERROR reg _)::xs) regs = findInlinedRegs xs (insertReg reg regs)
findInlinedRegs ((RETURN _ _)::xs) regs = findInlinedRegs xs regs
findInlinedRegs ((CASE _ brs Nothing)::xs) regs = findInlinedRegs xs (foldl (\rs,(_,is) => findInlinedRegs is rs) regs brs)
findInlinedRegs ((CASE _ brs (Just d))::xs) regs = findInlinedRegs xs (foldl (\rs,(_,is) => findInlinedRegs is rs) (findInlinedRegs d regs) brs)
findInlinedRegs ((CONSTCASE _ brs Nothing)::xs) regs = findInlinedRegs xs (foldl (\rs,(_,is) => findInlinedRegs is rs) regs brs)
findInlinedRegs ((CONSTCASE _ brs (Just d))::xs) regs = findInlinedRegs xs (foldl (\rs,(_,is) => findInlinedRegs is rs) (findInlinedRegs d regs) brs)
findInlinedRegs Nil regs = regs

doSubst : SortedMap CairoReg CairoReg -> List CairoInst -> List CairoInst
doSubst substMap inst = innerSubst Nil inst
    where subReg : CairoReg -> CairoReg
          subReg r = fromMaybe r (lookup r substMap)
          subRegs : List CairoReg -> List CairoReg
          subRegs rs = map subReg rs
          subImpls : LinearImplicitArgs -> LinearImplicitArgs
          subImpls impls = mapValueMap (\(f,t) => (subReg f, subReg t)) impls
          innerSubst : List CairoInst ->  List CairoInst ->  List CairoInst
          innerSubst acc ((ASSIGN r a)::insts) = innerSubst ((ASSIGN (subReg r) (subReg a))::acc) insts
          innerSubst acc ((MKCONSTANT r c)::insts) = innerSubst ((MKCONSTANT (subReg r) c)::acc) insts
          innerSubst acc ((OP r impls fn args)::insts) = innerSubst ((OP (subReg r) (subImpls impls) fn (subRegs args))::acc) insts
          innerSubst acc ((MKCON r t args)::insts) = innerSubst ((MKCON (subReg r) t (subRegs args))::acc) insts
          innerSubst acc ((PROJECT r v p)::insts) = innerSubst ((PROJECT (subReg r) (subReg v) p)::acc) insts
          innerSubst acc ((MKCLOSURE r n m args)::insts) = innerSubst ((MKCLOSURE (subReg r) n m (subRegs args))::acc) insts
          innerSubst acc ((APPLY r impls f a)::insts) = innerSubst ((APPLY (subReg r) (subImpls impls) (subReg f) (subReg a))::acc) insts
          innerSubst acc ((CALL rs impls n args)::insts) = innerSubst ((CALL (subRegs rs) (subImpls impls) n (subRegs args))::acc) insts
          innerSubst acc ((EXTPRIM rs impls n args)::insts) = innerSubst ((EXTPRIM (subRegs rs) (subImpls impls) n (subRegs args))::acc) insts
          innerSubst acc ((STARKNETINTRINSIC r impls n args)::insts) = innerSubst ((STARKNETINTRINSIC (subReg r) (subImpls impls) n (subRegs args))::acc) insts
          innerSubst acc ((RETURN rs impls)::insts) = innerSubst ((RETURN (subRegs rs) (mapValueMap subReg impls))::acc) insts
          innerSubst acc ((NULL r)::insts) = innerSubst ((NULL (subReg r))::acc) insts
          innerSubst acc ((ERROR r e)::insts) = innerSubst ((ERROR (subReg r) e)::acc) insts
          innerSubst acc ((CASE r alts def)::insts) = innerSubst ((CASE (subReg r) (map (\(t,is) => (t, doSubst substMap is)) alts) (maybeMap (doSubst substMap) def))::acc) insts
          innerSubst acc ((CONSTCASE r alts def)::insts) = innerSubst ((CONSTCASE (subReg r) (map (\(c,is) => (c, doSubst substMap is)) alts) (maybeMap (doSubst substMap) def))::acc) insts
          innerSubst acc Nil = reverse acc


localizeRegs : RegisterGen -> SortedSet CairoReg -> List CairoInst ->  List CairoInst
localizeRegs regGen cands = doSubst (fromList $ snd $ foldl compSubst (regGen,Nil) (toList cands))
  where compSubst : (RegisterGen, List (CairoReg,CairoReg)) -> CairoReg -> (RegisterGen, List (CairoReg,CairoReg))
        compSubst (rg,acc) r = let (nR,nRg) = nextRegister rg ((level r) +1) in (nRg, (r,nR)::acc)

mutual
    inlineBranch : RegisterGen -> Int -> SortedSet CairoReg ->  List CairoInst ->  List CairoInst ->  List CairoInst
    inlineBranch regGen depth tailRegs oldInsts newInsts = let (cRg,rRg) = splitRegisterGen regGen in
        let headRegs = setFilter (\r => (level r) == depth) (findInlinedRegs oldInsts empty) in
        let brInsts = localizeRegs rRg (union tailRegs headRegs) (oldInsts ++ newInsts) in
        tailBranching cRg (depth+1) brInsts

    tailBranching : RegisterGen -> Int -> List CairoInst -> List CairoInst
    tailBranching regGen depth ((CASE r alts def)::xs) = let tailRegs = findInlinedRegs xs empty in
        [CASE r (map (\(t,insts) => (t, inlineBranch (branchRegisterGen (Just t) regGen) depth tailRegs insts xs)) alts) (maybeMap (\insts => inlineBranch regGen depth tailRegs insts xs) def)]

    tailBranching regGen depth ((CONSTCASE r alts def)::xs) = let tailRegs = findInlinedRegs xs empty in
        [CONSTCASE r (map (\(c,insts) => (c, inlineBranch (branchRegisterGen (Just c) regGen) depth tailRegs insts xs)) alts) (maybeMap (\insts => inlineBranch regGen depth tailRegs insts xs) def)]

    tailBranching regGen depth (inst::xs) = inst::(tailBranching regGen depth xs) -- this is just for testing, tail recursive vesrion would be better
    tailBranching _ _ Nil = Nil

export
tailBranchDef : (CairoName, CairoDef) -> (CairoName, CairoDef)
tailBranchDef (name, FunDef params implicits rets body) = orderUnassignedRegIndexes (name, FunDef params implicits rets (tailBranching (mkRegisterGen "tailBranching") 0 body))
tailBranchDef (name, ExtFunDef tags params implicits rets body) = (name, ExtFunDef tags params implicits rets (tailBranching (mkRegisterGen "tailBranching") 0 body))
tailBranchDef def = def

export
tailBranch : List (CairoName, CairoDef) -> List (CairoName, CairoDef)
tailBranch defs = map tailBranchDef defs
