module CairoCode.Checker

import CairoCode.Name
import CairoCode.CairoCode
import Data.SortedMap
import Data.SortedSet
import Utils.Helpers
import Data.Either
import Data.List
import Data.Maybe
import Primitives.Primitives

import Debug.Trace

%hide Prelude.toList

record FunInfo where
    constructor MKFunInfo
    args : Int
    impls : SortedSet LinearImplicit


record Tracker where
    constructor MKTracker
    returned : Maybe Int
    regs : SortedMap CairoReg Int
    funs : SortedMap CairoName (Int, SortedSet LinearImplicit)

tracker : SortedMap CairoName (Int, SortedSet LinearImplicit) -> Tracker
tracker = MKTracker Nothing empty

data Checker : Type where
    Valid : Tracker -> Checker
    Invalid : SortedSet String -> Checker

mergeRegs : Int -> SortedMap CairoReg Int -> SortedMap CairoReg Int -> Either String (SortedMap CairoReg Int)
mergeRegs depth regs1 regs2 = foldl computeValue (Right empty) (union (fromList (keys regs1)) (fromList (keys regs2)))
    where computeValue : Either String (SortedMap CairoReg Int) -> CairoReg -> Either String (SortedMap CairoReg Int)
          computeValue (Left err) reg = Left err
          computeValue (Right res) reg = case (lookup reg regs1, lookup reg regs2) of
            (Nothing, Just v) => let l = (level reg) in if l <= depth || v <= depth
                then Left "Register \{show reg} is not assigned in all branches"
                else Right res
            (Just v, Nothing) => let l = (level reg) in if l <= depth || v <= depth
                then Left "Register \{show reg} is not assigned in all branches"
                else Right res
            (Just d1, Just d2) => Right $ insert reg (min d1 d2) res
            _ => assert_total $ idris_crash "can not happen"

mergeBranch : Int -> Checker -> Checker -> Checker
mergeBranch _ (Invalid r1) (Invalid r2) = Invalid (r1 <+> r2)
mergeBranch _ (Invalid r1) _ = Invalid r1
mergeBranch _ _ (Invalid r2) = Invalid r2
mergeBranch depth (Valid t1) (Valid t2) = if t1.returned /= t2.returned
    then Invalid $ singleton "each branch must end in a return or none must"
    else case mergeRegs depth t1.regs t2.regs of
        (Left err) =>  Invalid $ singleton err
        (Right res) => Valid $ { regs := res} t1

mergeBranches : Int -> List Checker -> Checker
mergeBranches _ Nil = Invalid $ singleton "Can not merge case without branches"
mergeBranches depth (c::cs) = foldl (mergeBranch depth) c cs

useRawReg : Int -> Checker -> CairoReg -> Checker
useRawReg _ e@(Invalid _) _ = e
useRawReg d1 (Valid tr) reg = case lookup reg tr.regs of
    Nothing => Invalid $ singleton "Register \{show reg} is not active"
    (Just d2) => let l = level reg in if d2 < l || d1 < l
        then Invalid $ singleton "Register \{show reg} is is used on a smaller level"
        else Valid ({regs $= insert reg (min d1 d2)} tr)

useReg : Int -> Checker -> CairoReg -> Checker
useReg _ e@(Invalid _) _ = e
useReg _ checker (Eliminated Null) = checker
useReg _ _ r@(Eliminated _) = Invalid $ singleton "Register \{show r} is eliminated and can not be used as parameter"
useReg _ checker r@(Const _) = checker
useReg depth checker reg = useRawReg depth checker reg

recordReturn : Int -> Checker -> List CairoReg -> Checker
recordReturn depth c regs = case (foldl (useReg depth) c regs) of
     (Valid tr) => if isJust tr.returned
        then Invalid $ singleton "Can not return more than once from a function"
        else Valid ({returned := Just $ cast $ length regs} tr)
     e => e

rawDefReg : Int -> Checker -> CairoReg -> Checker
rawDefReg _ e@(Invalid _) _ = e
rawDefReg depth (Valid tr) reg = if isJust tr.returned
    then Invalid $ singleton "Return must be in tail position"
    else case lookup reg tr.regs of
        Nothing => if depth < (level reg)
            then Invalid $ singleton "Register \{show reg} is is defined on a smaller level"
            else Valid ({regs $= insert reg depth} tr)
        (Just _) => Invalid $ singleton "Register \{show reg} is already active"

defReg : Int -> Checker -> CairoReg -> Checker
defReg depth check r@(Const _) = Invalid $ singleton "Register \{show r} must be assigned from a MKCONSTANT"
defReg depth check r@(Eliminated _) = check
defReg depth check reg = rawDefReg depth check reg

defConst : Int -> CairoConst -> Checker -> CairoReg -> Checker
defConst _ _ e@(Invalid _) _ = e
defConst depth c1 check r@(Const c2) = if c1 /= c2
    then Invalid $ singleton "Cannot assign constant \{show c1} to register \{show r}"
    else rawDefReg depth check r
defConst depth _ check r = defReg depth check r

linImplInputs : LinearImplicitArgs -> List CairoReg
linImplInputs impls = map fst (values impls)

linImplOutputs : LinearImplicitArgs -> List CairoReg
linImplOutputs impls = map snd (values impls)

-- todo: Shall we merge with Filter??
checkTargetParams : CairoName -> Int -> Checker -> Checker
checkTargetParams name args e@(Invalid _) = e
checkTargetParams name args (Valid tr) = case lookup name tr.funs of
    Nothing => Invalid $ singleton "Function \{show name} does not exist"
    (Just (args2, _)) => if args == args2
        then Valid tr
        else Invalid $ singleton "Function \{show name} is called with \{show args} instead of \{show args2}"

-- We need to allow passing Eliminated Regs as function argument as param list allow eliminated regs (as long not used)
-- Todo: shall we track that target is really eliminated
nullifyEliminatedRegs : List CairoReg -> List CairoReg
nullifyEliminatedRegs args = map nullify args
    where nullify : CairoReg -> CairoReg
          nullify (Eliminated _) = Eliminated Null
          nullify r = r

{-
-- Todo: Not yet used, may be tricky if injector is not yet run as foreign functions already have the information
checkTargetImpls : CairoName -> SortedSet LinearImplicits -> Checker -> Checker
checkTargetImpls name impls e@(Invalid _) = e
checkTargetImpls name impls (Valid tr) = case lookup name tr.funs of
    Nothing => Invalid $ singleton "Function \{show name} does not exist"
    (Just (_, impls2)) => if impls == impls2
        then Valid tr
        else Invalid $ singleton "Function \{show name} is called with implicits \{show impls} instead of \{show impls2}"
-}

-- Todo: in theory we could allow assign to const if sources are const (but this needs opcode interpretation here
checkOp : Int -> Checker -> CairoReg -> LinearImplicitArgs -> CairoPrimFn -> List CairoReg -> Checker
checkOp depth c r linImpl fn args = foldl (defReg depth) (foldl (useReg depth) (checkOpArity fn args) (args ++ (linImplInputs linImpl))) (r::(linImplOutputs linImpl))
    where checkedLinearity : Checker
          checkedLinearity = let expected = primFnLinearImplicits fn in if all (\l => contains l expected) (keys linImpl)
            then c
            else Invalid $ singleton "Unexpected implicits for \{show fn}"
          checkOpArity : CairoPrimFn -> List CairoReg -> Checker
          checkOpArity (Neg _) [_] = checkedLinearity
          checkOpArity BelieveMe [_,_,_] = checkedLinearity
          checkOpArity (Cast _ _) [_] = checkedLinearity
          -- Rest are bBinOps
          checkOpArity _ [_,_] = checkedLinearity
          checkOpArity _ _ = Invalid $ singleton "Operand \{show fn} has wrong number of arguments"


-- Todo: can we check implicit consistency
checkIntrinsic : Int -> Checker -> CairoReg -> LinearImplicitArgs -> StarkNetIntrinsic -> List CairoReg -> Checker
checkIntrinsic depth c r linImpl intr args = foldl (defReg depth) (foldl (useReg depth) (checkOpArity intr args) (args ++ (linImplInputs linImpl))) (r::(linImplOutputs linImpl))
    where checkOpArity : StarkNetIntrinsic -> List CairoReg -> Checker
          checkOpArity (StorageVarAddr _) [] = c
          checkOpArity (EventSelector _) [] = c
          checkOpArity (FunctionSelector _) [] = c
          checkOpArity _ _ = Invalid $ singleton "Intrinsic \{show intr} has wrong number of arguments"


mutual
    checkInst : Int -> Checker -> CairoInst -> Checker
    checkInst _ e@(Invalid _) _ = e
    checkInst depth c (ASSIGN r s@(Const const)) = defConst depth const (useReg depth c s) r
    checkInst depth c (ASSIGN r s) = defReg depth (useReg depth c s) r
    checkInst depth c (MKCONSTANT r const) = defConst depth const c r
    checkInst depth c (OP r linImpl fn args) = checkOp depth c r linImpl fn args
    checkInst depth c (MKCON r _ args) = defReg depth (foldl (useReg depth) c args) r
    checkInst depth c (PROJECT r arg _ ) = defReg depth (useReg depth c arg) r
    -- The currier can change closure signature using a hidden pack so we can no longer check arity
    checkInst depth c (MKCLOSURE r name@(Extension "curried" _ rest) miss args) = defReg depth (foldl (useReg depth) c (nullifyEliminatedRegs args)) r
    checkInst depth c (MKCLOSURE r name miss args) = defReg depth (foldl (useReg depth) (checkTargetParams name (cast (length args + miss)) c) (nullifyEliminatedRegs args)) r
    checkInst depth c (APPLY r linImpl f a) = foldl (defReg depth) (foldl (useReg depth) c (f::a::(linImplInputs linImpl))) (r::(linImplOutputs linImpl))
    checkInst depth c (CALL rs linImpl name args ) = foldl (defReg depth) (foldl (useReg depth) (checkTargetParams name (cast $ length args) c) ((nullifyEliminatedRegs args) ++ (linImplInputs linImpl))) (rs ++ (linImplOutputs linImpl))
    -- Todo: can we check argNo and existence (does this need extra stuff on external interface?)
    checkInst depth c (EXTPRIM rs linImpl name args ) = foldl (defReg depth) (foldl (useReg depth) c (args ++ (linImplInputs linImpl))) (rs ++ (linImplOutputs linImpl))
    checkInst depth c (STARKNETINTRINSIC r linImpl intr args) = checkIntrinsic  depth c r linImpl intr args
    checkInst depth c (CASE b alts def) = mergeBranches depth (map (checkInsts (depth+1) (useReg depth c b)) ((map snd alts) ++ (catMaybes [def])))
    checkInst depth c (CONSTCASE b alts def) = mergeBranches depth (map (checkInsts (depth+1) (useReg depth c b)) ((map snd alts) ++ (catMaybes [def])))
    checkInst depth c (RETURN rs linImpl) = recordReturn depth (foldl (useReg depth) c (values linImpl)) rs
    checkInst depth c (NULL (Eliminated Null)) = c
    checkInst depth c (NULL r) = defReg depth c r
    checkInst depth c (ERROR (Eliminated _) _) = c
    checkInst depth c (ERROR r _) = rawDefReg depth c r

    checkInsts : Int -> Checker -> List CairoInst -> Checker
    checkInsts depth c insts = foldl (checkInst depth) c insts

warning : String -> Bool
warning s = trace "warning: \{s}" True

error : String -> Bool
error s = trace "error: \{s}" False -- assert_total $ idris_crash "error: \{s}"

validateRes : CairoName -> Int -> Checker -> Bool
validateRes ctx rets (Valid tr) = if tr.returned == (Just rets)
    then True
    else error "The function \{show ctx} must return the number of values on each possible path"
validateRes _ rets (Invalid e) = any error (toList e)

checkDef : SortedMap CairoName (Int, SortedSet LinearImplicit) -> (CairoName, CairoDef) -> Bool
checkDef funs (name, FunDef args impls rets code) = validateRes name (cast $ length rets) (checkInsts 0 (foldl (defReg 0) (Valid $ tracker funs) (args ++ (values impls))) code)
checkDef _ (_, ExtFunDef _ _ _ _ Nil) = True -- external functions without code are allowed (used in Cairo ABI)
checkDef funs (name, ExtFunDef _ args impls rets code) = validateRes name (cast $ length rets) (checkInsts 0 (foldl (defReg 0) (Valid $ tracker funs) (args ++ (values impls))) code)
checkDef _ (_, _) = True


export
integrityCheck : List (CairoName, CairoDef) -> CairoName -> Bool
integrityCheck defs name = case (find (\(n,_) => n == name) defs) of
        Nothing => False
        (Just def) => let paramMap = foldl funParams empty defs in checkDef paramMap def
    -- todo: if we keep dedup
    where funParams : SortedMap CairoName (Int, SortedSet LinearImplicit) -> (CairoName, CairoDef) -> SortedMap CairoName (Int, SortedSet LinearImplicit)
          funParams acc (n, FunDef params impls _ _) = insert n (cast $ length params, fromList $ keys impls) acc
          funParams acc (n, ForeignDef info params _ ) = insert n (cast params,  fromList $ info.implicits) acc
          funParams acc (_, ExtFunDef _ _ _ _ _) = acc

export
checkDefs : List (CairoName, CairoDef) -> Bool
checkDefs defs = let paramMap = foldl funParams empty defs in all (checkDef paramMap) defs
    -- todo: check names are unique
    where funParams : SortedMap CairoName (Int, SortedSet LinearImplicit) -> (CairoName, CairoDef) -> SortedMap CairoName (Int, SortedSet LinearImplicit)
          funParams acc (n, FunDef params impls _ _) = insert n (cast $ length params, fromList $ keys impls) acc
          funParams acc (n, ForeignDef info params _ ) = insert n (cast params,  fromList $ info.implicits) acc
          funParams acc (_, ExtFunDef _ _ _ _ _) = acc

public export
integrityCheckDefs : List (CairoName, CairoDef) ->  List (CairoName, CairoDef)
integrityCheckDefs defs = case checkDefs defs of
    True => defs
    False => trace (show defs) defs -- assert_total $ idris_crash "integrity check failed"
