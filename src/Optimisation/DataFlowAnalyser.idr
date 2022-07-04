module Optimisation.DataFlowAnalyser

import Core.Context

import Utils.Helpers
import CairoCode.Traversal.Base
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CommonDef
import Data.SortedSet
import Data.SortedMap

import Debug.Trace

%hide Prelude.toList

-- It is intended to run after other optimisations as it does not handle closures well
--  It treats every functions parameters and returns that can be the target of an apply as Escaping (Unknown Structure & Sources / Sinks)
--  It does the same with EXtFuns & ForeignFuns & Extprims (the last could be improved upon for certain Extprims)

-- A Unification based approach is used that collects groups of registers that can be aliased
--  Meaning: they can share a sink (consumer of values) or a source (creator of values9
--           the algorithm is bidirectional, meaning it does not compute if 2 registers are only sink or only source aliased
--  Additionally the Algorithm collects the structure of the values the register can contain

-- The Approach is based on a Hindley Millner like type Inferenz Algorithm.
-- The algorithm is designed for simplicity not efficency
--   If memory becomes a problem A gc pass can be made after each function that resolves all register mappings and then removes unreachable SVars and Structures
--   If performance becomes a problem then another alg may be better - or at least do not generate intermidiary Unified entries (however makes the unifiers less elegant)
-- Structural Variable used to identify a Group of Registers with the same Structure that can be aliases of each other
public export
record GlobalReg where
    constructor MkGlobalReg
    function : Name
    register : CairoReg

public export
Eq GlobalReg where (==) (MkGlobalReg f1 r1) (MkGlobalReg f2 r2) = f1 == f2 && r1 == r2

public export
Show GlobalReg where show (MkGlobalReg f r) = (show f) ++ "[" ++ (show r) ++"]"

public export
Ord GlobalReg where compare (MkGlobalReg f1 r1) (MkGlobalReg f2 r2) = thenCompare (compare f1 f2) (compare r1 r2)

mapCReg : (CairoReg -> CairoReg) -> GlobalReg -> GlobalReg
mapCReg fn (MkGlobalReg f r) = MkGlobalReg f (fn r)

-- Structural Variable used to identify a Group of Registers with the same Structure that can be aliases of each other
SVar : Type
SVar = Nat

RegisterMapping : Type
RegisterMapping = SortedMap GlobalReg SVar

-- Used so we can Unify Closures and Variants and Records
public export
data Tag : Type where
   Ctr : Int -> Tag
   Clo : Name -> Tag
   All : Tag                -- Is used when a project accesses a field but we actually do not know what the tag is
                            -- At the end we need to unify everything in All with each Ctr & Clo
                            -- Alternative we could do on the fly while unifying the tags

Show Tag where
    show (Ctr t) = "[Ctr "++(show t)++"]"
    show (Clo n) = "[Clo "++(show n)++"]"
    show All = "[All]"

Eq Tag where
    (==) (Ctr t1) (Ctr t2) = t1 == t2
    (==) (Clo t1) (Clo t2) = t1 == t2
    (==) All All = True
    (==) _ _ = False

Ord Tag where
    compare All All = EQ
    compare All _ = GT
    compare _ All = LT
    compare (Ctr t1) (Ctr t2) = compare t1 t2
    compare (Ctr _) _ = GT
    compare _ (Ctr _) = LT
    compare (Clo t1) (Clo t2) = compare t1 t2

-- Structure (Similar to Scheme/Type in a Hindley Milner)
public export
data Structure : Type where
    Escaped : Structure                                             -- This leaves known context (External / Apply / Foreign)
    FieldEscape : Structure                                         -- This represents a Composite where the Fields Escape
    Free : Structure                                                -- The Structure of this is not yet known
    -- Should only be used with fresh SVars or cycle risk
    Unified : SVar -> Structure                                     -- This has the same Structure as whatever SVar ends up having (and is in the same group)
    Composite : SortedMap Tag (SortedMap Nat SVar) -> Structure     -- This is a composite value with 1 or more constructors that each have fields
    Primitive : CairoConst -> Structure                             -- This is of a known primitive type
    Error : Structure                                               -- Represents a unification error for example if something seems to be a number and Composite at the same time
                                                                    --  Note: Because of Idris Dependent typing this can happen in valid code. However in that case Optimization is tricky and we ignore it.

Show Structure where
    show Escaped = "Escaped"
    show FieldEscape = "FieldEscape"
    show Free = "Free"
    show (Unified s) = "Unified: "++(show s)
    show (Composite ctrs) = "Composite: "++(show ctrs)
    show (Primitive c) = "Primitive: "++(show c)
    show Error = "Error"

-- Todo: find out where this is used because its not fully correct
Eq Structure where
    (==) Escaped Escaped = True
    (==) FieldEscape FieldEscape = True
    (==) Free Free = True
    (==) Error Error = True
    -- for correctness we need to resolve sv1 & sv2 before comparing
    -- however it holds after a gc
    (==) (Unified sv1) (Unified sv2) = sv1 == sv2
    (==) (Composite ctrs1) (Composite ctrs2) = ctrs1 == ctrs2
    (==) (Primitive c1) (Primitive c2) = c1 == c2
    (==) _ _ = False

StructureMapping : Type
StructureMapping = SortedMap SVar Structure

record SignatureRegs where
     constructor MkSigRegs
     params : List GlobalReg
     returns : List GlobalReg
     implsIn : SortedMap LinearImplicit GlobalReg
     implsOut : SortedMap LinearImplicit GlobalReg

Show SignatureRegs where
    show (MkSigRegs p r ii ip) = "MkSigRegs: params="++(show p)++", returns="++(show r)

-- Todo put this somwhere general
public export
record CaseTracker where
     constructor MkCTrack
     bindStack : List (GlobalReg, Maybe Tag)
     rewindBind: List (SortedMap GlobalReg Tag)
     bindMap : SortedMap GlobalReg Tag
     
record Environment where
     constructor MkEnv
     generator : Nat
     registers : RegisterMapping
     structures : StructureMapping
     defSigs : SortedMap Name SignatureRegs
     caseTracker : CaseTracker

genSVar : Environment -> (SVar, Environment)
genSVar env = (env.generator, { generator := S env.generator} env)

mapSVar : SVar -> Structure -> Environment -> Environment
mapSVar v s = { structures $= insert v s }

mapReg : GlobalReg -> SVar -> Environment -> Environment
mapReg r v = { registers $= insert r v }

mapSig : Name -> SignatureRegs -> Environment -> Environment
mapSig n s = { defSigs $= insert n s }

public export
pushCase : GlobalReg -> CaseTracker -> CaseTracker
pushCase gr = { bindStack $= ((gr, Nothing)::)}

public export
pushBranch : Maybe Tag -> CaseTracker -> CaseTracker
pushBranch Nothing track = track
pushBranch (Just t) track = case track.bindStack of
    ((gr,_)::xs) => { rewindBind $= (track.bindMap::), bindStack := ((gr,Just t)::xs), bindMap $= insert gr t} track
    _ => assert_total $ idris_crash "empty stack"

public export
popBranch : CaseTracker -> CaseTracker
popBranch track = case (track.bindStack, track.rewindBind) of
    ((gr,Nothing)::xs, _) => track
    ((gr,(Just _))::xs, oldBindings::obs) => { rewindBind := obs, bindStack := (gr,Nothing)::xs, bindMap := oldBindings } track
    _ => assert_total $ idris_crash "empty stack"

public export
popCase : CaseTracker -> CaseTracker
popCase track = case track.bindStack of
    (_::xs) => { bindStack := xs} track
    _ => assert_total $ idris_crash "empty stack"

public export
getTag : GlobalReg -> CaseTracker -> Tag
getTag gr track = fromMaybe All (lookup gr track.bindMap)

public export
getBranchReg : CaseTracker -> GlobalReg
getBranchReg track = case track.bindStack of
    ((x,_)::xs) => x
    _ => assert_total $ idris_crash "empty stack"

public export
trackCase : Name -> InstVisit CairoReg -> CaseTracker -> CaseTracker
trackCase n (VisitCase r) ct = pushCase (MkGlobalReg n r) ct
trackCase n (VisitConBranch t) ct = pushBranch (map Ctr t) ct
trackCase n (VisitConstBranch _) ct = pushBranch Nothing ct
trackCase n VisitBranchEnd ct = popBranch ct
trackCase n VisitCaseEnd ct = popCase ct
trackCase _ _ ct = ct

getStructure : SVar -> Environment -> Structure
getStructure v env = case (lookup v env.structures) of
    Nothing => Free
    (Just s) => s

resolveSVar : SVar -> Environment -> SVar
resolveSVar v env = case (lookup v env.structures) of
    Just (Unified target) => resolveSVar target env
    _ => v

-- save version of mapSVar (this should be used in unification)
bindSVar : SVar -> Structure -> Environment -> Environment
bindSVar sv s e = mapSVar (resolveSVar sv e) s e

newVar : Environment -> Structure -> (SVar, Environment)
newVar env initialS = let (nv,nEnv) = genSVar env in (nv,mapSVar nv initialS nEnv)

resolveReg : GlobalReg -> Environment -> Maybe SVar
resolveReg reg env = case lookup reg env.registers of
    Nothing => Nothing
    (Just v) => Just $ resolveSVar v env

-- short circuits mapping of GlobalReg
simplifyReg : Environment -> GlobalReg -> Environment
simplifyReg env r = case resolveReg r env of
    Nothing => env
    (Just sv) => mapReg r sv env

saveRegResolve : GlobalReg -> Environment -> (Maybe SVar, Environment)
saveRegResolve r env = let nEnv = simplifyReg env r in
    case resolveReg r nEnv of
        Nothing => case r of
            (MkGlobalReg _ (Const c)) => let (s,e) = newVar nEnv (Primitive (typeOfConst c)) in (Just s,e)
            (MkGlobalReg _ (Eliminated c)) => let (s,e) = newVar nEnv Escaped in (Just s,e)
            _ => (Nothing, nEnv)
        sv => (sv, nEnv)

resolveArgReg : GlobalReg -> Environment -> (SVar, Environment)
resolveArgReg gr env = case saveRegResolve gr env of
    (Nothing, _) => assert_total $ idris_crash "reg was not bound"
    (Just sv, nEnv) => (sv, nEnv)

-- short circuits mapping of SVar
-- it collapse forwarder chains to a single forwarder
simplifySVar : Environment -> SVar -> Environment
simplifySVar env s = case (lookup s env.structures) of
    Just (Unified target) => mapSVar s (Unified (resolveSVar target env)) env
    _ => env

-- gc helpers (mostly to prevent triggering the cse bug)
cleanRegs : Environment -> Environment
cleanRegs env = foldl simplifyReg env (keys env.registers)

cleanSVars : Environment -> Environment
cleanSVars env = foldl simplifySVar env (keys env.structures)

computeReachable : Environment -> SortedSet SVar
computeReachable env = foldl traceSVar empty (values env.registers)
 where traceSVar : SortedSet SVar -> SVar -> SortedSet SVar
       traceSVar svs sv = if contains sv svs then svs else case getStructure sv env of
            (Composite ctrs) => foldl (foldl traceSVar) (insert sv svs) (map values (values ctrs))
            (Unified target) => traceSVar (insert sv svs) target
            _ => insert sv svs

filterUnreachable : SortedSet SVar -> Environment ->Environment
filterUnreachable reachableSVar env = { structures $= keyFilter (\k => contains k reachableSVar) } env

computeAndFilterUnreachable : Environment ->Environment
computeAndFilterUnreachable env = filterUnreachable (computeReachable env) env

-- garbage collector removes unused stuff
-- Probably not needed but for larger programs it could be that this is needed to preserve memory
gc : Environment -> Environment
gc env = computeAndFilterUnreachable $ cleanRegs $ cleanSVars env

joinStructures : Structure -> Structure -> Structure
joinStructures (Unified _) _ = assert_total $ idris_crash "unifyStructure is only defined on resolved SVars"
joinStructures _ (Unified _) = assert_total $ idris_crash "unifyStructure is only defined on resolved SVars"
joinStructures Free Free = Free
joinStructures Free s2 = s2
joinStructures s1 Free = s1
joinStructures Escaped _ = Escaped
joinStructures _ Escaped = Escaped
joinStructures Error _ = Error
joinStructures _ Error = Error
joinStructures (Primitive c1) (Primitive c2) = if c1 == c2 then (Primitive c1) else Error
joinStructures FieldEscape FieldEscape = FieldEscape
joinStructures FieldEscape (Composite _) = FieldEscape
joinStructures (Composite _) FieldEscape = FieldEscape
joinStructures (Composite e1) (Composite e2) = Composite $ mergeWith mergeLeft e1 e2
joinStructures _ _ = Error

mutual
    unifyNestedWith : Structure -> Structure -> Environment -> Environment
    unifyNestedWith st (Composite ctrs) env = foldl (foldl unifySVarWith) env (map values (values ctrs))
        where unifySVarWith : Environment -> SVar -> Environment
              unifySVarWith e s = let (ks,e2) = newVar e st in unifySVar s ks e2
    unifyNestedWith _ _ env = env

    unifyFieldList : SortedMap Nat SVar -> SortedMap Nat SVar -> Environment -> Environment
    unifyFieldList fs1 fs2 env = foldl unifyPos env (nub (keys fs1 ++ keys fs2))
            where unifyPos : Environment -> Nat -> Environment
                  unifyPos e p = case (lookup p fs1, lookup p fs2) of
                    (Just sv1, Just sv2) => unifySVar sv1 sv2 e
                    _ => e

    unifyAll : Maybe (SortedMap Nat SVar) -> SortedMap Tag (SortedMap Nat SVar) -> Environment -> Environment
    unifyAll Nothing _ env = env
    unifyAll (Just all) other env = foldl unifyTag env (toList other)
        where unifyTag : Environment -> (Tag,SortedMap Nat SVar) -> Environment
              unifyTag e (All,_) = e
              unifyTag e (_,fs) = unifyFieldList all fs e

    unifyAllCtrs : SortedMap Tag (SortedMap Nat SVar) -> SortedMap Tag (SortedMap Nat SVar) -> Environment -> Environment
    unifyAllCtrs c1 c2 e = unifyAll (lookup All c1) c2 (unifyAll (lookup All c2) c1 e)

    unifyCtrs : SortedMap Tag (SortedMap Nat SVar) -> SortedMap Tag (SortedMap Nat SVar) -> Environment -> Environment
    unifyCtrs c1 c2 env = foldl unifyTag env (nub (keys c2 ++ keys c1))
            where unifyTag : Environment -> Tag -> Environment
                  unifyTag e t = case (lookup t c1, lookup t c2) of
                    (Just fs1, Just fs2) => unifyFieldList fs1 fs2 e
                    _ => e

    -- It is required that this is executed on resolvedSVars
    unifyStructure : Structure -> Structure -> Environment -> Environment
    unifyStructure Escaped s2 env = unifyNestedWith Escaped s2 env
    unifyStructure s1 Escaped env = unifyNestedWith Escaped s1 env
    unifyStructure Error s2 env = unifyNestedWith Error s2 env
    unifyStructure s1 Error env = unifyNestedWith Error s1 env
    unifyStructure FieldEscape FieldEscape env = env
    unifyStructure FieldEscape s2@(Composite _) env = unifyNestedWith Escaped s2 env
    unifyStructure s1@(Composite _) FieldEscape env = unifyNestedWith Escaped s1 env
    -- Todo: Uncomment when all fine
    unifyStructure (Composite e1) (Composite e2) env = unifyAllCtrs e1 e2 (unifyCtrs e1 e2 env)
    unifyStructure _ _ env = env

    unifySVar : SVar -> SVar -> Environment -> Environment
    unifySVar s1 s2 env = if s1 == s2 then env else
        let (rs1, rs2) = (resolveSVar s1 env, resolveSVar s2 env) in
        if rs1 == rs2 then env else
        let (st1, st2) = (getStructure rs1 env, getStructure rs2 env) in
        case (getStructure rs1 env, getStructure rs2 env) of
            -- Shortcut for Free & Escaped & Error (just optimisations)
            (Free, _) => mapSVar rs1 (Unified rs2) env
            (_, Free) => mapSVar rs2 (Unified rs1) env
            (Error, Error) => mapSVar rs2 (Unified rs1) env
            (Escaped, Escaped) => mapSVar rs1 (Unified rs2) env
            -- doing this first prevents endless loops (seems not to be enough)
            (st1, st2) => let (nsv, nEnv) = newVar env (joinStructures st1 st2) in
                let nEnv2 = mapSVar rs1 (Unified nsv) (mapSVar rs2 (Unified nsv) nEnv) in
                unifyStructure st1 st2 nEnv2
        where simplify : Environment -> Environment
              simplify e = simplifySVar (simplifySVar e s2) s1

unifyReg : GlobalReg -> GlobalReg ->  Environment -> Environment
-- Simplify is just a performance optimisation - may not even be necessary
unifyReg gr1 gr2 env = let (sv1, nEnv) = saveRegResolve gr1 env in
    let (sv2, nEnv2) = saveRegResolve gr2 nEnv in
    case (sv1,sv2) of
        (Just sv1, Nothing) => mapReg gr2 sv1 nEnv2
        (Nothing, Just sv2) => mapReg gr1 sv2 nEnv2
        (Just sv1, Just sv2) => unifySVar sv1 sv2 nEnv2
        (Nothing, Nothing) => let (nsv, nEnv3) = newVar nEnv2 Free in
            mapReg gr2 nsv (mapReg gr1 nsv nEnv3)

assignSVar : GlobalReg -> SVar -> Environment -> Environment
assignSVar gr sv env = let (rsv, nEnv) = saveRegResolve gr env in case rsv of
    Nothing => mapReg gr sv nEnv
    (Just sv2) => unifySVar sv sv2 nEnv

killReg : GlobalReg -> Environment -> Environment
-- we do not bind constant & eliminated regs
killReg (MkGlobalReg _ (Const c)) env = env
killReg (MkGlobalReg _ (Eliminated _)) env = env
killReg gr env = let (s,e) = newVar env Escaped in assignSVar gr s e

assignStruct : GlobalReg -> Structure -> Environment -> Environment
-- we do not bind constant & eliminated regs
assignStruct (MkGlobalReg _ (Const c)) s env = env
assignStruct (MkGlobalReg _ (Eliminated _)) s env = env
assignStruct gr s env = let (nsv, nEnv) = newVar env s in assignSVar gr nsv nEnv

unifyInstDef : Environment ->  (Name, CairoDef) -> Environment
-- Not sure if gc after each is necessary but better slow than out of memory
unifyInstDef env def@(name, fDef) = gc $ foldl trackAndUnify env (fromCairoDef def)
    where global : CairoReg -> GlobalReg
          global = MkGlobalReg name
          -- Todo: execution of the next two may be done multiple times (cse bug)
          returnRegs : List CairoReg
          returnRegs = case fDef of
               (FunDef _ _ rets _) => rets
               (ForeignDef _ _ _) => empty
               (ExtFunDef _ _ _ rets _) => rets
          returnImpls : SortedMap LinearImplicit CairoReg
          returnImpls = case fDef of
               (FunDef _ impls _ _) => impls
               (ForeignDef _ _ _) => empty
               (ExtFunDef _ _ impls _ _) => impls
          resolveToSMap : Environment -> List CairoReg -> (SortedMap Nat SVar, Environment)
          resolveToSMap env args = snd $ foldl (\(n,(m,e)),arg => let (sv,nEnv) = resolveArgReg (global arg) e in (S n, (insert n sv m, nEnv))) (Z, (empty, env)) args
          assignImpls : SortedMap LinearImplicit (CairoReg, CairoReg) -> Environment -> Environment
          assignImpls impls env = foldl (\e,(f,t) => unifyReg (global f) (global t) e) env (values impls)
          escapeImpls : SortedMap LinearImplicit (CairoReg, CairoReg) -> Environment -> Environment
          escapeImpls impls env = foldl (\e,(f,t) => killReg (global f) (killReg (global t) e)) env (values impls)
          unifyImpls : SortedMap LinearImplicit (CairoReg, CairoReg) -> SortedMap LinearImplicit GlobalReg -> SortedMap LinearImplicit GlobalReg -> Environment -> Environment
          unifyImpls callImpls inImpls outImpls env = foldr (\k => unifyImpl (lookup k callImpls) (lookup k inImpls) (lookup k outImpls)) env (keys callImpls)
            where unifyImpl : Maybe (CairoReg, CairoReg) -> Maybe GlobalReg -> Maybe GlobalReg -> Environment -> Environment
                  unifyImpl (Just (inC, outC)) (Just inF) (Just outF) env = unifyReg (global inC) inF (unifyReg (global outC) outF env)
                  unifyImpl (Just (_, outC)) Nothing (Just outF) env = unifyReg (global outC) outF env
                  unifyImpl (Just (inC, _)) (Just inF) Nothing env = unifyReg (global inC) inF env
                  unifyImpl _ _ _ env = env
          unifyInstVisit :  Environment -> InstVisit CairoReg -> Environment
          unifyInstVisit env (VisitAssign r arg) = unifyReg (global r) (global arg) env
          unifyInstVisit env (VisitMkCon r (Just t) args) = let (asvs,nenv) = resolveToSMap env args in assignStruct (global r) (Composite (singleton (Ctr t) asvs)) nenv
          unifyInstVisit env (VisitMkCon r Nothing args) = let (asvs,nenv) = resolveToSMap env args in assignStruct (global r) (Composite (singleton (Ctr 0) asvs)) nenv
          unifyInstVisit env (VisitMkClosure r name _ args) = let (asvs,nenv) = resolveToSMap env args in assignStruct (global r) (Composite (singleton (Clo name) asvs)) nenv
          unifyInstVisit env (VisitApply r impls f a) = escapeImpls impls (killReg (global r) (killReg (global a) (assignStruct (global f) FieldEscape env)))
          unifyInstVisit env (VisitMkConstant r c) = assignStruct (global r) (Primitive (typeOfConst c)) env
          unifyInstVisit env (VisitCall rs impls n args) = case lookup n env.defSigs of
            Nothing => assert_total $ idris_crash "defSigs are wrongly initialized"
            (Just (MkSigRegs params returns implIns implOuts)) => foldl (\e,(r,gr) => unifyReg (global r) gr e) (unifyImpls impls implIns implOuts env) ((zip rs returns) ++ (zip args params))
          unifyInstVisit env (VisitOp r impls t args) = assignImpls impls processedPrimFn
            where processedPrimFn : Environment
                  processedPrimFn = case t of
                        (Add ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (Sub ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (Mul ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (Div ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (Mod ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (Neg ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (ShiftL ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (ShiftR ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (BAnd ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (BOr ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (BXOr ty) => foldr (\reg => assignStruct (global reg) (Primitive ty)) env (r::args)
                        (LT ty) => assignStruct (global r) (Primitive IntType) (foldr (\reg => assignStruct (global reg) (Primitive ty)) env args)
                        (LTE ty) => assignStruct (global r) (Primitive IntType) (foldr (\reg => assignStruct (global reg) (Primitive ty)) env args)
                        (EQ ty) => assignStruct (global r) (Primitive IntType) (foldr (\reg => assignStruct (global reg) (Primitive ty)) env args)
                        (GTE ty) => assignStruct (global r) (Primitive IntType) (foldr (\reg => assignStruct (global reg) (Primitive ty)) env args)
                        (GT ty) => assignStruct (global r) (Primitive IntType) (foldr (\reg => assignStruct (global reg) (Primitive ty)) env args)
                        (Cast fty tty) => assignStruct (global r) (Primitive tty) (foldr (\reg => assignStruct (global reg) (Primitive fty)) env args)
                        BelieveMe => foldr (\reg => assignStruct (global reg) Free) env (r::args)
                        Crash => foldr (\reg => assignStruct (global reg) Free) env (r::args)
          unifyInstVisit env (VisitExtprim rs impls _ args) = escapeImpls impls (foldr killReg env (map global (rs ++ args)))
          unifyInstVisit env (VisitStarkNetIntrinsic r impls _ args) = escapeImpls impls (foldr killReg env (map global (r::args)))
          unifyInstVisit env (VisitConBranch (Just t)) = assignStruct (getBranchReg env.caseTracker) (Composite (singleton (Ctr t) empty)) env
          unifyInstVisit env (VisitConBranch Nothing) = assignStruct (getBranchReg env.caseTracker) (Composite (singleton All empty)) env
          unifyInstVisit env (VisitConstBranch (Just c)) = assignStruct (getBranchReg env.caseTracker) (Primitive (typeOfConst c)) env
          unifyInstVisit env (VisitConstBranch Nothing) = assignStruct (getBranchReg env.caseTracker) Free env
          unifyInstVisit env (VisitProject r arg pos) = let (rsv, nEnv) = resolveArgReg (global r) (assignStruct (global r) Free env) in
            assignStruct (global arg) (Composite (singleton (getTag (global arg) nEnv.caseTracker) (singleton pos rsv))) nEnv
          unifyInstVisit env (VisitReturn rs impls) = foldl (\e,(r1,r2) => unifyReg (global r1) (global r2) e) env ((zip rs returnRegs) ++ implPairs)
            where implPairs : List (CairoReg,CairoReg)
                  implPairs = map (\(l,r) => (r, fromMaybe r (lookup l impls))) (toList returnImpls)
          unifyInstVisit env (VisitNull r) = assignStruct (global r) Free env -- todo: document - null is undef and shall not be used
          unifyInstVisit env (VisitError r _ )= assignStruct (global r) Error env
          unifyInstVisit env _ =  env
          trackAndUnify : Environment -> InstVisit CairoReg -> Environment
          trackAndUnify env inst = unifyInstVisit ({ caseTracker $= trackCase name inst } env) inst

-- Collects all functions that are closure targets
allClosureTargets : List (Name, CairoDef) -> SortedSet Name
allClosureTargets defs = snd $ runVisitConcatCairoDefs (pureTraversal allClosureTargetsTraversal) defs
    where allClosureTargetsTraversal : InstVisit CairoReg -> SortedSet Name
          allClosureTargetsTraversal (VisitMkClosure _ name _ _) = singleton name
          allClosureTargetsTraversal _ = empty

-- Initiates the sigs and unifies all defs
--       ExtFun, ForeignFun & FunDef that are ClosureTargets -> Are initated as Escaped
--       FunDef that are not ClosureTargets -> Are initated as Escaped
dataFlowCapturing : List (Name, CairoDef) -> Environment
dataFlowCapturing defs = foldl unifyInstDef initialEnv defs
    where cloFuns : SortedSet Name
          cloFuns = allClosureTargets defs
          initSig : SignatureRegs -> Structure -> Environment -> Environment
          initSig (MkSigRegs ps rs implIn implOut) init env = foldl (\e, r => assignStruct r init e) env (ps ++ rs ++ (values implIn) ++ (values implOut))
          enterSig : Name -> SignatureRegs -> Structure -> Environment -> Environment
          enterSig name sig init env = initSig sig init (mapSig name sig env)
          makeOutImpls : SortedMap LinearImplicit GlobalReg  -> SortedMap LinearImplicit GlobalReg
          makeOutImpls = mapValueMap (mapCReg (prefixedReg "out"))
          makeSigRet : Name -> List CairoReg -> List CairoReg -> SortedMap LinearImplicit CairoReg -> SignatureRegs
          makeSigRet name params rets impls = let gimpls = (mapValueMap (MkGlobalReg name) impls) in MkSigRegs (map (MkGlobalReg name) params) (map (MkGlobalReg name) rets) gimpls (makeOutImpls gimpls)
          enterMapping : Environment -> (Name, CairoDef) -> Environment
          enterMapping env (name, FunDef params impls rets _) = enterSig name (makeSigRet name params rets impls) (if contains name cloFuns then Escaped else Free) env
          enterMapping env (name, ExtFunDef _ params impls rets _) = enterSig name (makeSigRet name params rets impls) Escaped env
          enterMapping env (name, ForeignDef info args rs) = enterSig name (makeSigRet name params rets impls) Escaped env
            where impls : SortedMap LinearImplicit CairoReg
                  impls = fromList $ map (\l => (l, implicitReg l)) info.implicits
                  enumerate : Nat -> List Int
                  enumerate (S n) = fromZeroTo (cast n)
                  enumerate Z = Nil
                  params : List CairoReg
                  params = map Param (enumerate args)
                  rets : List CairoReg
                  rets = map (\n => Unassigned Nothing n 0) (enumerate rs)
          fillMappings : Environment -> Environment
          fillMappings env = foldl enterMapping env defs
          initialEnv : Environment
          initialEnv = fillMappings (MkEnv 0 empty empty empty (MkCTrack Nil Nil empty))

public export
data SrcSnkDesc : Type where
    Make : Tag -> Nat -> SrcSnkDesc
    Apply : SrcSnkDesc
    Const : SrcSnkDesc
    Op : CairoPrimFn -> SrcSnkDesc
    ConBranch : Tag -> SrcSnkDesc
    ConstBranch : Maybe CairoConst -> SrcSnkDesc
    Project : Tag -> Nat -> SrcSnkDesc
    Null : SrcSnkDesc
    Fail : SrcSnkDesc

public export
record DataFlow where
    constructor MkDataFlow
    structure : Structure
    registers : SortedSet GlobalReg
    sources : List SrcSnkDesc
    sinks : List SrcSnkDesc

Show SrcSnkDesc where
    show (Make t n) = "{Make: "++(show t)++" "++(show n)++"}"
    show Const = "{Const}"
    show Apply = "{Apply}"
    show (Op fn) = "{OP: "++(show fn)++"}"
    show (ConBranch t) = "{ConBranch: "++(show t)++"}"
    show (ConstBranch t) = "{ConstBranch: "++(show t)++"}"
    show (Project t p) = "{Project: "++(show t)++" "++(show p)++"}"
    show Null = "{Null}"
    show Fail = "{Fail}"

Show DataFlow where
    show (MkDataFlow s r src snk) = "DataFlow(structure="++(show s)++", registers="++(show r)++", sources="++(show src)++", sinks="++(show snk)++")"

-- sources and sinks are initialized as empty
groupRegisters : Environment -> SortedMap SVar DataFlow
groupRegisters env = mapFilter (\(s,gr) => gr.structure /= Escaped && gr.structure /= Error ) refinedGroups
    where extendGroup : Maybe SVar -> GlobalReg -> SortedMap SVar (SortedSet GlobalReg) -> SortedMap SVar (SortedSet GlobalReg)
          extendGroup (Just sv) gr grs = case lookup sv grs of
            Nothing => insert sv (singleton gr) grs
            (Just regs) => insert sv (insert gr regs) grs
          extendGroup Nothing _ _ = assert_total $ idris_crash "Should not be possible"
          rawGroups : SortedMap SVar (SortedSet GlobalReg)
          rawGroups = foldl (\s,r => extendGroup (resolveReg r env) r s) empty (keys env.registers)
          refinedGroups : SortedMap SVar DataFlow
          refinedGroups = mapMap (\(s,rs) => (s, MkDataFlow (getStructure s env) rs [] [])) rawGroups

addSink : Environment -> Name -> CairoReg -> SrcSnkDesc -> SortedMap SVar DataFlow -> SortedMap SVar DataFlow
addSink env fn reg ssd flows = case resolveReg (MkGlobalReg fn reg) env of
    Nothing => flows
    (Just sv) => case lookup sv flows of
        Nothing => flows
        (Just df) => insert sv ({ sinks $= (ssd::)} df) flows

addSource : Environment -> Name -> CairoReg -> SrcSnkDesc -> SortedMap SVar DataFlow -> SortedMap SVar DataFlow
addSource env fn reg ssd flows = case resolveReg (MkGlobalReg fn reg) env of
    Nothing => flows
    (Just sv) => case lookup sv flows of
        Nothing => flows
        (Just df) => insert sv ({ sources $= (ssd::)} df) flows

record SrcSnkResolveState where
     constructor MkSSRState
     flows : SortedMap SVar DataFlow
     caseTracker : CaseTracker


updateResCaseTracker : (CaseTracker -> CaseTracker) -> SrcSnkResolveState -> SrcSnkResolveState
updateResCaseTracker f = { caseTracker $= f }

-- todo: shall we add calls to foreign + extprim + appla arg/res as sink/source? (is usually only on escaped ones)
collectInstVisitDef : (Name, CairoDef) -> Environment -> SrcSnkResolveState -> SrcSnkResolveState
collectInstVisitDef def@(name, _) env res = foldl trackAndVisit res (fromCairoDef def)
    where addSrc : CairoReg -> SrcSnkDesc -> SrcSnkResolveState -> SrcSnkResolveState
          addSrc reg ssd = { flows $= addSource env name reg ssd}
          addSnk : CairoReg -> SrcSnkDesc -> SrcSnkResolveState -> SrcSnkResolveState
          addSnk reg ssd = { flows $= addSink env name reg ssd}
          visitInsts : SrcSnkResolveState -> InstVisit CairoReg -> SrcSnkResolveState
          visitInsts res inst@(VisitMkCon r (Just t) args) = addSrc r (Make (Ctr t) (length args)) res
          visitInsts res inst@(VisitMkCon r Nothing args) = addSrc r (Make (Ctr 0) (length args)) res
          visitInsts res inst@(VisitApply r _ f a) = addSnk f Apply res
          visitInsts res inst@(VisitMkClosure r name _ args) = addSrc r (Make (Clo name) (length args)) res
          visitInsts res inst@(VisitMkConstant r _) = addSrc r Const res
          visitInsts res inst@(VisitOp r _ pfn args) = addSrc r (Op pfn) (foldl (\f,r => addSnk r (Op pfn) f) res args)
          visitInsts res (VisitConBranch (Just t)) = addSnk ((getBranchReg res.caseTracker).register) (ConBranch (Ctr t)) res
          visitInsts res (VisitConBranch Nothing) = addSnk ((getBranchReg res.caseTracker).register) (ConBranch All) res
          visitInsts res (VisitConstBranch c) = addSnk ((getBranchReg res.caseTracker).register) (ConstBranch c) res
          visitInsts res inst@(VisitProject _ v p) = addSnk v (Project (getTag (MkGlobalReg name v) res.caseTracker) p) res
          visitInsts res inst@(VisitNull r) = addSrc r Null res
          visitInsts res inst@(VisitError r _) = addSrc r Fail res
          -- Inst that do an escape anyways are not even listed (no need to)
          visitInsts res _ = res
          trackAndVisit : SrcSnkResolveState -> InstVisit CairoReg -> SrcSnkResolveState
          trackAndVisit res inst = visitInsts ({ caseTracker $= trackCase name inst } res) inst

collectInstVisitDefs : List (Name, CairoDef) -> Environment -> SrcSnkResolveState -> SrcSnkResolveState
collectInstVisitDefs defs env flows = foldl (\f,def => collectInstVisitDef def env f) flows defs

analyseDataFlow : List (Name, CairoDef) -> Environment -> List DataFlow
analyseDataFlow defs dataFlow = values $ flows $ collectInstVisitDefs defs dataFlow (MkSSRState (groupRegisters dataFlow) (MkCTrack Nil Nil empty))

export
dataFlowAnalysis : List (Name, CairoDef) -> List DataFlow
dataFlowAnalysis defs = analyseDataFlow defs (dataFlowCapturing defs)
