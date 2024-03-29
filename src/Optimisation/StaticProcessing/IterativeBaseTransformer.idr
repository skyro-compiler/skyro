module Optimisation.StaticProcessing.IterativeBaseTransformer

import Data.List
import Data.Maybe
import Data.SortedSet
import Data.SortedMap
-- import Core.Context
import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.OrderAndEliminateDefinitions
import CairoCode.Traversal.Base
import Utils.Helpers
import CommonDef
import Utils.Lens

import CairoCode.Checker
import Debug.Trace

%hide Prelude.toList

record GlobalTransformerState a where
    constructor MkGlobalTransformerState
    -- Global Context
    allDefs : SortedMap CairoName CairoDef
    retBind : SortedMap CairoName (List StaticInfo)
    userState : a
    -- Per iter Context
    return : Maybe (List StaticInfo)
    fresh : List CairoName
    hot : Bool

userStateLens : Lens (GlobalTransformerState a) a
userStateLens = MkLens userState (\ts,fn => {userState $= fn} ts)

returnLens : Lens (GlobalTransformerState a) (Maybe (List StaticInfo))
returnLens = MkLens return (\ts,fn => {return $= fn} ts)

recordRet : List StaticInfo -> GlobalTransformerState a -> GlobalTransformerState a
recordRet ret state = case state.return of
    (Just oldRet) => if (length ret == length oldRet)
     -- todo: try to add a fallback
     then {return := Just (zipWith (mergeStaticInfo Nothing) ret oldRet)} state
     else trace ("SHOULD NOT HAPPEN") ({return := Just (zipWith (mergeStaticInfo Nothing) ret oldRet)} state)
    Nothing => {return := Just ret} state

markHot : GlobalTransformerState a -> GlobalTransformerState a
markHot = {hot := True}

addFresh : List (CairoName, CairoDef) -> GlobalTransformerState a -> GlobalTransformerState a
addFresh defs = {fresh $= ((map fst defs)++), allDefs $= mergeWith (\_,_ => assert_total $ idris_crash "Function already exists") (fromList defs)}

pullFresh : GlobalTransformerState a -> (GlobalTransformerState a, List CairoName)
pullFresh state = ({fresh := Nil} state, state.fresh)

integrateRet : CairoName -> List StaticInfo -> GlobalTransformerState a -> GlobalTransformerState a
integrateRet name ret = {retBind $= insert name ret}

integrateDef : (CairoName, CairoDef) -> GlobalTransformerState a -> GlobalTransformerState a
integrateDef (name, def) = {allDefs $= insert name def}

resetState : GlobalTransformerState a -> GlobalTransformerState a
resetState = {return := Nothing, hot := False}

finishDef : (CairoName, CairoDef) -> GlobalTransformerState a -> GlobalTransformerState a
finishDef def state = resetState $ integrateDef def (integrateRet (fst def) (fromMaybe (assert_total $ idris_crash "Missing return to record") state.return) state)

-- todo: not necessary but would lead to a cleaner ret map : REENABLE THIS --
{-
mutual
    cleanStaticValue : SortedSet CairoReg  -> StaticValue -> StaticValue
    cleanStaticValue argKeep (Constructed ctrs) = Constructed (mapValueMap (map (cleanStaticInfo argKeep)) ctrs)
    cleanStaticValue argKeep (Closure name args) = Closure name (map (cleanStaticInfo argKeep) args)
    cleanStaticValue argKeep (Field src tag no) = Field (cleanStaticInfo argKeep) tag no
    cleanStaticValue _ val = val

    cleanStaticInfo : SortedSet CairoReg -> StaticInfo -> StaticInfo
    cleanStaticInfo args (MKStaticInfo src val) = MKStaticInfo (intersection src args) (cleanStaticValue val)


cleanStaticInfos : (args: List CairoReg) -> (rets: List StaticInfo) -> List StaticInfo
cleanStaticInfos args rets = map (cleanStaticInfo (fromList args)) rets
-}

emptyInfo : StaticValue -> StaticInfo
emptyInfo = MKStaticInfo empty
mutual
    substituteStaticValue : SortedMap CairoReg StaticInfo -> StaticValue -> StaticInfo
    substituteStaticValue argSubs (Constructed ctrs) = emptyInfo (Constructed (mapValueMap (map (substituteStaticInfo argSubs)) ctrs))
    substituteStaticValue argSubs (Closure name args) = emptyInfo (Closure name (map (substituteStaticInfo argSubs) args))
    -- Todo: when is it nothing here? and can we do closure stuff?
    substituteStaticValue argSubs (Field src Nothing no) = emptyInfo (Field (substituteStaticInfo argSubs src) Nothing no)
    substituteStaticValue argSubs (Field src (Just tag) no) = simplify (substituteStaticInfo argSubs src)
        where tryExtractField : StaticInfo -> Nat -> List StaticInfo -> StaticInfo
              tryExtractField inner _ Nil = emptyInfo (Field inner (Just tag) no)
              tryExtractField inner Z (x::_) = substituteStaticInfo argSubs x
              tryExtractField inner (S n) (_::xs) = tryExtractField inner n xs
              simplify : StaticInfo -> StaticInfo
              simplify inner@(MKStaticInfo _ (Constructed ctrs)) = case (lookup tag ctrs) of
                Nothing => emptyInfo (Field inner (Just tag) no)
                (Just ctr) => tryExtractField inner no ctr
              simplify inner = emptyInfo (Field inner (Just tag) no)
    substituteStaticValue _ val = emptyInfo val

    substituteStaticInfo : SortedMap CairoReg StaticInfo -> StaticInfo -> StaticInfo
    substituteStaticInfo args (MKStaticInfo src val) = case usedParamRegs of
        Nil => substituteStaticValue args val
        reg::_ => fromMaybe (assert_total $ idris_crash "Can not happen") (lookup reg args)
        where usedParamRegs : List CairoReg
              usedParamRegs = toList $ intersection src (fromList $ keys args)

substituteStaticInfos : (args: List (CairoReg, StaticInfo)) -> (rets: List (CairoReg, StaticInfo)) -> List StaticInfo
substituteStaticInfos args rets = map (\(reg,ret) => addBinding (substituteStaticInfo (fromList args) ret) reg) rets

bindArgs : Maybe CairoDef -> List StaticInfo ->  List (CairoReg, StaticInfo)
bindArgs (Just (FunDef params _ _ _)) vals = zip params vals
bindArgs (Just (ExtFunDef _ params _ _ _)) vals = assert_total $ idris_crash "External Functions can not be called internally" -- zip params vals
-- todo: we need to add regs to ForeignDef more stable less risky
-- Todo: Maybe this is why global inference fails (some bug here)
bindArgs (Just (ForeignDef _ args _)) vals = zip (map Param (fromZeroTo ((cast args)-1))) vals -- just gen the default ones
bindArgs _ _ = trace "Def to bind args not available" []

public export
record FunData where
    constructor MKFunData
    function: CairoName
    target: CairoDef
    -- StaticInfo is input (stores a reg internally) & CairoReg is output
    implicitsIn: SortedMap LinearImplicit StaticInfo
    -- StaticInfo is static result & CairoReg is target reg to store it in
    implicitsOut: SortedMap LinearImplicit (CairoReg, StaticInfo)
    -- StaticInfo is input (stores a reg internally)
    arguments : List StaticInfo
    -- StaticInfo is static result & CairoReg is target reg to store it in
    returns: List (CairoReg, StaticInfo)

public export
record CloData where
    constructor MKCloData
    function: CairoName
    target: CairoDef
    -- StaticInfo is input (stores a reg internally)
    arguments : List StaticInfo
    miss : Nat
    -- StaticInfo is static result & CairoReg is target reg to store it in
    returns: CairoReg

export
genFunCall : FunData -> List (InstVisit CairoReg)
genFunCall (MKFunData name _ implIn implsOut args rs) = [VisitCall (map fst rs) (resolveLinearImplicits reconstructedImpls) name (map resolveInfToReg args)]
    where  reconstructedImpls : SortedMap LinearImplicit (StaticInfo, CairoReg)
           reconstructedImpls = fromList $ map (\(k,v) => (k, (v, fromMaybe (debugElimination "IBT_genFunCallling") (maybeMap fst (lookup k implsOut))))) (toList implIn)

export
genMkClo : CloData -> List (InstVisit CairoReg)
genMkClo (MKCloData name _ args miss r) = [VisitMkClosure r name  miss (map resolveInfToReg args)]

-- Todo:
-- 1. Add a way to generate functions when transforming
-- 2. Add a way to have extra info per function:
--    Make interface where def & name are generic, then replace (CairoName,CairoDef) -> Interface a => a

public export
TransformerResult : Type
TransformerResult = (Maybe (List (InstVisit CairoReg)), List (CairoName, CairoDef))
-- Todo: can we move RegGen into UserState?
-- Todo: add Fresh defs (can we replace hot and just return self?)
public export
interface IterativeTransformerConf a where
    funTransformer : a -> SortedMap CairoName CairoDef -> (depth: Int) -> CairoName -> FunData -> (a,  TransformerResult)
    cloTransformer : a -> SortedMap CairoName CairoDef -> (depth: Int) -> CairoName -> CloData -> (a,  TransformerResult)
    ctxBinder : a -> (CairoName, CairoDef) -> (List CairoReg, SortedMap LinearImplicit CairoReg) -> (List StaticInfo, SortedMap LinearImplicit StaticInfo)
    cleanUp : a -> SortedMap CairoName CairoDef -> (CairoName, CairoDef) -> (a, (CairoName, CairoDef))
    -- defaults --
    funTransformer uState _ _ _ funData = (uState, (Nothing, Nil))
    cloTransformer uState _ _ _ cloData = (uState, (Nothing, Nil))
    ctxBinder _ _ (params, impls) = (map paramInit params, mapValueMap paramInit impls)
        where paramInit : CairoReg -> StaticInfo
              paramInit reg = MKStaticInfo (singleton reg) Unknown
    cleanUp uState _ def = (uState, def)

-- reused helpers
writeStateBack : (GlobalTransformerState a, b) -> Traversal (GlobalTransformerState a) b
writeStateBack (state, res) = map (\_ => res) (writeState state)

overState : (GlobalTransformerState a -> (GlobalTransformerState a, b)) -> Traversal (GlobalTransformerState a) b
overState fn = readState >>= (\state => writeStateBack $ fn state)

iterativeProcessing : (ita: IterativeTransformerConf a) => List CairoName -> GlobalTransformerState a -> GlobalTransformerState a
iterativeProcessing Nil state = state
iterativeProcessing (name::xs) origState = case lookup name origState.allDefs of
        Nothing => iterativeProcessing (trace ("Function "++(show name)++" is missing") xs) origState
        (Just def) => case processFunction (name,def) origState of
            (True, state) => if integrityCheck (toList state.allDefs) name
                then let (nState,fresh) = pullFresh state in iterativeProcessing (fresh ++ (name::xs)) nState
                else assert_total $ idris_crash "Before: \{show (name, lookup name origState.allDefs)} \n After: \{show (name, lookup name state.allDefs)} \n All: \{show $ toList origState.allDefs}"
            (False, state) => let (nState,fresh) = pullFresh state in iterativeProcessing (fresh ++ xs) nState
    where processFunction : (CairoName, CairoDef) -> GlobalTransformerState a -> (Bool, GlobalTransformerState a)
          -- Abstract and Foreign Functions do not have a body
          processFunction curDef@(curName, (ForeignDef _ _ rets)) state = (False, finishDef curDef (recordRet (replicate rets (defaultInfo "IBT_Foreign_Ret" Unknown)) state))
          processFunction curDef@(curName, (ExtFunDef _ _ _ rets [])) state = (False, finishDef curDef (recordRet (replicate (length rets) (defaultInfo "IBT_Abstract_Ret" Unknown)) state))
          -- todo: Shall we have a track only version now that we have cleanup??
          processFunction curDef state = finish $ globalStaticOptimizeDef @{handler} state.allDefs state curDef
            where finish : ((CairoName, CairoDef), GlobalTransformerState a) -> (Bool, GlobalTransformerState a)
                  finish (def, nState) = let (nuState, nDef) = cleanUp @{ita} nState.userState nState.allDefs def in (nState.hot, finishDef nDef ({userState := nuState} nState))
                  -- Todo: There was a bug once and thus the ret tracking was disabled
                  --       However, I think I fixed it but are not 100% sure (as the failing test changed and more optims arrived)
                  --       If we have manifest problems again try disabling this this
                  --        also try reenable and fixing the cleanup
                  trackRet : CairoName -> List StaticInfo -> List CairoReg -> GlobalTransformerState a -> List StaticInfo
                  -- trackRet name args rs state = map (\r => MKStaticInfo (singleton r) Unknown) rs
                  trackRet name args rs state = produceRet $ lookup name state.retBind
                     where produceRet : Maybe (List StaticInfo) -> List StaticInfo
                           produceRet (Just statRet) = substituteStaticInfos (bindArgs (lookup name state.allDefs) args) (zip rs statRet)
                           produceRet Nothing = map (\r => MKStaticInfo (singleton r) Unknown) rs
                  [handler] CallHandler (GlobalTransformerState a) where
                    return rets _ = updateState (recordRet rets)
                    context regs = do
                        uState <- readStateL userStateLens
                        pure $ ctxBinder @{ita} uState curDef regs
                    track (MKCallData name _ impls args rs) = map (\state => (trackRet name args rs state, staticImplTracker impls)) readState
                    transformClosure (MKCreateCloData name depth args miss r) = overState withState
                        where withState : GlobalTransformerState a -> (GlobalTransformerState a, List (InstVisit CairoReg))
                              withState state = let cloData = (MKCloData name def args miss r) in
                                    processRes cloData (cloTransformer @{ita} state.userState  state.allDefs depth (fst curDef) cloData)
                                where def : CairoDef
                                      def = fromMaybe (assert_total $ idris_crash "Unknown function is called: \{show name}") (lookup name state.allDefs)
                                      processRes : CloData -> (a, TransformerResult) -> (GlobalTransformerState a, List (InstVisit CairoReg))
                                      processRes cloData (uState, (Nothing, fresh)) = (addFresh fresh (userStateLens.set state uState), genMkClo cloData)
                                      processRes _ (uState, (Just res, fresh)) = (addFresh fresh (markHot (userStateLens.set state uState)), res)
                    transformCall (MKCallData name depth impls args rs) = overState withState
                        where withState : GlobalTransformerState a -> (GlobalTransformerState a, List (InstVisit CairoReg))
                              withState state = let funData = (MKFunData name def (mapValueMap fst impls) implOut args rets) in
                                    processRes funData ( funTransformer @{ita} state.userState state.allDefs depth (fst curDef) funData)
                                where rets : List (CairoReg, StaticInfo)
                                      rets = zip rs (trackRet name args rs state)
                                      buildLinOut: SortedMap LinearImplicit StaticInfo -> LinearImplicit -> (LinearImplicit, (CairoReg, StaticInfo))
                                      buildLinOut nImpls k = (k, (fromMaybe (debugElimination "IBT_buildLinOut") (maybeMap snd (lookup k impls)), fromMaybe (defaultInfo "IBT_buildLinOut2" Unknown) (lookup k nImpls)))
                                      implOut : SortedMap LinearImplicit (CairoReg, StaticInfo)
                                      implOut = let nImpls = staticImplTracker impls in fromList $ map (buildLinOut nImpls) (keys impls)
                                      def : CairoDef
                                      def = fromMaybe (assert_total $ idris_crash "Unknown function is called: \{show name}") (lookup name state.allDefs)
                                      processRes : FunData -> (a, TransformerResult) -> (GlobalTransformerState a, List (InstVisit CairoReg))
                                      processRes funData (uState, (Nothing, fresh)) = (addFresh fresh (userStateLens.set state uState), genFunCall funData)
                                      processRes _ (uState, (Just res, fresh)) = (addFresh fresh (markHot (userStateLens.set state uState)), res)


export
rawIterativeCallTransform : IterativeTransformerConf a => a -> List (CairoName, CairoDef) -> (a, List (CairoName, CairoDef))
rawIterativeCallTransform uState defs = reconstruct $ iterativeProcessing orderedNames (MkGlobalTransformerState defLookup empty uState Nothing Nil False)
    where defLookup : SortedMap CairoName CairoDef
          defLookup = fromList defs
          orderedNames : List CairoName
          orderedNames = map fst (orderUsedDefs defs)
          reconstruct : GlobalTransformerState a -> (a, List (CairoName, CairoDef))
          reconstruct state = (state.userState, toList state.allDefs)

export
iterativeCallTransform : IterativeTransformerConf a => a -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
iterativeCallTransform uState defs = snd $ rawIterativeCallTransform uState defs
