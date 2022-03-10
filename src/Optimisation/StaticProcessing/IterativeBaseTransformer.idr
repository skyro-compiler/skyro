module Optimisation.StaticProcessing.IterativeBaseTransformer

import Data.List
import Data.SortedSet
import Data.SortedMap
import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Optimisation.StaticProcessing.StaticTransformer
import Optimisation.StaticProcessing.StaticTracker
import Optimisation.OrderAndEliminateDefinitions
import CairoCode.Traversal.Base
import Utils.Helpers
import CommonDef
import Utils.Lens

import Debug.Trace

%hide Prelude.toList

record GlobalTransformerState where
    constructor MkGlobalTransformerState
    -- Global Context
    allDefs : SortedMap Name CairoDef
    retBind : SortedMap Name (List StaticInfo)
    -- Per iter Context
    regGen : RegisterGen
    return : Maybe (List StaticInfo)
    hot : Bool

regGenLens : Lens GlobalTransformerState RegisterGen
regGenLens = MkLens regGen (\ts,fn => {regGen $= fn} ts)

returnLens : Lens GlobalTransformerState (Maybe (List StaticInfo))
returnLens = MkLens return (\ts,fn => {return $= fn} ts)

recordRet : List StaticInfo -> GlobalTransformerState -> GlobalTransformerState
recordRet ret (MkGlobalTransformerState allDefs retBind regGen (Just oldRet) hot) = MkGlobalTransformerState allDefs retBind regGen (Just (zipWith mergeStaticInfo ret oldRet)) hot
recordRet ret (MkGlobalTransformerState allDefs retBind regGen Nothing hot) = MkGlobalTransformerState allDefs retBind regGen (Just ret) hot

markHot : GlobalTransformerState -> GlobalTransformerState
markHot (MkGlobalTransformerState allDefs retBind regGen ret hot) = MkGlobalTransformerState allDefs retBind regGen ret True

integrateRet : Name -> List StaticInfo -> GlobalTransformerState -> GlobalTransformerState
integrateRet name ret (MkGlobalTransformerState allDefs retBind regGen rets hot) = MkGlobalTransformerState allDefs (insert name ret retBind) regGen rets hot

integrateDef : (Name, CairoDef) -> GlobalTransformerState -> GlobalTransformerState
integrateDef (name, def) (MkGlobalTransformerState allDefs retBind regGen rets hot) = MkGlobalTransformerState (insert name def allDefs) retBind regGen rets hot

resetState : GlobalTransformerState -> GlobalTransformerState
resetState (MkGlobalTransformerState allDefs retBind regGen _ _) = MkGlobalTransformerState allDefs retBind regGen Nothing False

finishDef : (Name, CairoDef) -> GlobalTransformerState -> GlobalTransformerState
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

mutual
    substituteStaticValue : SortedMap CairoReg StaticInfo -> StaticValue -> StaticInfo
    substituteStaticValue argSubs (Constructed ctrs) = MKStaticInfo empty (Constructed (mapValueMap (map (substituteStaticInfo argSubs)) ctrs))
    substituteStaticValue argSubs (Closure name args) = MKStaticInfo empty (Closure name (map (substituteStaticInfo argSubs) args))
    substituteStaticValue argSubs (Field src Nothing no) = MKStaticInfo empty (Field (substituteStaticInfo argSubs src) Nothing no)
    substituteStaticValue argSubs (Field src (Just tag) no) = simplify $ substituteStaticInfo argSubs src
        where tryExtractField : Nat -> List StaticInfo -> StaticInfo
              tryExtractField _ Nil = MKStaticInfo empty (Field src (Just tag) no)
              tryExtractField Z (x::_) = substituteStaticInfo argSubs x
              tryExtractField (S n) (_::xs) = tryExtractField n xs
              simplify : StaticInfo -> StaticInfo
              simplify inner@(MKStaticInfo _ (Constructed ctrs)) = case (lookup tag ctrs) of
                Nothing => MKStaticInfo empty (Field src (Just tag) no)
                (Just ctr) => tryExtractField no ctr
              simplify inner = MKStaticInfo empty (Field src (Just tag) no)
    substituteStaticValue _ val = MKStaticInfo empty val

    substituteStaticInfo : SortedMap CairoReg StaticInfo -> StaticInfo -> StaticInfo
    substituteStaticInfo args (MKStaticInfo src val) = case usedParamRegs of
        Nil => substituteStaticValue args val
        reg::_ => fromMaybe (MKStaticInfo empty Unknown) (lookup reg args)
        where usedParamRegs : List CairoReg
              usedParamRegs = toList $ intersection src (fromList $ keys args)

substituteStaticInfos : (args: List (CairoReg, StaticInfo)) -> (rets: List (CairoReg, StaticInfo)) -> List StaticInfo
substituteStaticInfos args rets = map (\(reg,ret) => addBinding (substituteStaticInfo (fromList args) ret) reg) rets

bindArgs : Maybe CairoDef -> List StaticInfo ->  List (CairoReg, StaticInfo)
bindArgs (Just (FunDef params _ _ _)) vals = zip params vals
bindArgs (Just (ForeignDef _ args _)) vals = zip (map Param (fromZeroTo ((cast args)-1))) vals -- just gen the default ones
bindArgs _ _ = trace "Def to bind args not available" []

public export
record FunData where
    constructor MKFunData
    function: Name
    target: CairoDef
    -- StaticInfo is input (stores a reg internally) & CairoReg is output
    implicitsIn: SortedMap LinearImplicit StaticInfo
    -- StaticInfo is static result & CairoReg is target reg to store it in
    implicitsOut: SortedMap LinearImplicit (CairoReg, StaticInfo)
    -- StaticInfo is input (stores a reg internally)
    arguments : List StaticInfo
    -- StaticInfo is static result & CairoReg is target reg to store it in
    returns: List (CairoReg, StaticInfo)

export
genFunCall : FunData -> List (InstVisit CairoReg)
genFunCall (MKFunData name _ implIn implsOut args rs) = [VisitCall (map fst rs) (resolveLinearImplicits reconstructedImpls) name (map resolveInfToReg args)]
    where  reconstructedImpls : SortedMap LinearImplicit (StaticInfo, CairoReg)
           reconstructedImpls = fromList $ map (\(k,v) => (k, (v, fromMaybe Eliminated (maybeMap fst (lookup k implsOut))))) (toList implIn)

iterativeProcessing : (RegisterGen -> Name -> FunData -> (RegisterGen, Maybe (List (InstVisit CairoReg)))) -> ((Name, CairoDef) -> (Name, CairoDef)) -> List Name -> GlobalTransformerState -> GlobalTransformerState
iterativeProcessing funTransformer cleanUp Nil state = state
iterativeProcessing funTransformer cleanUp (name::xs) state = case lookup name state.allDefs of
        Nothing => iterativeProcessing funTransformer cleanUp (trace ("Function "++(show name)++" is missing") xs) state
        (Just def) => case processFunction (name,def) state of
            (True, state) => iterativeProcessing funTransformer cleanUp (name::xs) state
            (False, state) => iterativeProcessing funTransformer cleanUp xs state
    where processFunction : (Name, CairoDef) -> GlobalTransformerState -> (Bool, GlobalTransformerState)
          processFunction curDef@(curName, (ForeignDef _ _ rets)) state = (False, finishDef curDef (recordRet (replicate rets (MKStaticInfo empty  Unknown)) state))
          -- todo: Shall we have a track only version now that we have cleanup??
          processFunction curDef state = finish $ globalStaticOptimizeDef @{handler} state.allDefs state curDef
            where finish : ((Name, CairoDef), GlobalTransformerState) -> (Bool, GlobalTransformerState)
                  finish (def, nState) = (nState.hot, finishDef (cleanUp def) nState)
                  trackRet : Name -> List StaticInfo -> List CairoReg -> GlobalTransformerState -> List StaticInfo
                  trackRet name args rs state = produceRet $ lookup name state.retBind
                    where produceRet : Maybe (List StaticInfo) ->  List StaticInfo
                          produceRet (Just statRet) = substituteStaticInfos (bindArgs (lookup name state.allDefs) args) (zip rs statRet)
                          produceRet Nothing = map (\r => MKStaticInfo (singleton r) Unknown) rs
                  [handler] CallHandler GlobalTransformerState where
                    return rets _ = updateState (recordRet rets)
                    track (MKCallData name impls args rs) = map (\state => (trackRet name args rs state, staticImplTracker impls)) readState
                    transform (MKCallData name impls args rs) = readState >>= (\state => writeStateBack $ withState state)
                        where writeStateBack : (GlobalTransformerState, List (InstVisit CairoReg)) -> Traversal GlobalTransformerState (List (InstVisit CairoReg))
                              writeStateBack (state, res) = map (\_ => res) (writeState state)
                              withState : GlobalTransformerState -> (GlobalTransformerState, List (InstVisit CairoReg))
                              withState state = processRet $ funTransformer state.regGen (fst curDef) funData
                                where nImpls : SortedMap LinearImplicit StaticInfo
                                      nImpls = staticImplTracker impls
                                      rets : List (CairoReg, StaticInfo)
                                      rets = zip rs (trackRet name args rs state)
                                      buildLinOut: LinearImplicit -> (LinearImplicit, (CairoReg, StaticInfo))
                                      buildLinOut k = (k, (fromMaybe Eliminated (maybeMap snd (lookup k impls)), fromMaybe (MKStaticInfo empty Unknown) (lookup k nImpls)))
                                      implOut : SortedMap LinearImplicit (CairoReg, StaticInfo)
                                      implOut = fromList $ map buildLinOut (keys impls)
                                      def : CairoDef
                                      def = fromMaybe (assert_total $ idris_crash "Unknown function is called") (lookup name state.allDefs)
                                      funData : FunData
                                      funData = (MKFunData name def (mapValueMap fst impls) implOut args rets)
                                      processRet : (RegisterGen, Maybe (List (InstVisit CairoReg))) -> (GlobalTransformerState, List (InstVisit CairoReg))
                                      processRet (regGen, Nothing) = (regGenLens.set state regGen, genFunCall funData)
                                      processRet (regGen, Just res) = (markHot $ regGenLens.set state regGen, res)

export
iterativeCallTransform : RegisterGen -> (RegisterGen -> Name -> FunData -> (RegisterGen, Maybe (List (InstVisit CairoReg)))) -> ((Name, CairoDef)  -> (Name, CairoDef))  -> Name -> List (Name, CairoDef) -> List (Name, CairoDef)
iterativeCallTransform regGen transformer cleaner entryPoint defs = reconstruct $ iterativeProcessing transformer cleaner orderedNames (MkGlobalTransformerState defLookup empty regGen Nothing False)
    where defLookup : SortedMap Name CairoDef
          defLookup = fromList defs
          orderedNames : List Name
          orderedNames = map fst (orderUsedDefs entryPoint defs)
          reconstruct : GlobalTransformerState -> List (Name, CairoDef)
          reconstruct (MkGlobalTransformerState newDefs _ _ _ _ ) = orderUsedDefs entryPoint (toList newDefs)

export
noTransform : RegisterGen -> Name -> FunData -> (RegisterGen, Maybe (List (InstVisit CairoReg)))
noTransform regGen _ funData = (regGen, Nothing)
