module Optimisation.StaticProcessing.StaticTracker

import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils

import Data.List
import Data.SortedSet
import Data.SortedMap
import Primitives.Primitives
import Primitives.Externals
import Primitives.Common
import CairoCode.Traversal.Base
import CairoCode.Traversal.ValueTracker
import CairoCode.Traversal.Composition
import Utils.Helpers
import Utils.Lens
import Debug.Trace

%hide Prelude.toList

-- Internal enriched definitions

mutual
    public export
    data StaticValue : Type where
        Unknown : StaticValue
        Error : String -> StaticValue
        -- values are all possible values
        Const : (values: SortedSet CairoConst) -> StaticValue
        -- ctrs are all possible constructors
        Constructed : (ctrs: SortedMap Int (List StaticInfo)) -> StaticValue
        Closure : (name: Maybe (Name, Nat)) -> (arguments: List StaticInfo) -> StaticValue
        -- Allows repacking of Unknown Projections
        Field : (source: StaticInfo) -> (tag: Maybe Int) -> (fieldIndex: Nat) -> StaticValue

    public export
    record StaticInfo where
        constructor MKStaticInfo
        sources: SortedSet CairoReg
        value: StaticValue

    -- for debugging
    export
    Show StaticValue where
        show Unknown = "Unknown"
        show (Error e) = "Error: "++ (show e)
        show (Const cs) = "Constant: "++ (show cs)
        show (Constructed ctrs) = assert_total ("Constructed: "++ (show ctrs))
        show (Closure name args) = assert_total ("Closure: "++ (show name) ++ "(" ++ (show args) ++ ")")
        show (Field source tag pos) = assert_total ("Field: "++ (show source) ++ "[" ++ (show tag) ++ ", " ++ (show pos) ++"]")

    export
    Show StaticInfo where
        show (MKStaticInfo sources value) = "{" ++ (show sources) ++ "} = " ++ (show value)

-- Conversions
export
toValueInfo : StaticInfo -> ValueInfo
toValueInfo (MKStaticInfo _ (Const cs)) = extractConst $ toList cs
    where extractConst : List CairoConst -> ValueInfo
          extractConst (c::Nil) = ConstValue c
          extractConst _ = UnknownValue
toValueInfo (MKStaticInfo _ (Constructed ctrs)) = extractConst $ toList ctrs
    where extractConst : List (Int,List StaticInfo) -> ValueInfo
          extractConst ((t,fields)::Nil) = CompositeValue t (map toValueInfo fields)
          extractConst _ = UnknownValue
toValueInfo (MKStaticInfo _ (Closure (Just (name, missing)) captures)) = ClosureValue name missing (map toValueInfo captures)
toValueInfo (MKStaticInfo regs _) = process (toList regs)
    where process : List CairoReg -> ValueInfo
          process [Const c] = ConstValue c
          process _ = UnknownValue

export
fromValueInfo : ValueInfo -> StaticInfo
fromValueInfo UnknownValue = MKStaticInfo empty Unknown
fromValueInfo (ConstValue c) = MKStaticInfo (singleton (Const c)) (Const (singleton c))
fromValueInfo (CompositeValue tag fields) = MKStaticInfo empty (Constructed (fromList [(tag, map fromValueInfo fields)]))
fromValueInfo (ClosureValue name miss captures) = MKStaticInfo empty (Closure (Just (name,miss)) (map fromValueInfo captures))

fromEvalRes : EvalRes -> List StaticInfo -> StaticInfo
fromEvalRes (Failure s) _ = MKStaticInfo empty (Error s)
fromEvalRes (NewValue val) _ = fromValueInfo val
fromEvalRes (ArgValue Z) (x::xs) = x
fromEvalRes (ArgValue (S rem)) (x::xs) = fromEvalRes (ArgValue rem) xs
fromEvalRes _ _ = assert_total $ idris_crash "can not process eval res"

mutual
    mergeStaticValue : StaticValue -> StaticValue -> StaticValue
    mergeStaticValue (Error _) other = other -- The error would crash program so if we arrive here it is the other
    mergeStaticValue other (Error _) = other -- The error would crash program so if we arrive here it is the other
    mergeStaticValue (Const vs1) (Const vs2) = Const (union vs1 vs2)
    mergeStaticValue (Constructed c1) (Constructed c2) = Constructed (mergeWith mergeFields c1 c2)
        where mergeFields: List StaticInfo -> List StaticInfo -> List StaticInfo
              mergeFields f1 f2 = zipWith mergeStaticInfo f1 f2
    mergeStaticValue (Closure n1 f1) (Closure n2 f2) = Closure (mergeNames n1 n2) (zipWith mergeStaticInfo f1 f2)
        where mergeNames : Maybe (Name, Nat) -> Maybe (Name, Nat) -> Maybe (Name, Nat)
              mergeNames (Just (n1, m1)) (Just (n2, m2)) = if n1 == n2 && m1 == m2 then Just (n1, m1) else Nothing
              mergeNames _ _ = Nothing
    -- todo: shall we go to Unknown if both tags are diff and remove maybe?
    mergeStaticValue (Field s1 t1 p1) (Field s2 t2 p2) = if p1 /= p2 then Unknown else Field (mergeStaticInfo s1 s2) (mergeTag t1 t2) p1
        where mergeTag : Maybe Int -> Maybe Int -> Maybe Int
              mergeTag (Just t1) (Just t2) = if t1 == t2 then Just t1 else Nothing
              mergeTag _ _ = Nothing
    mergeStaticValue _ _ = Unknown

    export
    mergeStaticInfo : StaticInfo -> StaticInfo -> StaticInfo
    mergeStaticInfo (MKStaticInfo regs1 vals1) (MKStaticInfo regs2 vals2) = MKStaticInfo (intersection regs1 regs2) (mergeStaticValue vals1 vals2)

export
Semigroup StaticInfo where
   (<+>) = mergeStaticInfo

export
addBinding : StaticInfo -> CairoReg -> StaticInfo
addBinding (MKStaticInfo sources Unknown) r@(Const c) = MKStaticInfo (insert r sources) (Const (singleton c))
addBinding (MKStaticInfo sources (Const cs)) r@(Const c) = MKStaticInfo (insert r sources) (Const (insert c cs))
addBinding (MKStaticInfo sources value) r = MKStaticInfo (insert r sources) value

-- this checks if all the args are the fields 0 to N of the same value with the same tag as the new construct and if so returns the regs storing the original value
-- basically it reorganizes that unpacking all fields and then repacking them with the same tag produces the same value
export
findRepackedSrcs : Int -> List StaticInfo -> SortedSet CairoReg
findRepackedSrcs tag Nil = empty
findRepackedSrcs tag args@(f::fs) = if isCons (toList combinedSrcRegs) && (isJust (foldl checkPosIncrementAndTag (Just 0) args))
     then combinedSrcRegs
     else empty
     where extractFieldSource : StaticInfo -> SortedSet CairoReg
           extractFieldSource (MKStaticInfo _ (Field src _ _ )) = src.sources
           extractFieldSource _ = empty
           combinedSrcRegs : SortedSet CairoReg
           combinedSrcRegs = foldl1 intersection (map extractFieldSource (f::fs))
           checkPosIncrementAndTag : Maybe Nat -> StaticInfo -> Maybe Nat
           checkPosIncrementAndTag (Just expectedPos) (MKStaticInfo _ (Field _ (Just t) pos )) = if expectedPos == pos && t == tag
             then Just (expectedPos+1)
             else Nothing
           checkPosIncrementAndTag _ _ = Nothing

-- extract the constant value from StaticInfo if it has one
export
extractSingleConstant : StaticInfo -> Maybe CairoConst
extractSingleConstant (MKStaticInfo _ (Const cs)) = extractIfSameConstant (toList cs)
    where extractIfSameConstant : List CairoConst -> Maybe CairoConst
          extractIfSameConstant Nil = Nothing
          extractIfSameConstant (x::Nil) = Just x
          extractIfSameConstant _ = Nothing -- as is sorted set more then 1 elem means unequal
extractSingleConstant (MKStaticInfo srcs _) = if isCons allConstants
    then head' allConstants -- if they are more it is given that they are the same (otherwise the tracker screwed up)
    else Nothing
    where toConst : CairoReg -> List CairoConst
          toConst (Const c) = [c]
          toConst _ = []
          allConstants : List CairoConst
          allConstants = (toList srcs) >>= toConst

export
asConstants : List StaticInfo -> Maybe (List CairoConst)
asConstants args = if (all isJust mappedConstants) then Just (mappedConstants >>= maybeToList) else Nothing
    where mappedConstants : List (Maybe CairoConst)
          mappedConstants = (map extractSingleConstant args)
          maybeToList : Maybe CairoConst -> List CairoConst
          maybeToList (Just a) = [a]
          maybeToList Nothing = []

export
extractField : SortedMap Int (List StaticInfo) -> Nat -> StaticInfo
extractField ctrs pos = mergeAll (map (extract pos) (values ctrs))
    where extract : Nat -> List StaticInfo -> StaticInfo
          extract _ Nil = MKStaticInfo empty Unknown
          extract Z (f::fs) = f
          extract (S rem) (f::fs) = extract rem fs
          mergeAll : List StaticInfo -> StaticInfo
          mergeAll Nil = MKStaticInfo empty Unknown
          mergeAll (i::is) = foldl1 mergeStaticInfo (i::is)

extractSingleTag : SortedMap Int (List StaticInfo) -> Maybe Int
extractSingleTag s = extract (keys s)
    where extract : List Int -> Maybe Int
          extract (x::Nil) = Just x
          extract _ = Nothing
export
resolveTag : Maybe Int -> Int
resolveTag Nothing = 0
resolveTag (Just t) = t

-- Just the tracking part for generating the optim infos
export
staticImplTracker : SortedMap LinearImplicit (StaticInfo, CairoReg) -> SortedMap LinearImplicit StaticInfo
staticImplTracker impls = mapValueMap (\(_, reg) => MKStaticInfo (singleton reg) Unknown) impls

export
staticValueTracker : (v:InstVisit StaticInfo) -> Traversal (ScopedBindings StaticInfo) (ValBindType v StaticInfo)
staticValueTracker (VisitFunction _ params impls _) = pure (map paramInit params, mapValueMap paramInit impls)
    where paramInit : CairoReg -> StaticInfo
          paramInit reg = MKStaticInfo (singleton reg) Unknown
staticValueTracker (VisitForeignFunction _ _ _ _) = pure ()
staticValueTracker (VisitAssign r constInfo) = pure $ addBinding constInfo r
staticValueTracker (VisitMkCon r tag args) = pure $ addBinding (MKStaticInfo (findRepackedSrcs (resolveTag tag) args) (Constructed (singleton (resolveTag tag) args))) r
staticValueTracker (VisitMkClosure r name missing args) = pure $ MKStaticInfo (singleton r) (Closure (Just (name, missing)) args)
staticValueTracker (VisitApply r impls (MKStaticInfo regs (Closure (Just (name, Z)) args)) arg) = pure (MKStaticInfo (singleton r) Unknown, staticImplTracker impls)
staticValueTracker (VisitApply r impls (MKStaticInfo regs (Closure (Just (name, (S rem))) args)) arg) = pure (MKStaticInfo (singleton r) (Closure (Just (name, rem)) (args ++ [arg])), staticImplTracker impls)
staticValueTracker (VisitApply r impls _ _) = pure (MKStaticInfo (singleton r) Unknown, staticImplTracker impls)
staticValueTracker (VisitMkConstant r const) = pure $ MKStaticInfo (singleton r) (Const (singleton const))
staticValueTracker (VisitCall rs impls _ _) = pure (map (\r => MKStaticInfo (singleton r) Unknown) rs, staticImplTracker impls)
staticValueTracker (VisitExtprim rs impls name args) = pure (result (externalEval name (length rs) (map toValueInfo args)), staticImplTracker impls)
    where result : Maybe (List EvalRes) -> List StaticInfo
          result Nothing = map (\r => MKStaticInfo (singleton r) Unknown) rs
          result (Just res) = if (length res) == (length rs)
            then zipWith (\r,res => addBinding (fromEvalRes res args) r) rs res
            else assert_total $ idris_crash "constant evaluation returned wrong number of results"
staticValueTracker (VisitOp r impls fn args) = pure (result (evaluateConstantOp fn (map toValueInfo args)), staticImplTracker impls)
    where result : Maybe EvalRes -> StaticInfo
          result Nothing = MKStaticInfo (singleton r) Unknown
          result (Just res) = addBinding (fromEvalRes res args) r
staticValueTracker (VisitProject r src@(MKStaticInfo _ (Constructed ctrs)) pos) = pure $ result (extractField ctrs pos)
    where result : StaticInfo -> StaticInfo
          result (MKStaticInfo _ Unknown) = MKStaticInfo (singleton r) (Field src (extractSingleTag ctrs) pos)
          result field = addBinding field r
staticValueTracker (VisitProject r src pos) = pure $ MKStaticInfo (singleton r) (Field src Nothing pos) -- As we are not in a case we have no tag (otherwise case would have spezialized)
staticValueTracker (VisitNull r) = pure $ MKStaticInfo (singleton r) Unknown
staticValueTracker (VisitError r err) = pure $ MKStaticInfo (singleton r) (Error err)
staticValueTracker (VisitReturn _ _) = pure ()
staticValueTracker (VisitCase _) = pure ()
staticValueTracker (VisitConBranch Nothing) = pure $ Nothing
staticValueTracker (VisitConBranch (Just tag)) = pure $ case !getCaseBinding of
   Just (MKStaticInfo binds (Constructed ctrs)) => Just $ MKStaticInfo binds (Constructed (singleton tag (fromMaybe Nil (lookup tag ctrs))))
   Just (MKStaticInfo binds _ ) => Just $ MKStaticInfo binds (Constructed (singleton tag Nil))
   Nothing => Nothing
staticValueTracker (VisitConstBranch Nothing) = pure $ Nothing
staticValueTracker (VisitConstBranch (Just const)) = pure $ case !getCaseBinding of
   Just (MKStaticInfo binds _ ) => Just $ MKStaticInfo binds (Const (singleton const))
   Nothing => Nothing
staticValueTracker VisitBranchEnd = pure ()
staticValueTracker VisitCaseEnd = pure ()
staticValueTracker VisitEndFunction = pure ()

-- This is non generic/local folder -- we keep for now: as it is simpler and more efficient
export
localStaticTrackDef : (Name, CairoDef) -> List StaticInfo
localStaticTrackDef def = collect $ snd $ runVisitConcatCairoDef (valueCollector idLens (dbgDef def) staticValueTracker extractReturn, initialTrackerState) def
    where dbgDef : (Name, CairoDef) -> CairoReg -> StaticInfo
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (MKStaticInfo (singleton reg) Unknown)
          extractReturn : InstVisit StaticInfo -> Traversal (ScopedBindings StaticInfo) (List (List StaticInfo))
          extractReturn (VisitReturn rets _) = pure [rets]
          extractReturn _ = pure Nil
          collect : (List (List StaticInfo)) -> (List StaticInfo)
          collect Nil = trace "Tracked function has no return statement" Nil
          collect (x::Nil) = x
          collect (x1::x2::xs) = collect ((zipWith mergeStaticInfo x1 x2)::xs)

-- A version witch allows generified call handling --
public export
record GlobalStaticTrackerState s where
    constructor MkGlobalStaticTrackerState
    bindingState : ScopedBindings StaticInfo
    globalState : s

-- Lenses for leaner and more readable main definitions
bindingStateLens : Lens (GlobalStaticTrackerState s) (ScopedBindings StaticInfo)
bindingStateLens = MkLens bindingState (\ts,fn => {bindingState $= fn} ts)

globalStateLens : Lens (GlobalStaticTrackerState s) s
globalStateLens = MkLens globalState (\ts,fn => {globalState $= fn} ts)

public export
record CallData where
    constructor MKCallData
    function: Name
    implicits: SortedMap LinearImplicit (StaticInfo, CairoReg)
    arguments : List StaticInfo
    returns: List CairoReg

public export
interface CallTracker s where
    -- Binds values of function value
    context : (List CairoReg, SortedMap LinearImplicit CairoReg) -> s -> (List StaticInfo, SortedMap LinearImplicit StaticInfo)
    -- Binds returns of a function
    process_return : List StaticInfo -> SortedMap LinearImplicit StaticInfo -> s -> s
    -- Process nested function
    process : CallData -> s -> s
    -- Extract tracked values from processed function
    track : CallData -> s -> (List StaticInfo, SortedMap LinearImplicit StaticInfo)
    -- defaults (same as unmodified value Tracker)
    context (params, impls) _ = (map paramInit params, mapValueMap paramInit impls)
        where paramInit : CairoReg -> StaticInfo
              paramInit reg = MKStaticInfo (singleton reg) Unknown
    process_return _ _ s = s
    process _ s = s
    track (MKCallData _ impls _ rs) _ = (map (\r => MKStaticInfo (singleton r) Unknown) rs, staticImplTracker impls)

export
trackCall : CallTracker s => CallData -> Traversal (GlobalStaticTrackerState s) (List StaticInfo, SortedMap LinearImplicit StaticInfo)
trackCall callData = update >>= (\_ => compute)
    where update : Traversal (GlobalStaticTrackerState s) ()
          update = updateStateL globalStateLens (process callData)
          compute : Traversal (GlobalStaticTrackerState s) (List StaticInfo, SortedMap LinearImplicit StaticInfo)
          compute = map (track callData) (readStateL globalStateLens)

export
globalStaticTrackDef : CallTracker s => SortedMap Name CairoDef -> s -> (Name, CairoDef) -> (s, List StaticInfo)
globalStaticTrackDef defs globalState def = collect $ runVisitConcatCairoDef (valueCollector bindingStateLens (dbgDef def) customizedStaticValueTracker extractReturn, initialState) def
          -- these just lift traversals defined on (ScopedBindings StaticInfo) to work with (GlobalStaticTrackerState s) by using a lense to point to the LocalStaticOptimState
    where liftedStaticValueTracker: (v:InstVisit StaticInfo) -> Traversal (GlobalStaticTrackerState s) (ValBindType v StaticInfo)
          liftedStaticValueTracker inst = composeState bindingStateLens (staticValueTracker inst)
          -- These use the CallTracker to customize the value Tracker
          -- we use explicit branching for 'customizedStaticValueTracker' because 'fallbackTraversal' has problems handling dependent type 'ValBindType v StaticInfo'
          customizedStaticValueTracker : (v:InstVisit StaticInfo) -> Traversal (GlobalStaticTrackerState s) (ValBindType v StaticInfo)
          customizedStaticValueTracker (VisitCall rs impls name args) = trackCall (MKCallData name impls args rs)
          customizedStaticValueTracker (VisitFunction _ params impls _) = map (context (params, impls)) (readStateL globalStateLens)
          customizedStaticValueTracker (VisitReturn res impls) = updateStateL globalStateLens (process_return res impls)
          customizedStaticValueTracker inst = liftedStaticValueTracker inst
          dbgDef : (Name, CairoDef) -> CairoReg -> StaticInfo
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (MKStaticInfo (singleton reg) Unknown)
          extractReturn : InstVisit StaticInfo -> Traversal (GlobalStaticTrackerState s) (List (List StaticInfo))
          extractReturn (VisitReturn rets _) = pure [rets]
          extractReturn _ = pure Nil
          initialState : GlobalStaticTrackerState s
          initialState = MkGlobalStaticTrackerState initialTrackerState globalState
          collect : (GlobalStaticTrackerState s, List (List StaticInfo)) -> (s, List StaticInfo)
          collect (s, Nil) = trace "Tracked function has no return statement" (s.globalState, Nil)
          collect (s, x::Nil) = (s.globalState, x)
          collect (s, x1::x2::xs) = collect (s, (zipWith mergeStaticInfo x1 x2)::xs)
