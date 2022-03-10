module Optimisation.StaticProcessing.StaticTransformer

import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils

import Data.List
import Data.SortedSet
import Data.SortedMap
import Primitives.Primitives
import Primitives.Externals
import Primitives.Common
import Optimisation.StaticProcessing.InstructionDeduplication
import CairoCode.Traversal.Base
import CairoCode.Traversal.ValueTracker
import CairoCode.Traversal.Composition
import Optimisation.StaticProcessing.StaticTracker
import Utils.Helpers
import Utils.Lens
import Debug.Trace

%hide Prelude.toList

record LocalStaticOptimState where
    constructor MkLocalStaticOptimState
    dedupState : TrackerState
    bindings : ScopedBindings StaticInfo
    elimDepth : Int

-- Lenses for leaner and more readable main definitions
dedupStateLens : Lens LocalStaticOptimState TrackerState
dedupStateLens = MkLens dedupState (\ts,fn => {dedupState $= fn} ts)

elimDepthLens : Lens LocalStaticOptimState Int
elimDepthLens = MkLens elimDepth (\ts,fn => {elimDepth $= fn} ts)

bindingsLens : Lens LocalStaticOptimState (ScopedBindings StaticInfo)
bindingsLens = MkLens bindings (\ts,fn => {bindings $= fn} ts)

inlineError : List StaticInfo -> List CairoReg -> Lazy (List (InstVisit CairoReg)) -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
inlineError args res noErrorTrav = if isCons errors
    then pure $ map (\r => VisitError r consolidateErrors) res
    else pure noErrorTrav
    where extractError : StaticInfo -> List String
          extractError (MKStaticInfo _ (Error err)) = [err]
          extractError _ = []
          errors : List String
          errors = args >>= extractError
          consolidateErrors : String
          consolidateErrors = foldl (\acc,err => acc ++ " " ++ err) "" errors

-- Because of assigns, repackings etc.. we may end up with multiple registers storing the same value
--  This function chooses one. It tries to choose the one least likely to be eliminated (or one that does not cost Insts if not eliminated)
-- Note: This assumes that list is sorted according to lifetime (which is default for CairoReg in CairoCode)
chooseBestReg : List CairoReg -> CairoReg
chooseBestReg (x::Nil) = x -- This is the case most likely to happen (only one candidate)
-- Note: If sort changes implement this differently (that is  why we treated this case seperately)
chooseBestReg (x::xs) = x
-- Note: This case is only used in Projection, everywhere else this would mean a mistake in the tracker
chooseBestReg Nil = Eliminated

export
resolveInfToReg : StaticInfo -> CairoReg
resolveInfToReg inf = result $ extractSingleConstant inf
    where result : Maybe CairoConst -> CairoReg
          result Nothing = chooseBestReg $ toList (inf.sources)
          result (Just c) = Const c

manifestRegister : CairoReg -> CairoReg -> InstVisit CairoReg
manifestRegister res (Const c) = VisitMkConstant res c
manifestRegister res Eliminated = VisitError res "CanNotManifestEliminatedRegister"
manifestRegister res reg = VisitAssign res reg

manifestConstant : CairoReg -> Maybe CairoConst -> InstVisit CairoReg
manifestConstant res Nothing = VisitError res "UndefinedConstantOperation"
manifestConstant res (Just c) = VisitMkConstant res c

canManifestEvalRes : EvalRes -> Bool
canManifestEvalRes (Failure _) = True
canManifestEvalRes (NewValue val) = isJust $ extractSingleConstant $ fromValueInfo val
canManifestEvalRes (ArgValue _) = True

manifestEvalRes : CairoReg -> EvalRes -> List StaticInfo -> InstVisit CairoReg
manifestEvalRes reg (Failure s) _ = VisitError reg "UndefinedPrimitiveOperation"
manifestEvalRes reg (NewValue val) _ = (manifestConstant reg) $ extractSingleConstant $ fromValueInfo val
manifestEvalRes reg (ArgValue Z) (x::xs) = VisitAssign reg (resolveInfToReg x)
manifestEvalRes reg (ArgValue (S rem)) (x::xs) = manifestEvalRes reg (ArgValue rem) xs
manifestEvalRes _  _ _ = assert_total $ idris_crash "can not process eval res"

reassignUnusedLinearImplicits : SortedSet LinearImplicit -> SortedMap LinearImplicit (StaticInfo, CairoReg) -> List (InstVisit CairoReg)
reassignUnusedLinearImplicits usedLinearImplicits availableLinearImplicits = map (\(_,(f,t)) => VisitAssign t (resolveInfToReg f)) unusedLinearImplicits
    where unusedLinearImplicits : List (LinearImplicit, (StaticInfo, CairoReg))
          unusedLinearImplicits = filter (\(i,_) => not (contains i usedLinearImplicits)) (toList availableLinearImplicits)

export
resolveLinearImplicits : SortedMap LinearImplicit (StaticInfo, CairoReg) -> SortedMap LinearImplicit (CairoReg, CairoReg)
resolveLinearImplicits linImpls = mapValueMap (\(f,t) => (resolveInfToReg f,t)) linImpls

canEliminate : Traversal LocalStaticOptimState Bool
canEliminate = map (/=0) (readStateL elimDepthLens)

eliminateBranch : Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
eliminateBranch = map (\_ => Just []) (updateStateL elimDepthLens (+1))

keepBranch : InstVisit CairoReg -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
keepBranch inst = pure $ Just [inst]

forwardBranchInst : Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
forwardBranchInst = pure Nothing

caseBindings : Traversal LocalStaticOptimState (Maybe StaticInfo)
caseBindings = composeState bindingsLens resolveCaseBinding
    where resolveCaseBinding : Traversal (ScopedBindings StaticInfo) (Maybe StaticInfo)
          resolveCaseBinding = case !getCaseReg of
              Nothing => pure Nothing
              (Just (Const c)) => pure $ Just $ MKStaticInfo (singleton $ Const c) (Const $ singleton c)
              (Just reg) => getBinding reg

branchFilter : InstVisit CairoReg -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
branchFilter (VisitConBranch reg) = canEliminate >>= process
    where process : Bool -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
          process True = eliminateBranch
          process False = forwardBranchInst

branchFilter (VisitConstBranch reg) = canEliminate >>= process
    where process : Bool -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
          process True = eliminateBranch
          process False = forwardBranchInst

branchFilter VisitBranchEnd = canEliminate >>= process
   where process : Bool -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
         process True = map (\_ => Just []) (updateStateL elimDepthLens (\a => a-1))
         process False = forwardBranchInst

branchFilter _ = canEliminate >>= process
   where process : Bool -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
         process True = pure $ Just []
         process False = forwardBranchInst

branchEliminationDetection : InstVisit StaticInfo -> Traversal LocalStaticOptimState (Maybe (List (InstVisit CairoReg)))
branchEliminationDetection (VisitConBranch (Just t)) = case !caseBindings of
    (Just (MKStaticInfo _ (Constructed ctrs))) => if isJust (lookup t ctrs) then keepBranch (VisitConBranch (Just t)) else eliminateBranch
    _ => keepBranch (VisitConBranch (Just t))
branchEliminationDetection (VisitConstBranch (Just c)) = case !caseBindings of
    (Just (MKStaticInfo _ (Const vals))) => if contains c vals then keepBranch (VisitConstBranch (Just c)) else eliminateBranch
    _ => keepBranch (VisitConstBranch (Just c))
branchEliminationDetection (VisitConBranch Nothing) = keepBranch (VisitConBranch Nothing)
branchEliminationDetection (VisitConstBranch Nothing) = keepBranch (VisitConstBranch Nothing)
branchEliminationDetection VisitBranchEnd = keepBranch VisitBranchEnd
branchEliminationDetection _ = forwardBranchInst

constantFoldTransform : SortedMap Name CairoDef -> InstVisit StaticInfo -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
constantFoldTransform defs inst = transformer inst
    where extractLinearImplicits : CairoDef -> SortedSet LinearImplicit
          extractLinearImplicits (FunDef _ linImpls _ _) = fromList $ keys linImpls
          extractLinearImplicits (ForeignDef info _ _) = fromList $ implicits info
          implicitLookup : SortedMap Name (SortedSet LinearImplicit)
          implicitLookup = mapValueMap extractLinearImplicits defs
          transformer : InstVisit StaticInfo -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
          transformer (VisitFunction name params impls rets) = pure [VisitFunction name params impls rets]
          transformer (VisitForeignFunction name info args rets) = pure [VisitForeignFunction name info args rets]
          transformer (VisitAssign res from) = inlineError [from] [res] [manifestRegister res (resolveInfToReg from)]
          transformer (VisitMkCon res tag args) = inlineError args [res] inst
            where repackedSrcs : List CairoReg
                  repackedSrcs = toList (findRepackedSrcs (resolveTag tag) args)
                  inst : List (InstVisit CairoReg)
                  inst = if isNil repackedSrcs
                    then [VisitMkCon res tag (map resolveInfToReg args)]
                    else [manifestRegister res (chooseBestReg repackedSrcs)]
          transformer (VisitMkClosure res name miss args) = inlineError args [res] [VisitMkClosure res name miss (map resolveInfToReg args)]
          transformer (VisitApply res linImpls (MKStaticInfo _ (Closure (Just (name, 1)) args)) arg) = inlineError allArgs [res] ((VisitCall [res] callLinearImplicits name (map resolveInfToReg allArgs))::implicitReassigns)
            where allArgs : List StaticInfo
                  allArgs = args ++ [arg]
                  usedLinearImplicits : SortedSet LinearImplicit
                  usedLinearImplicits = fromMaybe empty (lookup name implicitLookup)
                  callLinearImplicits : SortedMap LinearImplicit (CairoReg, CairoReg)
                  callLinearImplicits = resolveLinearImplicits $ fromList $ filter (\(i,_) => contains i usedLinearImplicits) (toList $ linImpls)
                  implicitReassigns : List (InstVisit CairoReg)
                  implicitReassigns = reassignUnusedLinearImplicits usedLinearImplicits linImpls
          transformer (VisitApply res linImpls (MKStaticInfo _ (Closure (Just (name, (S rem))) args)) arg) = inlineError allArgs [res] ((VisitMkClosure res name rem (map resolveInfToReg allArgs))::implicitReassigns)
            where allArgs : List StaticInfo
                  allArgs = args ++ [arg]
                  implicitReassigns : List (InstVisit CairoReg)
                  implicitReassigns = reassignUnusedLinearImplicits empty linImpls
          transformer (VisitApply res linImpls clo arg) = inlineError [clo,arg] [res] [VisitApply res (resolveLinearImplicits linImpls) (resolveInfToReg clo) (resolveInfToReg arg)]
          transformer (VisitOp res linImpls fn args) = inlineError args [res] (result (evaluateConstantOp fn (map toValueInfo args)))
                      where result : Maybe EvalRes -> List (InstVisit CairoReg)
                            result (Just nRes) = if canManifestEvalRes nRes
                              then (manifestEvalRes res nRes args)::(reassignUnusedLinearImplicits empty linImpls)
                              else [VisitOp res (resolveLinearImplicits linImpls) fn (map resolveInfToReg args)]
                            result _ = [VisitOp res (resolveLinearImplicits linImpls) fn (map resolveInfToReg args)]
          transformer (VisitCall res linImpls name args) = inlineError args res [VisitCall res (resolveLinearImplicits linImpls) name (map resolveInfToReg args)]
          transformer (VisitExtprim res linImpls name args) = inlineError args res (result (externalEval name (length res) (map toValueInfo args)))
            where result : Maybe (List EvalRes) -> List (InstVisit CairoReg)
                  result (Just nRes) = if all canManifestEvalRes nRes
                    then (zipWith (\reg,res => manifestEvalRes reg res args) res nRes) ++ (reassignUnusedLinearImplicits empty linImpls)
                    else [VisitExtprim res (resolveLinearImplicits linImpls) name (map resolveInfToReg args)]
                  result _ = [VisitExtprim res (resolveLinearImplicits linImpls) name (map resolveInfToReg args)]
          transformer (VisitReturn res linImpls) = pure [VisitReturn (map resolveInfToReg res) (mapValueMap resolveInfToReg linImpls)]
          transformer (VisitProject res arg@(MKStaticInfo _ (Constructed ctrs)) pos) = inlineError [arg] [res] (result (resolveInfToReg (extractField ctrs pos)))
            where result : CairoReg -> List (InstVisit CairoReg)
                  result Eliminated = [VisitProject res (resolveInfToReg arg) pos]
                  result reg = [manifestRegister res reg]
          transformer (VisitProject res arg pos) = inlineError [arg] [res] [VisitProject res (resolveInfToReg arg) pos]
          transformer (VisitCase reg) = pure [VisitCase (resolveInfToReg reg)]
          -- Untouched ones
          transformer VisitCaseEnd = pure $ [VisitCaseEnd]
          transformer (VisitNull reg) = pure $ [VisitNull reg]
          transformer (VisitError reg err) = pure $ [VisitError reg err]
          transformer (VisitMkConstant reg c) = pure $ [VisitMkConstant reg c]
          transformer VisitEndFunction = pure $ [VisitEndFunction]
          -- Covered by Branch Eliminator --
          transformer (VisitConBranch t) = assert_total $ idris_crash "constantFoldTransform must be coupled with a branch hanlder"
          transformer (VisitConstBranch c) = assert_total $ idris_crash "constantFoldTransform must be coupled with a branch hanlder"
          transformer VisitBranchEnd = assert_total $ idris_crash "constantFoldTransform must be coupled with a branch hanlder"

{-
 1. skips the instruction if it lies in an eliminated branch
 2. it substitutes registers for their statically known value
 3. if a branch instruction it decides if the branch is needed or not (used in 1.)
    for unneeded branches the branching instruction is skipped
 4. it replaces or eliminates instructions based on the static value of the used registers where possible
 5. it eliminates duplicated instructions (instructions already executed earlier on the same registers)
 6. for the remaining transformed instructions it statically executes them where possible to find the static values of its returns based on the static values of the inputs (for 2.)

 start - value (Reg) & state -> branchFilter | case Just: - value (Reg) & state ------------------------------------------------------------------------------v
                                             | case Nothing: - state ->  valueTransformer ( staticValueTracker, transformerPipeline) - value (Reg) & state -> end

 transformPipeline: start - value (StaticInfo) & state -> branchAwareFolder - state & [value (Reg)] -> for each value : instructionDeduplication - state & [value (Reg)] -> end

 branchAwareFolder: start - value (StaticInfo) & state -> branchEliminationDetection | case Just: - value (Reg) & state -----------------------------------------v
                    |                                                                | case Nothing: - state -> constantFoldTransform - [value (Reg)] & state -> end
                    | - value (StaticInfo) ---------------------------------------------------------------------^

branchFilter : Skippes unused branches
instructionDeduplication : Removes duplicated instructions (same regs as inputs)
constantFoldTransform : Simplifies instruction based on static input
-}
export
localStaticOptimizeDef : List (Name, CairoDef) -> (Name, CairoDef) -> (Name, CairoDef)
localStaticOptimizeDef defs def = snd $ runVisitTransformCairoDef (transformerPipeline, initialState) def
    where liftedStaticValueTracker: (v:InstVisit StaticInfo) -> Traversal LocalStaticOptimState (ValBindType v StaticInfo)
          liftedStaticValueTracker inst = composeState bindingsLens (staticValueTracker inst)
          branchAwareFolder : InstVisit StaticInfo -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
          branchAwareFolder = fallbackTraversal branchEliminationDetection (constantFoldTransform (fromList defs))
          transformPipeline : InstVisit StaticInfo -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
          transformPipeline = chainedTraversal branchAwareFolder (lensTraversal dedupStateLens instructionDeduplication)
          dbgDef : (Name, CairoDef) -> CairoReg -> StaticInfo
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (MKStaticInfo (singleton reg) Unknown)
          activeBranchPipeline : InstVisit CairoReg -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
          activeBranchPipeline = valueTransformer bindingsLens (dbgDef def) liftedStaticValueTracker transformPipeline
          transformerPipeline : InstVisit CairoReg -> Traversal LocalStaticOptimState (List (InstVisit CairoReg))
          transformerPipeline = fallbackTraversal branchFilter activeBranchPipeline
          initialState : LocalStaticOptimState
          initialState = MkLocalStaticOptimState initialDedupState initialTrackerState 0

public export
localStaticOptimizeDefs : List (Name, CairoDef) -> List (Name, CairoDef)
localStaticOptimizeDefs defs = map (localStaticOptimizeDef defs) defs

-- A version witch allows generified call handling --
public export
record GlobalStaticOptimState s where
    constructor MkGlobalStaticOptimState
    folderState : LocalStaticOptimState
    globalState : s

-- Lenses for leaner and more readable main definitions
folderStateLens : Lens (GlobalStaticOptimState s) LocalStaticOptimState
folderStateLens = MkLens folderState (\ts,fn => {folderState $= fn} ts)

globalStateLens : Lens (GlobalStaticOptimState s) s
globalStateLens = MkLens globalState (\ts,fn => {globalState $= fn} ts)

public export
interface CallHandler s where
    -- Binds values of function value
    context : (List CairoReg, SortedMap LinearImplicit CairoReg) -> Traversal s (List StaticInfo, SortedMap LinearImplicit StaticInfo)
    -- Binds returns of a function
    return : List StaticInfo -> SortedMap LinearImplicit StaticInfo -> Traversal s ()
    -- Extract tracked values from processed function
    track : CallData -> Traversal s (List StaticInfo, SortedMap LinearImplicit StaticInfo)
    -- Replace tracked function with inlined code
    transform : CallData -> Traversal s (List (InstVisit CairoReg))
    -- defaults (same as unmodified value Tracker)
    context (params, impls) = pure (map paramInit params, mapValueMap paramInit impls)
        where paramInit : CairoReg -> StaticInfo
              paramInit reg = MKStaticInfo (singleton reg) Unknown
    return _ _ = pure ()
    track (MKCallData _ impls _ rs) = pure (map (\r => MKStaticInfo (singleton r) Unknown) rs, staticImplTracker impls)
    -- todo: make a more advanced inline error based one here as default -- needs to factor out traversal
    transform (MKCallData name impls args rs) = pure [VisitCall rs (resolveLinearImplicits impls) name (map resolveInfToReg args)]

callTracking : CallHandler s => CallData -> Traversal (GlobalStaticOptimState s) (List StaticInfo, SortedMap LinearImplicit StaticInfo)
callTracking callData = composeState globalStateLens (track callData)

callTransform: CallHandler s => CallData -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
callTransform callData = composeState globalStateLens (transform callData)

-- The actual generified folder (usable for global folding, inlining, specialisation, ...)
{-
 Works the same as localStaticOptimizeDef. However it can customize how call instructions are treated over a CallHandler
 Further it allows to collect the static values produced by  return instructions over CallHandler
 It introduces an additional state for the functions used in CallHandler
 This allows to define recursive algorithms that follow the call graph (thus global instead of local)
-}
public export
globalStaticOptimizeDef : CallHandler s => SortedMap Name CairoDef -> s -> (Name, CairoDef) -> ((Name, CairoDef), s)
globalStaticOptimizeDef defs globalState def = extract $ runVisitTransformCairoDef (transformerPipeline, initialState) def
    where bindLens : Lens (GlobalStaticOptimState s) (ScopedBindings StaticInfo)
          bindLens = join folderStateLens bindingsLens
          -- these just lift traversals defined on LocalStaticOptimState to work with (GlobalStaticOptimState s) by using a lense to point to the LocalStaticOptimState
          liftedStaticValueTracker: (v:InstVisit StaticInfo) -> Traversal (GlobalStaticOptimState s) (ValBindType v StaticInfo)
          liftedStaticValueTracker inst = composeState bindLens (staticValueTracker inst)
          liftedBranchEliminatorTransform : InstVisit StaticInfo -> Traversal (GlobalStaticOptimState s) (Maybe (List (InstVisit CairoReg)))
          liftedBranchEliminatorTransform inst = composeState folderStateLens (branchEliminationDetection inst)
          liftedBranchFilter : InstVisit CairoReg -> Traversal (GlobalStaticOptimState s) (Maybe (List (InstVisit CairoReg)))
          liftedBranchFilter inst = composeState folderStateLens (branchFilter inst)
          liftedConstantFoldTransform : InstVisit StaticInfo -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
          liftedConstantFoldTransform inst = composeState folderStateLens (constantFoldTransform defs inst)
          -- These use the CallHandler to customize the value Tracker
          -- we use explicit branching for 'customizedStaticValueTracker' because 'fallbackTraversal' has problems handling dependent type 'ValBindType v StaticInfo'
          customizedStaticValueTracker : (v:InstVisit StaticInfo) -> Traversal (GlobalStaticOptimState s) (ValBindType v StaticInfo)
          customizedStaticValueTracker (VisitCall rs impls name args) = callTracking (MKCallData name impls args rs)
          customizedStaticValueTracker (VisitFunction _ params impls _) = composeState globalStateLens (context (params, impls))
          -- Note: Putting this here is suboptimal as it requires the tracker to handle it
          --  but putting it in the transform prevents transformations of returns
          --  thats why its here and why we added a forwarding in the return case of the tracker
          customizedStaticValueTracker (VisitReturn res impls) = composeState globalStateLens (return res impls)
          customizedStaticValueTracker inst = liftedStaticValueTracker inst
          -- These use the CallHandler to customize the constant Folder
          -- we use explicit branching for 'customizedConstantFoldTransform' to be congruent with 'customizedStaticValueTracker'
          customizedConstantFoldTransform : InstVisit StaticInfo -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
          customizedConstantFoldTransform (VisitCall rs impls name args) = callTransform (MKCallData name impls args rs)
          customizedConstantFoldTransform inst = liftedConstantFoldTransform inst
          -- These are the same as in the local variant
          branchAwareFolder : InstVisit StaticInfo -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
          branchAwareFolder = fallbackTraversal liftedBranchEliminatorTransform customizedConstantFoldTransform
          transformPipeline : InstVisit StaticInfo -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
          transformPipeline = chainedTraversal branchAwareFolder (lensTraversal (join folderStateLens dedupStateLens) instructionDeduplication)
          dbgDef : (Name, CairoDef) -> CairoReg -> StaticInfo
          dbgDef (name, def) reg = trace "Register not bound in \{show name}: \{show reg}" (MKStaticInfo (singleton reg) Unknown)
          activeBranchPipeline : InstVisit CairoReg -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
          activeBranchPipeline = valueTransformer bindLens (dbgDef def) customizedStaticValueTracker transformPipeline
          transformerPipeline : InstVisit CairoReg -> Traversal (GlobalStaticOptimState s) (List (InstVisit CairoReg))
          transformerPipeline = fallbackTraversal liftedBranchFilter activeBranchPipeline
          initialState : GlobalStaticOptimState s
          initialState = MkGlobalStaticOptimState (MkLocalStaticOptimState initialDedupState initialTrackerState 0) globalState
          -- this does extract the CallHandler state from the GlobalStaticOptimState
          extract : (GlobalStaticOptimState s, (Name, CairoDef)) -> ((Name, CairoDef), s)
          extract (MkGlobalStaticOptimState _ globalState, def) = (def, globalState)
