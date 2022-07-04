module CodeGen.InjectLinearImplicits

import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Primitives.Externals
import Primitives.Primitives
import Data.SortedMap
import Data.SortedSet
import Core.Context
import CairoCode.Traversal.Base
import CairoCode.Traversal.Composition
import Utils.Lens
import Utils.Helpers

%hide Prelude.toList

extractImpls : (Name, CairoDef) -> (Name, SortedSet LinearImplicit)
extractImpls (n, FunDef _ impls _ _) = (n, fromList $ keys impls)
extractImpls (n, ExtFunDef _ _ impls _ _) = (n, fromList $ keys impls)
extractImpls (n, ForeignDef (MkForeignInfo _ _ impls _ _) _ _) = (n, fromList impls)

preloadLinearImplicitsDefs : List (Name, CairoDef) -> SortedMap Name (SortedSet LinearImplicit)
preloadLinearImplicitsDefs defs = fromList $ map extractImpls defs

collectApplyLinearImplicits : SortedMap Name (SortedSet LinearImplicit) -> List (Name, CairoDef) -> SortedSet LinearImplicit
collectApplyLinearImplicits implicitLookup defs = snd $ runVisitConcatCairoDefs (pureTraversal closureCollectTraversal) defs
    where closureCollectTraversal : InstVisit CairoReg -> SortedSet LinearImplicit
          closureCollectTraversal (VisitMkClosure _ name _ _ ) = fromMaybe empty (lookup name implicitLookup)
          closureCollectTraversal _ = empty


starkNetIntrinsicsNeededImplicits : StarkNetIntrinsic -> SortedSet LinearImplicit
-- Note: StorageVarAddr cairo functions take builtins, however unless they have arguments, they do not use them & ours do not have arguments
starkNetIntrinsicsNeededImplicits (StorageVarAddr _) = empty -- fromList [pedersen_builtin, range_check_builtin]
starkNetIntrinsicsNeededImplicits (EventSelector _) = empty -- fromList [pedersen_builtin, range_check_builtin]


discoverNeededLinearImplicitsDef : SortedMap Name (SortedSet LinearImplicit) -> SortedSet LinearImplicit -> (Name, CairoDef) -> SortedSet LinearImplicit
discoverNeededLinearImplicitsDef implicitLookup applyLinearImplicits def = snd $ runVisitConcatCairoDef (pureTraversal neededLinearImplicits) def
      where exludeExisting : SortedSet LinearImplicit -> LinearImplicitArgs -> SortedSet LinearImplicit
            exludeExisting needed existing = difference needed (fromList $ keys existing)
            lookupLinearImplicits : Name -> SortedSet LinearImplicit
            lookupLinearImplicits name = fromMaybe empty (lookup name implicitLookup)
            definedImpls : List LinearImplicit
            definedImpls = toList $ snd $ extractImpls def
            neededLinearImplicits : InstVisit CairoReg -> SortedSet LinearImplicit
            neededLinearImplicits (VisitApply _ linImpls _ _) = exludeExisting applyLinearImplicits linImpls
            neededLinearImplicits (VisitCall _ linImpls name _) = exludeExisting (lookupLinearImplicits name) linImpls
            neededLinearImplicits (VisitExtprim _ linImpls name _) = exludeExisting (fromList $ externalLinearImplicits name) linImpls
            neededLinearImplicits (VisitStarkNetIntrinsic _ linImpls intr _) = exludeExisting (starkNetIntrinsicsNeededImplicits intr) linImpls
            neededLinearImplicits (VisitOp  _ linImpls fn _) = exludeExisting (primFnLinearImplicits fn) linImpls
            -- This is just an integrity check
            neededLinearImplicits (VisitReturn _ linImpls) = if definedImpls /= (keys linImpls)
                 then assert_total $ idris_crash ("predefined implicits are not returned")
                 else empty
            neededLinearImplicits _ = empty

discoverNeededLinearImplicitsDefs : SortedMap Name (SortedSet LinearImplicit) -> SortedSet LinearImplicit -> List (Name, CairoDef) -> SortedMap Name (SortedSet LinearImplicit)
discoverNeededLinearImplicitsDefs implicitLookup applyLinearImplicits defs = foldl processCheckAndUpdateDef implicitLookup defs
    where processCheckAndUpdateDef : SortedMap Name (SortedSet LinearImplicit) -> (Name, CairoDef) -> SortedMap Name (SortedSet LinearImplicit)
          processCheckAndUpdateDef currentLookup def@(name,_) = updateDef $ discoverNeededLinearImplicitsDef currentLookup applyLinearImplicits def
                where definedImpls : SortedSet LinearImplicit
                      definedImpls = snd $ extractImpls def
                      checkedImpls : SortedSet LinearImplicit -> SortedSet LinearImplicit
                      checkedImpls discoveredLinearImplicits = if all (\i => not (contains i definedImpls)) discoveredLinearImplicits
                        then discoveredLinearImplicits
                        else assert_total $ idris_crash ("predefined implicits do not cover all instructions")
                      updateDef : SortedSet LinearImplicit -> SortedMap Name (SortedSet LinearImplicit)
                      updateDef discoveredLinearImplicits = insert name (union (checkedImpls discoveredLinearImplicits) (fromMaybe empty (lookup name currentLookup))) currentLookup

singleDiscoveryRun : SortedMap Name (SortedSet LinearImplicit) -> List (Name, CairoDef) -> (SortedSet LinearImplicit, SortedMap Name (SortedSet LinearImplicit))
singleDiscoveryRun implicitLookup defs = (appliedLinearImplicits, discoverNeededLinearImplicitsDefs implicitLookup appliedLinearImplicits defs)
    where appliedLinearImplicits : SortedSet LinearImplicit
          appliedLinearImplicits = collectApplyLinearImplicits implicitLookup defs

repeatedDiscoveryRun : SortedMap Name (SortedSet LinearImplicit) -> List (Name, CairoDef) -> (SortedSet LinearImplicit, SortedMap Name (SortedSet LinearImplicit))
repeatedDiscoveryRun implicitLookup defs = if (snd runResult) == implicitLookup
    then runResult
    else repeatedDiscoveryRun (snd runResult) defs
    where runResult : (SortedSet LinearImplicit, SortedMap Name (SortedSet LinearImplicit))
          runResult = singleDiscoveryRun implicitLookup defs

-- This does the discovery of all implicits needed per Name
executeLinearImplicitDiscovery : List (Name, CairoDef) -> (SortedSet LinearImplicit, SortedMap Name (SortedSet LinearImplicit))
executeLinearImplicitDiscovery defs = repeatedDiscoveryRun (preloadLinearImplicitsDefs defs) defs

-- Note: SortedMap CairoReg CairoReg only needed as Optimisation can not do forward substitution at branch border:
--          Meaning: "x = ...; y = x" is not translated to "y = ..." when y escapes the branch
--          If we ever do we can simplify this by just doing an ASSIGN at end of branch
--        Currently we record y = x in the map and use substituteRegs to make the translation
--       The List (CairoReg, RegGen) are the active register in each active branch
--        as well as the generator to generate the next register in that branch
record RegTrackerState where
    constructor MkRegTrackerState
    stack : List (CairoReg, RegisterGen)
    subst : SortedMap CairoReg CairoReg

-- Lenses for leaner and more readable main definitions
stackLens : Lens RegTrackerState (List (CairoReg, RegisterGen))
stackLens = MkLens stack (\ts,fn => {stack $= fn} ts)

substLens : Lens RegTrackerState (SortedMap CairoReg CairoReg)
substLens = MkLens subst (\ts,fn => {subst $= fn} ts)

headLens : Lens RegTrackerState (CairoReg, RegisterGen)
headLens = join stackLens headFailLens

activeRegLens : Lens RegTrackerState CairoReg
activeRegLens = join headLens leftLens

activeRegGenLens : Lens RegTrackerState RegisterGen
activeRegGenLens = join headLens rightLens

-- Accessors
getCurrentReg : Traversal RegTrackerState CairoReg
getCurrentReg = readStateL activeRegLens

getDepth : Traversal RegTrackerState Int
getDepth = map (\s => (cast $ length s) - 1) (readStateL stackLens)

advanceRegBinding : Traversal RegTrackerState (CairoReg, CairoReg)
advanceRegBinding = do
    beforeReg <- getCurrentReg
    depth <- getDepth
    _ <- updateStateL headLens (\(_,regGen) => nextRegister regGen depth)
    afterReg <- getCurrentReg
    pure (beforeReg, afterReg)

enterBranch : Show a => Maybe a -> Traversal RegTrackerState (CairoReg, CairoReg)
enterBranch tc = do
    beforeReg <- getCurrentReg
    depth <- getDepth
    regGen <- readStateL activeRegGenLens
    let nextRegAndGen = nextRegister (branchRegisterGen tc regGen) depth
    _ <- updateStateL stackLens (nextRegAndGen::)
    afterReg <- getCurrentReg
    pure (beforeReg, afterReg)

leaveBranch : Traversal RegTrackerState ()
leaveBranch = updateState update
    -- goes 2 elements deep on stack, so lenses do not improve the situation here
    where update : RegTrackerState -> RegTrackerState
          update (MkRegTrackerState ((branchReg, _)::(reg,regGen)::xs) subst) =
            MkRegTrackerState ((reg,regGen)::xs) (insert branchReg (fst $ nextRegister regGen (cast $ length xs)) subst)
          update _ = assert_total $ idris_crash "Illegal Active State"

implicitRegTransformer : SortedSet Name -> Bool -> LinearImplicit -> (InstVisit CairoReg -> Traversal RegTrackerState (List (InstVisit CairoReg)))
implicitRegTransformer neededByCall neededByApply impl = implicitRegInjector
    where implicitRegInjector : InstVisit CairoReg -> Traversal RegTrackerState (List (InstVisit CairoReg))
          implicitRegInjector (VisitFunction name tags params linImpls rets) = map (\r => [VisitFunction name tags params (insert impl r linImpls) rets]) getCurrentReg
          implicitRegInjector inst@(VisitApply res linImpls clo arg) = if neededByApply
              then map (\bind => [VisitApply res (insert impl bind linImpls) clo arg]) advanceRegBinding
              else pure [inst]
          implicitRegInjector inst@(VisitCall res linImpls name args) = if contains name neededByCall
              then map (\bind => [VisitCall res (insert impl bind linImpls) name args]) advanceRegBinding
              else pure [inst]
          implicitRegInjector inst@(VisitOp res linImpls fn args) = if contains impl (primFnLinearImplicits fn)
              then map (\bind => [VisitOp res (insert impl bind linImpls) fn args]) advanceRegBinding
              else pure [inst]
          implicitRegInjector inst@(VisitExtprim res linImpls name args) = if contains impl (fromList $ externalLinearImplicits name)
              then map (\bind => [VisitExtprim res (insert impl bind linImpls) name args]) advanceRegBinding
              else pure [inst]
          implicitRegInjector inst@(VisitStarkNetIntrinsic res linImpls intr args) = if contains impl (starkNetIntrinsicsNeededImplicits intr)
              then map (\bind => [VisitStarkNetIntrinsic res (insert impl bind linImpls) intr args]) advanceRegBinding
              else pure [inst]
          implicitRegInjector (VisitReturn res linImpls) = map (\(reg,_) => [VisitReturn res (insert impl reg linImpls)]) advanceRegBinding
          implicitRegInjector (VisitConBranch tag) = map (\(curReg, brReg) => [VisitConBranch tag, VisitAssign brReg curReg]) (enterBranch tag)
          implicitRegInjector (VisitConstBranch const) = map (\(curReg, brReg) => [VisitConstBranch const, VisitAssign brReg curReg]) (enterBranch const)
          implicitRegInjector (VisitBranchEnd) = map (\_ => [VisitBranchEnd]) leaveBranch
          implicitRegInjector (VisitCaseEnd) = map (\_ => [VisitCaseEnd]) advanceRegBinding
          implicitRegInjector inst = pure [inst]

areAppliesAffected : LinearImplicit -> SortedSet LinearImplicit -> Bool
areAppliesAffected = contains


transformLinearImplicits : LinearImplicit -> SortedMap Name (SortedSet LinearImplicit) -> SortedSet LinearImplicit -> (Name, CairoDef) -> SortedMap LinearImplicit CairoReg -> (Name, CairoDef)
transformLinearImplicits impl functionImpls applyImpls def@(name, _ ) linImpls = if isJust (lookup impl linImpls)
    then def -- is already present no need to inject
    else substituteDefRegisters substituteReg (snd result)
    where affectedCalls : SortedSet Name
          affectedCalls = fromList ((toList functionImpls) >>= (\(n,linImpls) => if contains impl linImpls then [n] else []))
          areAppliesAffected : Bool
          areAppliesAffected = contains impl applyImpls
          transformer : InstVisit CairoReg -> Traversal RegTrackerState (List (InstVisit CairoReg))
          transformer = implicitRegTransformer affectedCalls areAppliesAffected impl
          initialState : RegTrackerState
          initialState = MkRegTrackerState ((CustomReg (implicitName impl) Nothing, ("implicit_" ++ (implicitName impl), 0))::Nil) empty
          result : (RegTrackerState, (Name, CairoDef))
          result = runVisitTransformCairoDef (rawTraversal transformer initialState) def
          substituteReg : CairoReg -> Maybe CairoReg
          -- call recursively to ensure we end up with the final substitution
          substituteReg reg = maybeMap (\r => fromMaybe r (substituteReg r)) (lookup reg (subst (fst result)))

transformLinearImplicitDef : LinearImplicit -> SortedMap Name (SortedSet LinearImplicit) -> SortedSet LinearImplicit -> (Name, CairoDef) -> (Name, CairoDef)
transformLinearImplicitDef impl functionImpls applyImpls def@(name, FunDef _ linImpls _ _) = transformLinearImplicits impl functionImpls applyImpls def linImpls
transformLinearImplicitDef impl functionImpls applyImpls def@(name, ExtFunDef _ _ linImpls _ _) = transformLinearImplicits impl functionImpls applyImpls def linImpls
transformLinearImplicitDef _ _ _ def = def

transformDef : SortedMap Name (SortedSet LinearImplicit) -> SortedSet LinearImplicit -> (Name, CairoDef) -> (Name, CairoDef)
transformDef functionImpls applyImpls def@(name,_) = foldl (\d,impl => transformLinearImplicitDef impl functionImpls applyImpls d) def requiredImpls
    where requiredImpls : SortedSet LinearImplicit
          requiredImpls = fromMaybe empty (lookup name functionImpls)

transformDefs : SortedMap Name (SortedSet LinearImplicit) -> SortedSet LinearImplicit -> List (Name, CairoDef) -> List (Name, CairoDef)
transformDefs functionImpls applyImpls defs = map (transformDef functionImpls applyImpls) defs

export
injectLinearImplicitsDefs : List (Name, CairoDef) -> List (Name, CairoDef)
injectLinearImplicitsDefs defs = transformDefs (snd discoveryResult) (fst discoveryResult) defs
    where discoveryResult : (SortedSet LinearImplicit, SortedMap Name (SortedSet LinearImplicit))
          discoveryResult = executeLinearImplicitDiscovery defs
