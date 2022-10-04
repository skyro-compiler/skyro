module Optimisation.StaticProcessing.InstructionDeduplication

-- import Core.Context
import CairoCode.Name
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Data.List
import Data.Maybe
import Data.SortedMap
import CairoCode.Traversal.Base
import CairoCode.Traversal.Composition
import Utils.Lens
import CommonDef
import Primitives.Externals

%hide Prelude.toList

-- This helps to deduplicate instructions representing the same operation with the same arguments
--  The second apperance is replaced by assigning the result of the first to the second (instead of recomputing)
--  Note: Together with StaticTransformer this can eliminate CommonSub Expressions unless an if is involved

-- This is part of StaticOptimisation/Constant Folding
--  A seperate module is used to keep the main module small

-- Instruction representation that only captures the inputs not the outputs not implicits
-- However, non relevant instructions like Null, Error or Assign are omitted

export
data InstInput: Type where
     Construct : Maybe Int -> List CairoReg -> InstInput
     Closure : CairoName -> List CairoReg -> InstInput
     Apply : CairoReg -> CairoReg -> InstInput
     Call : CairoName -> List CairoReg -> InstInput
     Op : CairoPrimFn -> List CairoReg -> InstInput
     Extprim : CairoName -> List CairoReg -> InstInput
     Intrinsic : StarkNetIntrinsic -> List CairoReg -> InstInput
     Project : Nat -> CairoReg -> InstInput

public export
Eq InstInput where
  (==) (Construct t1 a1) (Construct t2 a2) = t1 == t2 && a1 == a2
  (==) (Closure n1 a1) (Closure n2 a2) = n1 == n2 && a1 == a2
  (==) (Apply c1 a1) (Apply c2 a2) = c1 == c2 && a1 == a2
  (==) (Call n1 a1) (Call n2 a2) = n1 == n2 && a1 == a2
  (==) (Op f1 a1) (Op f2 a2) = f1 == f2 && a1 == a2
  (==) (Extprim n1 a1) (Extprim n2 a2) = n1 == n2 && a1 == a2
  (==) (Intrinsic i1 a1) (Intrinsic i2 a2) = i1 == i2 && a1 == a2
  (==) (Project p1 a1) (Project p2 a2) = p1 == p2 && a1 == a2
  (==) _ _  = False

public export
Ord InstInput where
  compare (Construct t1 a1) (Construct t2 a2) = thenCompare (compare t1 t2) (compare a1 a2)
  compare (Closure n1 a1) (Closure n2 a2) = thenCompare (compare n1 n2) (compare a1 a2)
  compare (Apply c1 a1) (Apply c2 a2) = thenCompare (compare c1 c2) (compare a1 a2)
  compare (Call n1 a1) (Call n2 a2) = thenCompare (compare n1 n2) (compare a1 a2)
  compare (Op f1 a1) (Op f2 a2) = thenCompare (compare f1 f2) (compare a1 a2)
  compare (Extprim n1 a1) (Extprim n2 a2) = thenCompare (compare n1 n2) (compare a1 a2)
  compare (Intrinsic i1 a1) (Intrinsic i2 a2) = thenCompare (compare i1 i2) (compare a1 a2)
  compare (Project p1 a1) (Project p2 a2)  = thenCompare (compare p1 p2) (compare a1 a2)
  compare a b = compare (dataOrder a) (dataOrder b)
    where dataOrder : InstInput -> Int
          dataOrder (Construct _ _) = 0
          dataOrder (Closure _ _) = 1
          dataOrder (Apply _ _) = 2
          dataOrder (Call _ _) = 3
          dataOrder (Op _ _) = 4
          dataOrder (Extprim _ _) = 5
          dataOrder (Intrinsic _ _) = 6
          dataOrder (Project _ _) = 7

inputFromVisit : InstVisit CairoReg -> Maybe (List CairoReg, InstInput)
inputFromVisit (VisitMkCon res tag args) = Just ([res], Construct tag args)
inputFromVisit (VisitMkClosure res name _ args) = Just ([res], Closure name args)
inputFromVisit (VisitApply res _ f a) = Just ([res], Apply f a)
inputFromVisit (VisitCall res _ name args) = Just (res, Call name args)
inputFromVisit (VisitOp res _ fn args) =  Just ([res], Op fn args)
inputFromVisit (VisitExtprim res _ name args) = if externalIsTransparent name
    then Just (res, Extprim name args)
    else Nothing
inputFromVisit (VisitStarkNetIntrinsic res _ intr args) = Just ([res], Intrinsic intr args)
inputFromVisit (VisitProject res arg pos) = Just ([res], Project pos arg)
inputFromVisit _ = Nothing

public export
ActiveInsts : Type
ActiveInsts = SortedMap InstInput (List CairoReg)

public export
TrackerState : Type
TrackerState = List ActiveInsts

activeInstructionTracker : InstVisit CairoReg -> Traversal TrackerState ()
activeInstructionTracker (VisitConBranch _ ) = readStateL headFailLens >>= (\head => updateState (head::))
activeInstructionTracker (VisitConstBranch _ ) = readStateL headFailLens >>= (\head => updateState (head::))
activeInstructionTracker VisitBranchEnd = readStateL tailFailLens >>= (\tail => writeState tail)
activeInstructionTracker VisitEndFunction = readStateL tailFailLens >>= (\tail => writeState (empty::tail))
activeInstructionTracker inst = process $ inputFromVisit inst
    where process : Maybe (List CairoReg, InstInput) -> Traversal TrackerState ()
          process Nothing = pure ()
          process (Just (regs, inst)) = updateStateL headFailLens (insert inst regs)

reassignImpls : SortedMap LinearImplicit (CairoReg, CairoReg) -> List (InstVisit CairoReg)
reassignImpls impls = map (\(_,(from,to)) => VisitAssign to from) (toList impls)

reassignInstImpls : InstVisit CairoReg -> List (InstVisit CairoReg)
reassignInstImpls (VisitApply _ impls _ _) = reassignImpls impls
reassignInstImpls (VisitCall _ impls _ _) = reassignImpls impls
reassignInstImpls (VisitOp _ impls _ _) = reassignImpls impls
reassignInstImpls (VisitExtprim _ impls _ _) = reassignImpls impls
reassignInstImpls (VisitStarkNetIntrinsic _ impls _ _) = reassignImpls impls
reassignInstImpls _ = Nil

activeInstructionDedup : InstVisit CairoReg -> Traversal TrackerState (List (InstVisit CairoReg))
activeInstructionDedup inst = pure $ fromMaybe [inst] (fetchReplacement !(readStateL headFailLens))
    where fetchReplacement : ActiveInsts -> Maybe (List (InstVisit CairoReg))
          fetchReplacement activeInsts = do
              (res, inputInst) <- inputFromVisit inst
              original <- lookup inputInst activeInsts
              pure $ if (length res) == (length original)
                  then (zipWith (\r,o => VisitAssign r o) res original) ++ (reassignInstImpls inst)
                  else [inst]

export
instructionDeduplication : InstVisit CairoReg -> Traversal TrackerState (List (InstVisit CairoReg))
instructionDeduplication = traverseTransform activeInstructionDedup activeInstructionTracker

export
initialDedupState : TrackerState
initialDedupState = empty::Nil
