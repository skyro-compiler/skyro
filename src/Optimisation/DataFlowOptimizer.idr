module Optimisation.DataFlowOptimizer

import CairoCode.Name
import Utils.Helpers
import CairoCode.Traversal.Base
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CommonDef
import Data.SortedSet
import Data.SortedMap
import Data.Fin
import Data.List
import Data.Maybe

import Debug.Trace
import Optimisation.DataFlowAnalyser

%hide Prelude.toList

data SpecialForm : Type where
    Unused : SpecialForm                   -- Replaces sources with Null
    TagOnly : SpecialForm                  -- Replaces Variant with inlined Tag and VisitConBranch with VisitConstBranch
    FieldLift : Nat -> SpecialForm         -- Replaces Closures And Variants with a single field
    FieldChange : Bool -> List Nat -> SpecialForm  -- Rearranges and Eliminates Closure & Data Fields

Show SpecialForm where
    show Unused = "Unused"
    show TagOnly = "TagOnly"
    show (FieldLift n) = "FieldLift("++(show n)++")"
    show (FieldChange tag ns) = "FieldChange("++(show tag)++"|"++(show ns)++")"

record Transformation where
    constructor MKTrans
    form : SpecialForm
    regs : SortedSet GlobalReg

-- Todo: improve to be tag specific inProject -- allows more elims : SortedMap Tag -> Nat (&then add the all to each tag)
-- -1 means tag is used
collectFields : SortedSet Int -> SrcSnkDesc -> SortedSet Int
collectFields col (Project _ pos) = insert (cast pos) col
collectFields col (ConBranch _) = insert (-1) col
collectFields _ _ = assert_total $ idris_crash "Unexpected Sink Desc for a Composite Value"

-- Todo: Improve to make FieldLift & FieldChange on a per tag basis
--       We can Field List if from each Tag only one is used
--       We can reorder/elim tags differently on a per Tag basis
--       If we have projects that access All - we fallback to tagless approach
--       However, we could improve analysis to store the covered tasks (instead of all) all Except - then we can from the sources figure out the missing ones
-- The main reason for Dataflow Optimisation
-- Todo: this calcs the field list way to many times (optimize
deadDataElim : DataFlow -> Maybe Transformation
deadDataElim flow = case usedFields of
    [] =>  Just (MKTrans Unused flow.registers)
    [-1] => Just (MKTrans TagOnly flow.registers)
    [f] => Just (MKTrans (FieldLift (cast f)) flow.registers)
    _ => if (length fieldList) == maxParams && needsTag
            then Nothing
            else Just (MKTrans (FieldChange needsTag fieldList) flow.registers)
    where usedFields : List Int
          usedFields = toList $ foldl collectFields empty flow.sinks
          fieldList : List Nat
          fieldList = sort $ map cast (filter (/=(-1)) usedFields)
          needsTag : Bool
          needsTag = any (==(-1)) usedFields
          max : List Nat -> Nat
          max = foldl maximum 0
          maxParams : Nat
          maxParams = case flow.structure of
             (Composite ctrs) => 1 + max (map max (map keys (values ctrs)))
             _ => assert_total $ idris_crash "Unexpected Structure in DataFlow"

-- Todo: delay this needs Extprims as Special form
-- if all sources are MkClosures with 0 captured fields we can inline Name (Special Extprim for Apply & MkClosure)
--  we can pass null / uninitialized for closure pointer
funRefInline : DataFlow -> Maybe Transformation
funRefInline _ = Nothing

analyseFlow : DataFlow -> Maybe Transformation
analyseFlow flow = case flow.structure of
    (Composite ctrs) => deadDataElim flow
    FieldEscape => funRefInline flow
    -- For now this is all
    _ => Nothing

makeSpecialFormIndex : Transformation -> SortedMap GlobalReg SpecialForm -> SortedMap GlobalReg SpecialForm
makeSpecialFormIndex (MKTrans form regs) sfs = foldl (\e,r => insert r form e) sfs regs

analyseAllFlows : List DataFlow -> SortedMap GlobalReg SpecialForm
analyseAllFlows flows = foldl processFlow empty flows
    where processFlow : SortedMap GlobalReg SpecialForm -> DataFlow -> SortedMap GlobalReg SpecialForm
          processFlow sfs df = case analyseFlow df of
            Nothing => sfs
            (Just opt) => makeSpecialFormIndex opt sfs

transformDef : SortedMap GlobalReg SpecialForm -> (CairoName, CairoDef) -> (CairoName, CairoDef)
transformDef optims def@(name, _) = toCairoDef $ reverse $ fst $ foldl trackAndTransform (Nil, MkCTrack Nil Nil empty) (fromCairoDef def)
    where global : CairoReg -> GlobalReg
          global = MkGlobalReg name
          form : GlobalReg -> Maybe SpecialForm
          form r = lookup r optims
          field : Nat -> List CairoReg -> CairoReg
          field Z (x::xs) = x
          field (S n) (_::xs) = field n xs
          field _ Nil = assert_total $ idris_crash "Non Existing Field"
          transformInst : CaseTracker -> InstVisit CairoReg -> InstVisit CairoReg
          transformInst _ inst@(VisitMkCon r t args) = case (form (global r)) of
            Nothing => inst
            (Just Unused) => VisitNull r
            (Just TagOnly) => VisitAssign r (Const (F (cast $ fromMaybe 0 t)))
            (Just (FieldLift n)) => VisitAssign r (field n args)
            (Just (FieldChange True fs)) => VisitMkCon r t (map (\n => field n args) fs)
            (Just (FieldChange False fs)) => VisitMkCon r Nothing (map (\n => field n args) fs)
          transformInst _ inst@(VisitMkClosure r name miss args) = case (form (global r)) of
            Nothing => inst
            (Just Unused) => VisitNull r
            (Just TagOnly) => assert_total $ idris_crash "Unimplemented needs special Form Extrprims"
            (Just (FieldLift n)) => VisitAssign r (field n args)
            (Just (FieldChange True fs)) => VisitMkClosure r name miss (map (\n => field n args) fs)
            (Just (FieldChange False fs)) => VisitMkCon r Nothing (map (\n => field n args) fs)
          transformInst _ inst@(VisitMkConstant r _) = case (form (global r)) of
            Nothing => inst
            (Just Unused) => VisitNull r
            _ => assert_total $ idris_crash "Illegal Special Form"

          transformInst _ inst@(VisitOp r _ pfn args) = case (form (global r)) of
            -- Todo: Add Sink Special Forms -- Or Remove the Ops completely
            --       For now this is ok as their are on analyses on Prims
            Nothing => inst
            (Just Unused) => VisitNull r
            _ => assert_total $ idris_crash "Illegal Special Form"
          transformInst tracker inst@(VisitConBranch t) = case (form (getBranchReg tracker)) of
             Nothing => inst
             (Just TagOnly) => VisitConstBranch (maybeMap (\i => F (cast i)) t)
             _ => assert_total $ idris_crash "Illegal Special Form"
          transformInst tracker inst@(VisitProject r v p) = case (form (global v)) of
            Nothing => inst
            (Just (FieldLift n)) => if n /= p
                then trace "This should not happen (Just here to be save)" (VisitNull r)
                else (VisitAssign r v)
            (Just (FieldChange _ fs)) => case findIndex (p==) fs of
                Nothing => assert_total $ idris_crash "Illegal Special Form"
                (Just newPos) => VisitProject r v (finToNat newPos)
            (Just Unused) => VisitNull r -- can this even happen
            _ => assert_total $ idris_crash "Illegal Special Form"

          -- the remaining insts are not considered sinks or sources or have no special forms
          transformInst _ inst = inst
          trackAndTransform : (List (InstVisit CairoReg), CaseTracker) -> InstVisit CairoReg -> (List (InstVisit CairoReg), CaseTracker)
          trackAndTransform (acc, track) inst = let nTrack = trackCase name inst track in ((transformInst nTrack inst)::acc, nTrack)

transformDefs : SortedMap GlobalReg SpecialForm -> List (CairoName, CairoDef) -> List (CairoName, CairoDef)
transformDefs optims defs =  map (transformDef optims) defs

public export
deadDataEliminator : List (CairoName, CairoDef) ->  List (CairoName, CairoDef)
deadDataEliminator defs = transformDefs (analyseAllFlows (dataFlowAnalysis defs)) defs
