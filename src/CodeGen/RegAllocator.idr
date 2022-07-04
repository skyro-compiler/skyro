module CodeGen.RegAllocator

import CommonDef
import Core.Name.Namespace
import Core.Context
import Compiler.Common
import Compiler.ANF
import Data.List
import Data.String
import Data.Vect
import Data.SortedSet
import Data.SortedMap
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import Primitives.Externals
import Primitives.Primitives

%hide Prelude.toList

data Elem : Type where
   Branch : Int -> Elem
   Case : Int -> Elem

Eq Elem where
 (==) (Branch a) (Branch b) = a == b
 (==) (Case a) (Case b) = a == b
 (==) _ _ = False
 (/=) (Branch a) (Branch b) = a /= b
 (/=) (Case a) (Case b) = a /= b
 (/=) _ _ = True

data UseDef : Type where
   Use : List Elem -> Int -> UseDef
   Def : List Elem -> Int -> Maybe CairoConst -> UseDef

%prefix_record_projections off
record RegInfo where
    constructor MkRegInfo
    positions: List UseDef
    reg: CairoReg              --Is the original Register
    alloc: CairoReg            --Is the newly allocated Register

emptyRegInfo : CairoReg -> RegInfo
emptyRegInfo r = MkRegInfo [] r r

addUseDef: UseDef -> RegInfo -> RegInfo
addUseDef ud rg = { positions $= (ud::) } rg

mutual
    %prefix_record_projections off
    record RegTreeBlock where
        constructor MkRegTreeBlock
        depth : Int
        regs: List RegInfo
        cases: SortedMap Int RegTreeCase

    %prefix_record_projections off
    record RegTreeCase where
        constructor MkRegTreeCase
        depth : Int
        regs: List RegInfo
        blocks: SortedMap Int RegTreeBlock

commonPrefix : List Elem -> List Elem -> List Elem
commonPrefix _ Nil = Nil
commonPrefix Nil _ = Nil
commonPrefix (h1::tail1) (h2::tail2) = if h1 == h2 then h1::(commonPrefix tail1 tail2) else Nil

insertReg : RegTreeBlock -> RegInfo -> RegTreeBlock
insertReg root regInfo = insertIntoBlock (root.depth) pathRes (Just root)
 where
   computePrefix: Maybe (List Elem) -> UseDef -> Maybe (List Elem)
   computePrefix Nothing (Def path _ _) = Just path
   computePrefix Nothing (Use path _) = Just path
   computePrefix (Just pathAcc) (Def path _ _) = Just (commonPrefix path pathAcc)
   computePrefix (Just pathAcc) (Use path _) = Just (commonPrefix path pathAcc)
   pathRes: List Elem
   pathRes = fromMaybe [] (foldl computePrefix Nothing (regInfo.positions))
   mutual
       insertIntoBlock: Int -> List Elem -> Maybe RegTreeBlock -> RegTreeBlock
       insertIntoBlock _ Nil (Just block) = MkRegTreeBlock (block.depth) (regInfo::(block.regs)) (block.cases)
       insertIntoBlock depth Nil Nothing = MkRegTreeBlock depth [regInfo] empty
       insertIntoBlock depth ((Case i)::rest) (Just block) = MkRegTreeBlock (block.depth) (block.regs) (insert i (insertIntoCase depth rest (lookup i (block.cases))) (block.cases))
       insertIntoBlock depth ((Case i)::rest) Nothing = MkRegTreeBlock depth [] (singleton i (insertIntoCase depth rest Nothing))
       insertIntoBlock depth _ _ = MkRegTreeBlock depth [] empty -- should not happen


       insertIntoCase : Int -> List Elem -> Maybe RegTreeCase -> RegTreeCase
       insertIntoCase _ Nil (Just cases) = MkRegTreeCase (cases.depth) (regInfo::(cases.regs)) (cases.blocks)
       insertIntoCase depth Nil Nothing = MkRegTreeCase depth [regInfo] empty
       insertIntoCase depth ((Branch i)::rest) (Just cases) = MkRegTreeCase (cases.depth) (cases.regs) (insert i (insertIntoBlock (depth+1) rest (lookup i (cases.blocks))) (cases.blocks))
       insertIntoCase depth ((Branch i)::rest) Nothing = MkRegTreeCase depth [] (singleton i (insertIntoBlock (depth+1) rest Nothing))
       insertIntoCase depth _ _ = MkRegTreeCase depth [] empty -- should not happen


buildTree : SortedMap CairoReg RegInfo -> RegTreeBlock
buildTree regInfoMap = foldl insertReg (MkRegTreeBlock 0 [] empty) (values regInfoMap)

RegUseState : Type
RegUseState = (Int,Int,Int) -- currentApRegion, nextApRegion, nextCaseIndex

addRegDef : UseDef -> SortedMap CairoReg RegInfo -> CairoReg -> SortedMap CairoReg RegInfo
addRegDef ud apMap reg = insert reg (includeUseDef (lookup reg apMap)) apMap
    where
     includeUseDef : Maybe RegInfo -> RegInfo
     includeUseDef Nothing = MkRegInfo [ud] reg reg
     includeUseDef (Just oldInfo) = addUseDef ud oldInfo


addResRegDef : List Elem -> Int -> Maybe CairoConst -> CairoReg -> SortedMap CairoReg RegInfo -> SortedMap CairoReg RegInfo
addResRegDef path apRegion const reg apMap = addRegDef (Def path apRegion const) apMap reg

addResRegDefs : List Elem -> Int -> List CairoReg -> SortedMap CairoReg RegInfo -> SortedMap CairoReg RegInfo
addResRegDefs path apRegion regs apMap = foldl addRegDefAcc apMap regs
 where
  addRegDefAcc : SortedMap CairoReg RegInfo -> CairoReg -> SortedMap CairoReg RegInfo
  addRegDefAcc acc reg = addResRegDef path apRegion Nothing reg acc


addRegUse : List Elem -> Int -> CairoReg -> SortedMap CairoReg RegInfo -> SortedMap CairoReg RegInfo
addRegUse path apRegion reg apMap = insert reg (includeUseDef (lookup reg apMap)) apMap
    where
     ud : UseDef
     ud = Use path apRegion
     includeUseDef : Maybe RegInfo -> RegInfo
     includeUseDef Nothing = MkRegInfo [ud] reg reg
     includeUseDef (Just oldInfo) = addUseDef ud oldInfo

addRegUses : List Elem -> Int -> List CairoReg -> SortedMap CairoReg RegInfo -> SortedMap CairoReg RegInfo
addRegUses path apRegion regs apMap = foldl addRegUseAcc apMap regs
 where
  addRegUseAcc : SortedMap CairoReg RegInfo -> CairoReg -> SortedMap CairoReg RegInfo
  addRegUseAcc acc reg = addRegUse path apRegion reg acc


collectCairoInstRegUseBefore : List Elem -> Int -> SortedMap CairoReg RegInfo -> CairoInst -> SortedMap CairoReg RegInfo
collectCairoInstRegUseBefore path apRegion apMap (ASSIGN _ from) = addRegUse (reverse path) apRegion from apMap
collectCairoInstRegUseBefore path apRegion apMap (MKCON _ _ args) = addRegUses (reverse path) apRegion args apMap
collectCairoInstRegUseBefore path apRegion apMap (MKCLOSURE _ _ _ args) = addRegUses (reverse path) apRegion args apMap
collectCairoInstRegUseBefore path apRegion apMap (APPLY _ impls clo arg) = addRegUses (reverse path) apRegion (clo::arg::(map fst (values impls))) apMap
collectCairoInstRegUseBefore path apRegion apMap (MKCONSTANT _ _ ) = apMap
collectCairoInstRegUseBefore path apRegion apMap (CALL _ impls _ args) = addRegUses (reverse path) apRegion (args ++ (map fst (values impls))) apMap
collectCairoInstRegUseBefore path apRegion apMap (OP _ impls _ args) = addRegUses (reverse path) apRegion (args ++ (map fst (values impls))) apMap
collectCairoInstRegUseBefore path apRegion apMap (EXTPRIM _ impls _ args) = addRegUses (reverse path) apRegion (args ++ (map fst (values impls))) apMap
collectCairoInstRegUseBefore path apRegion apMap (CASE from _ _) = addRegUse (reverse path) apRegion from apMap
collectCairoInstRegUseBefore path apRegion apMap (CONSTCASE from _ _) = addRegUse (reverse path) apRegion from apMap
collectCairoInstRegUseBefore path apRegion apMap (RETURN froms impls) = addRegUses (reverse path) apRegion (froms ++ (values impls)) apMap
collectCairoInstRegUseBefore path apRegion apMap (PROJECT _ from _) = addRegUse (reverse path) apRegion from apMap
collectCairoInstRegUseBefore path apRegion apMap (STARKNETINTRINSIC _ impls _ args) = addRegUses (reverse path) apRegion (args ++ (map fst (values impls))) apMap
collectCairoInstRegUseBefore path apRegion apMap (NULL _) = apMap
collectCairoInstRegUseBefore path apRegion apMap (ERROR _ _) = apMap

collectCairoInstRegUseAfter : List Elem -> Int -> SortedMap CairoReg RegInfo -> CairoInst -> SortedMap CairoReg RegInfo
collectCairoInstRegUseAfter path apRegion apMap (ASSIGN to _) = addResRegDef (reverse path) apRegion Nothing to apMap
collectCairoInstRegUseAfter path apRegion apMap (MKCON to _ _) = addResRegDef (reverse path) apRegion Nothing to apMap
collectCairoInstRegUseAfter path apRegion apMap (MKCLOSURE to _ _ _) = addResRegDef (reverse path) apRegion Nothing to apMap
collectCairoInstRegUseAfter path apRegion apMap (APPLY to impls _ _) = addResRegDefs (reverse path) apRegion (to::(map snd (values impls))) apMap
collectCairoInstRegUseAfter path apRegion apMap (MKCONSTANT to c ) = addResRegDef (reverse path) apRegion (Just c) to apMap
collectCairoInstRegUseAfter path apRegion apMap (CALL tos impls _ _) = addResRegDefs (reverse path) apRegion (tos ++ (map snd (values impls))) apMap
collectCairoInstRegUseAfter path apRegion apMap (OP to impls _ _) = addResRegDefs (reverse path) apRegion (to::(map snd (values impls))) apMap
collectCairoInstRegUseAfter path apRegion apMap (EXTPRIM tos impls _ _) = addResRegDefs (reverse path) apRegion (tos ++ (map snd (values impls))) apMap
collectCairoInstRegUseAfter path apRegion apMap (STARKNETINTRINSIC to impls _ _) = addResRegDefs (reverse path) apRegion (to::(map snd (values impls))) apMap
collectCairoInstRegUseAfter path apRegion apMap (CASE _ _ _) = apMap
collectCairoInstRegUseAfter path apRegion apMap (CONSTCASE _ _ _) = apMap
collectCairoInstRegUseAfter path apRegion apMap (RETURN _ _) = apMap
collectCairoInstRegUseAfter path apRegion apMap (PROJECT to _ _) = addResRegDef (reverse path) apRegion Nothing to apMap
collectCairoInstRegUseAfter path apRegion apMap (NULL to) = addResRegDef (reverse path) apRegion Nothing to apMap
collectCairoInstRegUseAfter path apRegion apMap (ERROR to _) = addResRegDef (reverse path) apRegion Nothing to apMap

intrinsicApStable : StarkNetIntrinsic -> Bool
-- Todo: Check that Cairo really produce ap stable
intrinsicApStable (StorageVarAddr _) = True
intrinsicApStable (EventSelector _) = True

isCairoInstApModStatic : SortedSet Name -> CairoInst -> Bool
isCairoInstApModStatic _ (APPLY _ _ _ _) = False -- An apply can result in an arbitrary ap mod, so this is undef
isCairoInstApModStatic safeCalls (CALL _ _ n _) = contains n safeCalls
isCairoInstApModStatic _ (EXTPRIM _ _ name _) = externalApStable name
isCairoInstApModStatic _ (STARKNETINTRINSIC _ _ i _) = intrinsicApStable i
isCairoInstApModStatic _ (OP _ _ fn _) = primFnApStable fn
isCairoInstApModStatic _ (CASE _ _ _) = False
isCairoInstApModStatic _ (CONSTCASE _ _ _) = False
isCairoInstApModStatic _ (ERROR _ _ ) = False
isCairoInstApModStatic _ _ = True

mutual
    collectCairoInstRegUseCase : SortedSet Name -> List Elem -> (SortedMap CairoReg RegInfo, RegUseState) -> CairoInst -> List (List CairoInst) -> (SortedMap CairoReg RegInfo, RegUseState)
    collectCairoInstRegUseCase safeCalls path (apMap, (curApRegion, nextApRegion, nextCase)) inst cases = (after, (afterApRegion, afterApRegion+1, nextCase+1))
             where
               before : SortedMap CairoReg RegInfo
               before = collectCairoInstRegUseBefore path curApRegion apMap inst

               branchExtractHelper : Int -> (SortedMap CairoReg RegInfo, RegUseState) -> (SortedMap CairoReg RegInfo, (Int,Int))
               branchExtractHelper nextBr (apMap,(_, next, _)) = (apMap, (next,nextBr))

               newPath : List Elem
               newPath = (Case nextCase)::path

               applyBranch : (SortedMap CairoReg RegInfo, (Int,Int)) -> List CairoInst -> (SortedMap CairoReg RegInfo, (Int,Int))
               applyBranch (state, (nextApRegion, br)) insts = branchExtractHelper (br+1) (collectCairoInstRegUses safeCalls (Branch br::newPath) (state, (curApRegion, nextApRegion, 0)) insts)

               inside : (SortedMap CairoReg RegInfo, (Int,Int))
               inside = foldl applyBranch (before,(nextApRegion,0)) cases

               afterApRegion : Int
               afterApRegion = fst (snd inside)

               after : SortedMap CairoReg RegInfo
               after = collectCairoInstRegUseAfter path afterApRegion (fst inside) inst

    collectCairoInstRegUse : SortedSet Name -> List Elem -> (SortedMap CairoReg RegInfo, RegUseState) -> CairoInst -> (SortedMap CairoReg RegInfo, RegUseState)
    collectCairoInstRegUse safeCalls path state (CASE from alts Nothing) = collectCairoInstRegUseCase safeCalls path state (CASE from alts Nothing) (map snd alts)
    collectCairoInstRegUse safeCalls path state (CASE from alts (Just def)) =  collectCairoInstRegUseCase safeCalls path state (CASE from alts (Just def)) (def::(map snd alts))
    collectCairoInstRegUse safeCalls path state (CONSTCASE from alts Nothing) =  collectCairoInstRegUseCase safeCalls path state (CONSTCASE from alts Nothing) (map snd alts)
    collectCairoInstRegUse safeCalls path state (CONSTCASE from alts (Just def)) =  collectCairoInstRegUseCase safeCalls path state (CONSTCASE from alts (Just def)) (def::(map snd alts))
    collectCairoInstRegUse safeCalls path (apMap, (curApRegion, nextApRegion, nextCase)) inst = process (isCairoInstApModStatic safeCalls inst)
     where
       before : SortedMap CairoReg RegInfo
       before = collectCairoInstRegUseBefore path curApRegion apMap inst

       applyAfter : Int -> SortedMap CairoReg RegInfo -> SortedMap CairoReg RegInfo
       applyAfter region curApMap = collectCairoInstRegUseAfter path region curApMap inst

       process : Bool -> (SortedMap CairoReg RegInfo, RegUseState)
       process False = (applyAfter nextApRegion before, (nextApRegion, nextApRegion+1, nextCase))
       process True = (applyAfter curApRegion before, (curApRegion, nextApRegion, nextCase))

    collectCairoInstRegUses: SortedSet Name -> List Elem -> (SortedMap CairoReg RegInfo, RegUseState) -> List CairoInst -> (SortedMap CairoReg RegInfo, RegUseState)
    collectCairoInstRegUses safeCalls path state insts = foldl (collectCairoInstRegUse safeCalls path) state insts

collectRegUse : SortedSet Name -> List CairoReg -> List CairoInst -> (SortedMap CairoReg RegInfo, Bool)
collectRegUse safeCalls args insts = (fst collectionRes, hasSingleApRegion)
    where
     mapEntry : CairoReg -> (CairoReg, RegInfo)
     mapEntry reg = (reg, MkRegInfo [Def [] 0 Nothing] reg reg)

     initial : List CairoReg -> SortedMap CairoReg RegInfo
     initial args = fromList (map mapEntry args)

     initialApRegion: Int
     initialApRegion = 0

     collectionRes : (SortedMap CairoReg RegInfo, RegUseState)
     collectionRes = collectCairoInstRegUses safeCalls [] (initial args,(initialApRegion,initialApRegion+1,0)) insts

     hasSingleApRegion : Bool
     hasSingleApRegion = (fst (snd collectionRes)) == initialApRegion

SelectionState : Type
SelectionState = (SortedMap CairoReg CairoReg,(Int, Int))

assignRegs : SelectionState -> Int -> List RegInfo -> SelectionState
assignRegs state depth regs = foldl assignReg state regs
    where
     decideTempType : Maybe CairoConst -> Bool -> Int -> CairoReg
     decideTempType (Just v) _ _ = Const v
     decideTempType Nothing False index = Temp index depth
     decideTempType Nothing True index = Let index depth

     extractUsePath : UseDef -> List (List Elem)
     extractUsePath (Use p _) = [p]
     extractUsePath (Def _ _ _) = []

     isCase : Maybe Elem -> Bool
     isCase Nothing = False               -- share the root, so in same branch
     isCase (Just (Branch _)) = False     -- share a branch
     isCase (Just (Case _)) = True        -- share a case but not a branch

     checkPrefixCase : List Elem -> List (List Elem) -> Bool
     checkPrefixCase _ Nil = True
     checkPrefixCase p1 (p2::tail) = isCase (last' (commonPrefix p1 p2))

     distinctBranch : List (List Elem) -> Bool
     distinctBranch Nil = True
     distinctBranch (p::tail) = (checkPrefixCase p tail) && (distinctBranch tail)

     isSingleUse : List UseDef -> Bool
     isSingleUse uds = distinctBranch (uds >>= extractUsePath)

     extractConstant : UseDef -> List CairoConst
     extractConstant (Use _ _) = Nil
     extractConstant (Def _ _ Nothing) = Nil
     extractConstant (Def _ _ (Just s)) = [s]

     uniqueElem : List CairoConst -> Maybe CairoConst
     uniqueElem [v] = Just v
     uniqueElem _ = Nothing

     extractSingleConstant : List UseDef -> Maybe CairoConst
     extractSingleConstant uds = uniqueElem (toList (SortedSet.fromList (uds >>= extractConstant)))

     doRegAlloc : Maybe Int -> SelectionState -> RegInfo -> SelectionState
     doRegAlloc (Just regio) (mapping, (nextLocal, nextTemp)) (MkRegInfo ud r _) = (insert r (decideTempType (extractSingleConstant ud) (isSingleUse ud) nextTemp) mapping, (nextLocal,nextTemp+1))  -- is temp/let/const assignable
     doRegAlloc Nothing (mapping, (nextLocal, nextTemp)) (MkRegInfo ud r _) = (insert r (Local nextLocal depth) mapping, (nextLocal+1,nextTemp))                                                 -- must be local assigned

     mergeApRegions : Int -> Maybe Int -> Maybe Int
     mergeApRegions _ Nothing = Nothing
     mergeApRegions newRegion (Just oldRegion) = if newRegion == oldRegion then Just oldRegion else Nothing

     detectApRegion : List UseDef -> Maybe Int
     detectApRegion Nil = Nothing                                                           -- should never happen
     detectApRegion ((Use _ apRegion)::Nil) = Just apRegion
     detectApRegion ((Def _ apRegion _)::Nil) = Just apRegion
     detectApRegion ((Use _ apRegion)::tail) = mergeApRegions apRegion (detectApRegion tail)
     detectApRegion ((Def _ apRegion _)::tail) = mergeApRegions apRegion (detectApRegion tail)

     assignReg : SelectionState -> RegInfo -> SelectionState
     assignReg state assig@(MkRegInfo locs r (Unassigned _ _ _)) = doRegAlloc (detectApRegion locs) state assig
     assignReg (mapping, counters) (MkRegInfo _ r res) = (insert r res mapping, counters) --Already ia allocated skip


mutual
    assignBlockRegs : SelectionState -> RegTreeBlock -> SelectionState
    assignBlockRegs state block = assignNestedRegs
        where
         assignBlockLocatedRegs : SelectionState
         assignBlockLocatedRegs = assignRegs state (block.depth) (block.regs)

         assignNestedRegs : SelectionState
         assignNestedRegs = foldl assignCaseRegs assignBlockLocatedRegs (values block.cases)

    assignCaseRegs : SelectionState -> RegTreeCase -> SelectionState
    assignCaseRegs state cases = mergeResults (assignNestedBranchesRegs assignCaseLocatedRegs)
        where
         assignCaseLocatedRegs : SelectionState
         assignCaseLocatedRegs = assignRegs state (cases.depth) (cases.regs)

         assignNestedBranchesRegs : SelectionState -> List SelectionState
         assignNestedBranchesRegs (_, counters) = map (assignBlockRegs (empty, counters)) (values cases.blocks)

         mergeStates : SelectionState -> SelectionState -> SelectionState
         mergeStates (mapping1, (nextLocal1, nextTemp1)) (mapping2, (nextLocal2, nextTemp2)) = (mergeLeft mapping1 mapping2, (max nextLocal1 nextLocal2, max nextTemp1 nextTemp2))

         mergeResults : List SelectionState -> SelectionState
         mergeResults branchResults = foldl mergeStates (fst assignCaseLocatedRegs, (0,0)) branchResults

allocateRegisters : SortedSet Name -> (Name, CairoDef) -> List CairoReg -> List CairoInst -> (CairoDef, SortedSet Name)
allocateRegisters safeCalls def@(n, _) args body= (updatedDef, updatedSafeCalls)
    where collectedRegs : (SortedMap CairoReg RegInfo, Bool)
          collectedRegs = collectRegUse safeCalls args body
          builtTree : RegTreeBlock
          builtTree = buildTree (fst collectedRegs)
          assignedRegs : SelectionState
          assignedRegs = assignBlockRegs (empty,(0,0)) builtTree
          updatedDef : CairoDef
          updatedDef = snd $ substituteDefRegisters (\reg => lookup reg (fst assignedRegs)) def
          updatedSafeCalls : SortedSet Name
          updatedSafeCalls = if (snd collectedRegs) then (insert n safeCalls) else safeCalls

public export
allocateCairoDefRegisters : SortedSet Name -> (Name, CairoDef) -> (CairoDef, SortedSet Name)
allocateCairoDefRegisters safeCalls def@(n, FunDef args _ _ body) = allocateRegisters safeCalls def args body
allocateCairoDefRegisters safeCalls def@(n, ExtFunDef _ args _ _ body) = allocateRegisters safeCalls def args body
allocateCairoDefRegisters safeCalls def@(n, ForeignDef info _ _) = if isApStable info
    then (snd def, insert n safeCalls)
    else (snd def, safeCalls)
