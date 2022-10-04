module Idris.Transpiler

import CairoCode.CairoCode
import CairoCode.Name
import Core.Name.Namespace
import Core.Context
import Compiler.Common
import Core.CompileExpr
import Compiler.ANF
import Data.List
import Data.List1
import Data.String
import Data.Vect
import Data.Either
import Data.SortedMap
import Data.SortedSet
import CommonDef
import ABI.Definitions
import Idris.Naming

resolveIndex : SortedMap Int CairoReg -> Int -> CairoReg
resolveIndex subs i = fromMaybe (assert_total $ idris_crash "No Cairo Register bound for ANF Local") (lookup i subs)

resolveReg : SortedMap Int CairoReg -> AVar -> CairoReg
resolveReg subs (ALocal i) = resolveIndex subs i
resolveReg _ ANull = Eliminated Null

-- When generating instructions, this defines where the last instruction of a block should store its result.
data Result : Type where
  -- Currently evaluating a whole function          -> The value will be returned
  Return : Result
  -- Currently evaluation a block inside a function -> Assign to a register instead of returning
  Assign : CairoReg -> Result

produceResult : (Int,Int) -> Result -> (CairoReg -> CairoInst) -> (Int, List CairoInst)
produceResult (nextReg, _) (Assign c) f = (nextReg, [f c])
produceResult (nextReg, depth) Return f = (nextReg+1, [f c, RETURN [c] empty])
    where c : CairoReg
          c = Unassigned (Just "return") nextReg depth

projectArgs : CairoReg -> Nat -> (fields : List CairoReg) -> List CairoInst
projectArgs src i [] = []
projectArgs src i (field :: fields) = (PROJECT field src i)::(projectArgs src (i + 1) fields)

fromANFPrimType : PrimType -> CairoConst
fromANFPrimType StringType = StringType
fromANFPrimType CharType = CharType
fromANFPrimType IntType = IntType
fromANFPrimType Int8Type = Int8Type
fromANFPrimType Int16Type = Int16Type
fromANFPrimType Int32Type = Int32Type
fromANFPrimType Int64Type = Int64Type
fromANFPrimType IntegerType = IntegerType
fromANFPrimType Bits8Type = Bits8Type
fromANFPrimType Bits16Type = Bits16Type
fromANFPrimType Bits32Type = Bits32Type
fromANFPrimType Bits64Type = Bits64Type
fromANFPrimType _ = assert_total $ idris_crash "Unsupported PrimType"

-- Convert constants. Doubles, DoubleType and WorldType are not supported.
fromANFConst : Constant -> CairoConst
fromANFConst (I a) = I a
fromANFConst (I8 a) = I8 a
fromANFConst (I16 a) = I16 a
fromANFConst (I32 a) = I32 a
fromANFConst (I64 a) = I64 a
fromANFConst (BI a) = BI a
fromANFConst (B8 a) = B8 a
fromANFConst (B16 a) = B16 a
fromANFConst (B32 a) = B32 a
fromANFConst (B64 a) = B64 a
fromANFConst (Str a) = Str a
fromANFConst (Ch a) = Ch a
-- Sadly this one appears in MainExpr so we need to translate or throw main expr & co. out early
fromANFConst WorldVal = Str "WorldVal"
fromANFConst (PrT prt) = fromANFPrimType prt
fromANFConst _ = assert_total $ idris_crash "Unsupported Constant type"

-- Convert ANF Primitive function/operator, dropping the arity information.

%hide Core.Context.Context.Constructor.arity
-- TODO take FC for more precise error reporting
fromANFPrimFn : PrimFn arity -> Core CairoPrimFn
fromANFPrimFn (Add a) = pure (Add $ fromANFPrimType a)
fromANFPrimFn (Sub a) = pure (Sub $ fromANFPrimType a)
fromANFPrimFn (Mul a) = pure (Mul $ fromANFPrimType a)
fromANFPrimFn (Div a) = pure (Div $ fromANFPrimType a)
fromANFPrimFn (Mod a) = pure (Mod $ fromANFPrimType a)
fromANFPrimFn (Neg a) = pure (Neg $ fromANFPrimType a)
fromANFPrimFn (ShiftL a) = pure (ShiftL $ fromANFPrimType a)
fromANFPrimFn (ShiftR a) = pure (ShiftR $ fromANFPrimType a)
fromANFPrimFn (BAnd a) = pure (BAnd $ fromANFPrimType a)
fromANFPrimFn (BOr a) = pure (BOr $ fromANFPrimType a)
fromANFPrimFn (BXOr a) = pure (BXOr $ fromANFPrimType a)
fromANFPrimFn (LT a) = pure (LT $ fromANFPrimType a)
fromANFPrimFn (LTE a) = pure (LTE $ fromANFPrimType a)
fromANFPrimFn (EQ a) = pure (EQ $ fromANFPrimType a)
fromANFPrimFn (GTE a) = pure (GTE $ fromANFPrimType a)
fromANFPrimFn (GT a) = pure (GT $ fromANFPrimType a)
fromANFPrimFn (Cast a b) = pure (Cast (fromANFPrimType a) (fromANFPrimType b))
fromANFPrimFn (BelieveMe) = pure BelieveMe
fromANFPrimFn (Crash) = pure Crash
fromANFPrimFn f = throw (UserError ("PrimFn " ++ show f ++ " is not supported"))


-- splitLast '_' "abc_efg_hij" = Just ("abc_efg", "hij")
-- splitLast '_' "abc_efg_hij" = Just ("abc_efg", "hij")
splitLast : Char -> String -> Maybe (String, String)
splitLast sep string =
  case break (== sep) (reverse string) of
    (suffix, pref) =>
      case strM pref of
        (StrNil) => Nothing
        (StrCons _ rest) => Just (reverse rest, reverse suffix)


-- %extern definitions, used in the Cairo stdlib for casts and operations on Felt elements.
fromANFExtPrim : Name -> CairoReg -> List CairoReg -> CairoInst
fromANFExtPrim n res args = let name = fromIdrisName n in
  case extractNamespace name of
    ["Common","Casts"] =>
      case extractName name of
        "prim__cast_Felt_to_Felt" => OP res empty (Cast FeltType FeltType) args
        "prim__cast_Int_to_Felt" => OP res empty (Cast IntType FeltType) args
        "prim__cast_Int8_to_Felt" => OP res empty (Cast Int8Type FeltType) args
        "prim__cast_Int16_to_Felt" => OP res empty (Cast Int16Type FeltType) args
        "prim__cast_Int32_to_Felt" => OP res empty (Cast Int32Type FeltType) args
        "prim__cast_Int64_to_Felt" => OP res empty (Cast Int64Type FeltType) args
        "prim__cast_Integer_to_Felt" => OP res empty (Cast IntegerType FeltType) args
        "prim__cast_Bits8_to_Felt" => OP res empty (Cast Bits8Type FeltType) args
        "prim__cast_Bits16_to_Felt" => OP res empty (Cast Bits16Type FeltType) args
        "prim__cast_Bits32_to_Felt" => OP res empty (Cast Bits32Type FeltType) args
        "prim__cast_Bits64_to_Felt" => OP res empty (Cast Bits64Type FeltType) args

        "prim__cast_Felt_to_Int" => OP res empty (Cast FeltType IntType) args
        "prim__cast_Int_to_Int" => OP res empty (Cast IntType IntType) args
        "prim__cast_Int8_to_Int" => OP res empty (Cast Int8Type IntType) args
        "prim__cast_Int16_to_Int" => OP res empty (Cast Int16Type IntType) args
        "prim__cast_Int32_to_Int" => OP res empty (Cast Int32Type IntType) args
        "prim__cast_Int64_to_Int" => OP res empty (Cast Int64Type IntType) args
        "prim__cast_Integer_to_Int" => OP res empty (Cast IntegerType IntType) args
        "prim__cast_Bits8_to_Int" => OP res empty (Cast Bits8Type IntType) args
        "prim__cast_Bits16_to_Int" => OP res empty (Cast Bits16Type IntType) args
        "prim__cast_Bits32_to_Int" => OP res empty (Cast Bits32Type IntType) args
        "prim__cast_Bits64_to_Int" => OP res empty (Cast Bits64Type IntType) args

        "prim__cast_Felt_to_Int8" => OP res empty (Cast FeltType Int8Type) args
        "prim__cast_Int_to_Int8" => OP res empty (Cast IntType Int8Type) args
        "prim__cast_Int8_to_Int8" => OP res empty (Cast Int8Type Int8Type) args
        "prim__cast_Int16_to_Int8" => OP res empty (Cast Int16Type Int8Type) args
        "prim__cast_Int32_to_Int8" => OP res empty (Cast Int32Type Int8Type) args
        "prim__cast_Int64_to_Int8" => OP res empty (Cast Int64Type Int8Type) args
        "prim__cast_Integer_to_Int8" => OP res empty (Cast IntegerType Int8Type) args
        "prim__cast_Bits8_to_Int8" => OP res empty (Cast Bits8Type Int8Type) args
        "prim__cast_Bits16_to_Int8" => OP res empty (Cast Bits16Type Int8Type) args
        "prim__cast_Bits32_to_Int8" => OP res empty (Cast Bits32Type Int8Type) args
        "prim__cast_Bits64_to_Int8" => OP res empty (Cast Bits64Type Int8Type) args

        "prim__cast_Felt_to_Int16" => OP res empty (Cast FeltType Int16Type) args
        "prim__cast_Int_to_Int16" => OP res empty (Cast IntType Int16Type) args
        "prim__cast_Int8_to_Int16" => OP res empty (Cast Int8Type Int16Type) args
        "prim__cast_Int16_to_Int16" => OP res empty (Cast Int16Type Int16Type) args
        "prim__cast_Int32_to_Int16" => OP res empty (Cast Int32Type Int16Type) args
        "prim__cast_Int64_to_Int16" => OP res empty (Cast Int64Type Int16Type) args
        "prim__cast_Integer_to_Int16" => OP res empty (Cast IntegerType Int16Type) args
        "prim__cast_Bits8_to_Int16" => OP res empty (Cast Bits8Type Int16Type) args
        "prim__cast_Bits16_to_Int16" => OP res empty (Cast Bits16Type Int16Type) args
        "prim__cast_Bits32_to_Int16" => OP res empty (Cast Bits32Type Int16Type) args
        "prim__cast_Bits64_to_Int16" => OP res empty (Cast Bits64Type Int16Type) args

        "prim__cast_Felt_to_Int32" => OP res empty (Cast FeltType Int32Type) args
        "prim__cast_Int_to_Int32" => OP res empty (Cast IntType Int32Type) args
        "prim__cast_Int8_to_Int32" => OP res empty (Cast Int8Type Int32Type) args
        "prim__cast_Int16_to_Int32" => OP res empty (Cast Int16Type Int32Type) args
        "prim__cast_Int32_to_Int32" => OP res empty (Cast Int32Type Int32Type) args
        "prim__cast_Int64_to_Int32" => OP res empty (Cast Int64Type Int32Type) args
        "prim__cast_Integer_to_Int32" => OP res empty (Cast IntegerType Int32Type) args
        "prim__cast_Bits8_to_Int32" => OP res empty (Cast Bits8Type Int32Type) args
        "prim__cast_Bits16_to_Int32" => OP res empty (Cast Bits16Type Int32Type) args
        "prim__cast_Bits32_to_Int32" => OP res empty (Cast Bits32Type Int32Type) args
        "prim__cast_Bits64_to_Int32" => OP res empty (Cast Bits64Type Int32Type) args

        "prim__cast_Felt_to_Int64" => OP res empty (Cast FeltType Int64Type) args
        "prim__cast_Int_to_Int64" => OP res empty (Cast IntType Int64Type) args
        "prim__cast_Int8_to_Int64" => OP res empty (Cast Int8Type Int64Type) args
        "prim__cast_Int16_to_Int64" => OP res empty (Cast Int16Type Int64Type) args
        "prim__cast_Int32_to_Int64" => OP res empty (Cast Int32Type Int64Type) args
        "prim__cast_Int64_to_Int64" => OP res empty (Cast Int64Type Int64Type) args
        "prim__cast_Integer_to_Int64" => OP res empty (Cast IntegerType Int64Type) args
        "prim__cast_Bits8_to_Int64" => OP res empty (Cast Bits8Type Int64Type) args
        "prim__cast_Bits16_to_Int64" => OP res empty (Cast Bits16Type Int64Type) args
        "prim__cast_Bits32_to_Int64" => OP res empty (Cast Bits32Type Int64Type) args
        "prim__cast_Bits64_to_Int64" => OP res empty (Cast Bits64Type Int64Type) args

        "prim__cast_Felt_to_Integer" => OP res empty (Cast FeltType IntegerType) args
        "prim__cast_Int_to_Integer" => OP res empty (Cast IntType IntegerType) args
        "prim__cast_Int8_to_Integer" => OP res empty (Cast Int8Type IntegerType) args
        "prim__cast_Int16_to_Integer" => OP res empty (Cast Int16Type IntegerType) args
        "prim__cast_Int32_to_Integer" => OP res empty (Cast Int32Type IntegerType) args
        "prim__cast_Int64_to_Integer" => OP res empty (Cast Int64Type IntegerType) args
        "prim__cast_Integer_to_Integer" => OP res empty (Cast IntegerType IntegerType) args
        "prim__cast_Bits8_to_Integer" => OP res empty (Cast Bits8Type IntegerType) args
        "prim__cast_Bits16_to_Integer" => OP res empty (Cast Bits16Type IntegerType) args
        "prim__cast_Bits32_to_Integer" => OP res empty (Cast Bits32Type IntegerType) args
        "prim__cast_Bits64_to_Integer" => OP res empty (Cast Bits64Type IntegerType) args

        "prim__cast_Felt_to_Bits8" => OP res empty (Cast FeltType Bits8Type) args
        "prim__cast_Int_to_Bits8" => OP res empty (Cast IntType Bits8Type) args
        "prim__cast_Int8_to_Bits8" => OP res empty (Cast Int8Type Bits8Type) args
        "prim__cast_Int16_to_Bits8" => OP res empty (Cast Int16Type Bits8Type) args
        "prim__cast_Int32_to_Bits8" => OP res empty (Cast Int32Type Bits8Type) args
        "prim__cast_Int64_to_Bits8" => OP res empty (Cast Int64Type Bits8Type) args
        "prim__cast_Integer_to_Bits8" => OP res empty (Cast IntegerType Bits8Type) args
        "prim__cast_Bits8_to_Bits8" => OP res empty (Cast Bits8Type Bits8Type) args
        "prim__cast_Bits16_to_Bits8" => OP res empty (Cast Bits16Type Bits8Type) args
        "prim__cast_Bits32_to_Bits8" => OP res empty (Cast Bits32Type Bits8Type) args
        "prim__cast_Bits64_to_Bits8" => OP res empty (Cast Bits64Type Bits8Type) args

        "prim__cast_Felt_to_Bits16" => OP res empty (Cast FeltType Bits16Type) args
        "prim__cast_Int_to_Bits16" => OP res empty (Cast IntType Bits16Type) args
        "prim__cast_Int8_to_Bits16" => OP res empty (Cast Int8Type Bits16Type) args
        "prim__cast_Int16_to_Bits16" => OP res empty (Cast Int16Type Bits16Type) args
        "prim__cast_Int32_to_Bits16" => OP res empty (Cast Int32Type Bits16Type) args
        "prim__cast_Int64_to_Bits16" => OP res empty (Cast Int64Type Bits16Type) args
        "prim__cast_Integer_to_Bits16" => OP res empty (Cast IntegerType Bits16Type) args
        "prim__cast_Bits8_to_Bits16" => OP res empty (Cast Bits8Type Bits16Type) args
        "prim__cast_Bits16_to_Bits16" => OP res empty (Cast Bits16Type Bits16Type) args
        "prim__cast_Bits32_to_Bits16" => OP res empty (Cast Bits32Type Bits16Type) args
        "prim__cast_Bits64_to_Bits16" => OP res empty (Cast Bits64Type Bits16Type) args

        "prim__cast_Felt_to_Bits32" => OP res empty (Cast FeltType Bits32Type) args
        "prim__cast_Int_to_Bits32" => OP res empty (Cast IntType Bits32Type) args
        "prim__cast_Int8_to_Bits32" => OP res empty (Cast Int8Type Bits32Type) args
        "prim__cast_Int16_to_Bits32" => OP res empty (Cast Int16Type Bits32Type) args
        "prim__cast_Int32_to_Bits32" => OP res empty (Cast Int32Type Bits32Type) args
        "prim__cast_Int64_to_Bits32" => OP res empty (Cast Int64Type Bits32Type) args
        "prim__cast_Integer_to_Bits32" => OP res empty (Cast IntegerType Bits32Type) args
        "prim__cast_Bits8_to_Bits32" => OP res empty (Cast Bits8Type Bits32Type) args
        "prim__cast_Bits16_to_Bits32" => OP res empty (Cast Bits16Type Bits32Type) args
        "prim__cast_Bits32_to_Bits32" => OP res empty (Cast Bits32Type Bits32Type) args
        "prim__cast_Bits64_to_Bits32" => OP res empty (Cast Bits64Type Bits32Type) args

        "prim__cast_Felt_to_Bits64" => OP res empty (Cast FeltType Bits64Type) args
        "prim__cast_Int_to_Bits64" => OP res empty (Cast IntType Bits64Type) args
        "prim__cast_Int8_to_Bits64" => OP res empty (Cast Int8Type Bits64Type) args
        "prim__cast_Int16_to_Bits64" => OP res empty (Cast Int16Type Bits64Type) args
        "prim__cast_Int32_to_Bits64" => OP res empty (Cast Int32Type Bits64Type) args
        "prim__cast_Int64_to_Bits64" => OP res empty (Cast Int64Type Bits64Type) args
        "prim__cast_Integer_to_Bits64" => OP res empty (Cast IntegerType Bits64Type) args
        "prim__cast_Bits8_to_Bits64" => OP res empty (Cast Bits8Type Bits64Type) args
        "prim__cast_Bits16_to_Bits64" => OP res empty (Cast Bits16Type Bits64Type) args
        "prim__cast_Bits32_to_Bits64" => OP res empty (Cast Bits32Type Bits64Type) args
        "prim__cast_Bits64_to_Bits64" => OP res empty (Cast Bits64Type Bits64Type) args

        name => assert_total $ idris_crash $ "Unsupported cast: " ++ name

    ["Common","Felt"] =>
      case extractName name of
        "prim__mk_Felt" => OP res empty (Cast IntegerType FeltType) args
        "prim__from_Felt" => OP res empty (Cast FeltType IntType) args
        "prim__eq_Felt" => OP res empty (EQ FeltType) args
        "prim__lt_Felt" => OP res empty (LT FeltType) args
        "prim__lte_Felt" => OP res empty (LTE FeltType) args
        "prim__gt_Felt" => OP res empty (GT FeltType) args
        "prim__gte_Felt" => OP res empty (GTE FeltType) args
        "prim__add_Felt" => OP res empty (Add FeltType) args
        "prim__mul_Felt" => OP res empty (Mul FeltType) args
        "prim__sub_Felt" => OP res empty (Sub FeltType) args
        "prim__div_Felt" => OP res empty (Div FeltType) args
        "prim__mod_Felt" => OP res empty (Mod FeltType) args
        "prim__neg_Felt" => OP res empty (Neg FeltType) args
        name => assert_total $ idris_crash $ "Unsupported felt operation: " ++ name

--    ["Common","NativeEncode"] =>
--       case extractName name of
--         -- Todo: Generate in abi a wrapper function named packed_read_ptr that does call cairoreadptr EXTPRIM and then MKCon to pack the results
--         "read" => CALL [res] empty (Extension "external" Nothing (fullName ["ABI", "Helper"] "packed_read_ptr")) args
--         "write" => EXTPRIM [res] empty (Extension "external" Nothing (fullName ["ABI", "Helper"] "cairowriteptr")) args
--         name => assert_total $ idris_crash $ "Unsupported segment operation: " ++ name
     -- todo: as soon as cairo supports namespaces for StorageVar & EventSelector we can update
    ns => case splitLast '_' (extractName name) of
      Just (name', "addr")  => 
        let storageVarName = noMangle $ fullName [] name'
         in STARKNETINTRINSIC res empty (StorageVarAddr storageVarName) []
      Just (name', "event") => 
        let eventName = noMangle $ fullName [] name'
         in STARKNETINTRINSIC res empty (EventSelector eventName) []
      Just (name', "selector") => 
        let selectorName = fullName ns name'
         in STARKNETINTRINSIC res empty (FunctionSelector selectorName) []
      Just (name', "encodeParams") => 
        let paramEncodeName = genAbstractFunctionParamEncoderName $ fullName ns name'
         in CALL [res] empty paramEncodeName args
      Just (name', "decodeResult") => 
        let resultDecoderName = genAbstractFunctionResultDecoderName $ fullName ns name'
         in CALL [res] empty resultDecoderName args
      _            => assert_total $ idris_crash $ "Unsupported ExtPrim operation: " ++ show ns ++ show name


-- Nothing in target means return
fromANFInst : (regInfo:(Int,Int)) -> SortedMap Int CairoReg -> (target : Result) -> ANF -> Core (Int, List CairoInst)
fromANFInst (nextReg,_) subs (Assign (Eliminated _)) _    = pure (nextReg, [])
fromANFInst regInfo subs res (AV _ reg)                   = pure (produceResult regInfo res (\r => ASSIGN r (resolveReg subs reg)))
fromANFInst regInfo subs res (AAppName _ _ name args)     = pure (produceResult regInfo res (\r => CALL [r] empty (fromIdrisName name) (map (resolveReg subs) args)))
fromANFInst regInfo subs res (AUnderApp _ name miss args) = pure (produceResult regInfo res (\r => MKCLOSURE r (fromIdrisName name) miss (map (resolveReg subs) args)))
fromANFInst regInfo subs res (AApp _ _ src arg)           = pure (produceResult regInfo res (\r => APPLY r empty (resolveReg subs src) (resolveReg subs arg)))
fromANFInst regInfo subs res (ACon _ n ci tag args)       = pure (produceResult regInfo res (\r => MKCON r tag (map (resolveReg subs) args)))
fromANFInst regInfo subs res (AOp _ _ fn args)
    = do cairoPrimFn <- fromANFPrimFn fn
         pure (produceResult regInfo res (\r => OP r empty cairoPrimFn (map (resolveReg subs) (toList args))))

fromANFInst regInfo subs res (AExtPrim _ _ name args) = pure (produceResult regInfo res (\r => fromANFExtPrim name r (map (resolveReg subs) args)))
fromANFInst regInfo subs res (APrimVal _ const)       = pure (produceResult regInfo res (\r => MKCONSTANT r (fromANFConst const)))
fromANFInst regInfo subs res (AErased _)              = pure (produceResult regInfo res (\r => NULL r))
fromANFInst regInfo subs res (ACrash _ err)           = pure (produceResult regInfo res (\r => ERROR r err))
fromANFInst (next,depth) subs res (ALet _ var val body)
    = do (next1, v) <- fromANFInst (next+1,depth) subs (Assign newReg) val
         (next2, b) <- fromANFInst (next1,depth) newSubs res body
         pure (next2, v ++ b)
    where newReg : CairoReg
          newReg = Unassigned Nothing next depth
          newSubs : SortedMap Int CairoReg
          newSubs = insert var newReg subs

-- exactly one alternative, so skip matching
-- Note: We simplified as our constant folder and dead code eliminator should get rid of unused PROJECTS
fromANFInst (next,depth) subs res (AConCase fc src [MkAConAlt n ci mt args code] Nothing)
    = do (next2, body) <- fromANFInst (fst nextRegAndSubs,depth) newSubs res code
         pure (next2, projects ++ body)
    where nextRegAndSubs : (Int, SortedMap Int CairoReg)
          nextRegAndSubs = foldl (\(n,s),i => (n+1, insert i (Unassigned Nothing n depth) s)) (next, subs) args
          newSubs : SortedMap Int CairoReg
          newSubs = snd nextRegAndSubs
          projects : List CairoInst
          projects = projectArgs (resolveReg subs src) 0 (map (resolveIndex newSubs) args)

fromANFInst regInfo subs res (AConCase _ ANull _ _) = pure (produceResult regInfo res (\r => NULL r))
fromANFInst (next,depth) subs res (AConCase fc src alts def)
    = do (next4, as) <- fromANFInstConAlts next alts
         res <- traverseOpt (fromANFInst (next4, depth+1) subs res) def
         let next5 = fromMaybe next4 (map fst res)
         let d = map snd res
         pure (next5, [CASE (resolveReg subs src) as d])
    where fromANFInstConAlts : Int -> List AConAlt -> Core (Int, List (Int, List CairoInst))
          fromANFInstConAlts next1 Nil = pure (next1, Nil)
          fromANFInstConAlts next1 ((MkAConAlt n _ tag args code)::rest)
            = do (next2, c) <- fromANFInst (fst nextRegAndSubs, depth+1) newSubs res code
                 (next3, brs) <- fromANFInstConAlts next2 rest
                 pure (next3, (fromMaybe 0 tag, projects ++ c)::brs)
            where nextRegAndSubs : (Int, SortedMap Int CairoReg)
                  nextRegAndSubs = foldl (\(n,s),i => (n+1, insert i (Unassigned Nothing n (depth+1)) s)) (next1, subs) args
                  newSubs : SortedMap Int CairoReg
                  newSubs = snd nextRegAndSubs
                  projects : List CairoInst
                  projects = projectArgs (resolveReg subs src) 0 (map (resolveIndex newSubs) args)

fromANFInst regInfo subs res (AConstCase _ ANull _ _) = pure (produceResult regInfo res (\r => NULL r))
fromANFInst (next,depth) subs res (AConstCase fc src alts def)
    = do (next4, as) <- fromANFInstConstAlts next alts
         res <- traverseOpt (fromANFInst (next4, depth+1) subs res) def
         let next5 = fromMaybe next4 (map fst res)
         let d = map snd res
         pure (next5, [CONSTCASE (resolveReg subs src) as d])
    where fromANFInstConstAlts : Int -> List AConstAlt -> Core (Int, List (CairoConst, List CairoInst))
          fromANFInstConstAlts next1 Nil = pure (next1, Nil)
          fromANFInstConstAlts next1 ((MkAConstAlt constant code)::rest)
            = do (next2, c) <- fromANFInst (next1, depth+1) subs res code
                 (next3, brs) <- fromANFInstConstAlts next2 rest
                 pure (next3, (fromANFConst constant, c)::brs)

fromANFInst regInfo subs res _ = pure (produceResult regInfo res (\r => NULL r))

---------------------------------
---- FFI Definitions Start ------
---------------------------------

dropStr : Int -> String -> String
dropStr n str = substr (cast n) (cast ((strLength str)- n)) str

trimEnds : Int -> String -> String
trimEnds n str = substr (cast n) (cast ((strLength str)- 2*n)) str

-- Parses an imports declaration. Example:
-- imports:a.b.c f, a.b.c g, x.y.z h
parseImports : List String -> SortedSet Import
parseImports input = fromMaybe empty (map parse (find (\s => isPrefixOf "imports:" s) input))
   where parseImport : String -> Import
         parseImport str = case split (== ' ') (trim str) of
                             (ns ::: (f :: Nil)) => MkImport ns f Nothing
                             (ns ::: (f :: (r :: Nil))) => MkImport ns f (Just r)
                             _                   => assert_total $ idris_crash ("can not parse \"" ++ str ++ "\"" )

         stripPrefix : String -> String
         stripPrefix = dropStr (strLength "imports:")

         splitImports : String -> List String
         splitImports = forget . (split (== ','))

         parse: String -> SortedSet Import
         parse = fromList . map parseImport . splitImports . stripPrefix


parseCode : List String -> String
parseCode input = fromMaybe (assert_total $ idris_crash "Externals must have a code definition") (map parse (find (\s => isPrefixOf "code:" s) input))
     where parse: String -> String
           parse str = dropStr (strLength "code:") str

parseLinearImplicits : List String -> List LinearImplicit
parseLinearImplicits input = fromMaybe [] (map parse (find (\s => isPrefixOf "linear_implicits:" s) input))
     where parse: String -> List LinearImplicit
           parse str = map (MKLinearImplicit . trim) (filter (\s => (strLength (trim s)) /= 0) (forget (split (== ',') (dropStr (strLength "linear_implicits:") str))))

parseUntupledSig : List String -> Maybe TupleStructure
parseUntupledSig input = fromMaybe Nothing (map parse (find (\s => isPrefixOf "untupled:" s) input))
     where innerParse : String -> TupleStructure
           innerParse str = if (isPrefixOf "(" str) && (isSuffixOf ")" str)
                -- todo: add support for data in addition to records by specifing tag
                then Tupled 0 $ map (\x => innerParse $ assert_smaller str $ trim x)
                              $ filter (\s => (strLength (trim s)) /= 0)
                              $ forget
                              $ split (== ',')
                              $ trimEnds 1 str
                else if str == "_"
                    then ReturnValue
                    else assert_total $ idris_crash (" can not parse " ++ str )
           parse : String -> Maybe TupleStructure
           parse str = Just $ innerParse $ trim (dropStr (strLength "untupled:") str)

parseIsApStable : List String -> Bool
parseIsApStable input = fromMaybe False (map parse (find (\s => isPrefixOf "apStable:" s) input))
    where innerParse : String -> Bool
          innerParse "True" = True
          innerParse "true" = True
          innerParse "False" = False
          innerParse "false" = False
          innerParse x = assert_total $ idris_crash (" can not parse " ++ x)
          parse: String -> Bool
          parse str = innerParse $ trim $ dropStr (strLength "apStable:") str

parseForeign : List String -> ForeignInfo
parseForeign defs = MkForeignInfo (parseIsApStable cleanInput) (parseUntupledSig cleanInput) (parseLinearImplicits cleanInput) (parseImports cleanInput) (parseCode cleanInput)
    where cleanInput : List String
          cleanInput = map trim defs

---------------------------------
----- FFI Definitions End -------
---------------------------------
export
fromANFDef : (Name, ANFDef) -> Core (List (CairoName, CairoDef))
fromANFDef (name, MkAFun args body)
    = do (_, cairoBody) <- fromANFInst (0, 0) subst Return body
         pure [(fromIdrisName name, FunDef argRegs empty [CustomReg "res" Nothing] cairoBody)]
    where numArgs : Int
          numArgs = cast (length args)
          argRegs : List CairoReg
          argRegs = map Param (fromZeroTo (numArgs-1))
          subst : SortedMap Int CairoReg
          subst = fromList (zip args argRegs)

fromANFDef (name, MkAForeign ccs cargs ret) = pure [(fromIdrisName name, ForeignDef (parseForeign ccs) (length cargs) 1)]
fromANFDef _ = pure Nil
