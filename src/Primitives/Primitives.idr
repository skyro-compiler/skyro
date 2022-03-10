module Primitives.Primitives

import Core.Context
import CairoCode.CairoCode
import Data.SortedSet
import Data.SortedMap
import Primitives.Common
import Primitives.Felt
import Primitives.UInt
import Primitives.Int
import Primitives.BigInt
import CairoCode.Traversal.Base
import Utils.Helpers
import CodeGen.CodeGenHelper
import Debug.Trace
import CommonDef

[no_op] PrimFn where
  eval [_] = Just $ ArgValue 0 
  eval _ = Nothing

  generateCode r [a] _ = Raw "\{ compileRegDecl r } = \{ compileReg a } # no_op\n"
  generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode no_op"

[believeme] PrimFn where
  eval [_,_,_] = Just $ ArgValue 2 -- Do nothing, trust that it works :)
  eval _ = Nothing

  generateCode r [_,_,a] _ = Raw "\{ compileRegDecl r } = \{ compileReg a } # believeme\n"
  generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode believeme"

-- Todo: extract error message if static
[crash] PrimFn where
  eval [_,_] = Just $ Failure "Crash"
  eval _ = Nothing

  generateCode r [_,_] _ = Instructions [ERROR r "Crash"]
  generateCode _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode crash"


associate : (rec:PrimFn) => (f:(PrimFn -> a)) -> a
associate fun = fun rec

-- Dispatch
dispatch : CairoPrimFn -> ((PrimFn => a) -> a)
dispatch (Add t) = case t of
  IntType => associate @{add_int}
  Int8Type => associate @{add_int8}
  Int16Type => associate @{add_int16}
  Int32Type => associate @{add_int32}
  Int64Type => associate @{add_int64}
  FeltType => associate @{add_felt}
  IntegerType => associate @{add_integer}
  Bits8Type => associate @{add_uint8}
  Bits16Type => associate @{add_uint16}
  Bits32Type => associate @{add_uint32}
  Bits64Type => associate @{add_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for add: " ++ show t

dispatch (Sub t) = case t of
  IntType => associate @{sub_int}
  Int8Type => associate @{sub_int8}
  Int16Type => associate @{sub_int16}
  Int32Type => associate @{sub_int32}
  Int64Type => associate @{sub_int64}
  FeltType => associate @{sub_felt}
  IntegerType => associate @{sub_integer}
  Bits8Type => associate @{sub_uint8}
  Bits16Type => associate @{sub_uint16}
  Bits32Type => associate @{sub_uint32}
  Bits64Type => associate @{sub_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for sub: " ++ show t

dispatch (Mul t) = case t of
  IntType => associate @{mul_int}
  Int8Type => associate @{mul_int8}
  Int16Type => associate @{mul_int16}
  Int32Type => associate @{mul_int32}
  Int64Type => associate @{mul_int64}
  FeltType => associate @{mul_felt}
  IntegerType => associate @{mul_integer}
  Bits8Type => associate @{mul_uint8}
  Bits16Type => associate @{mul_uint16}
  Bits32Type => associate @{mul_uint32}
  Bits64Type => associate @{mul_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for mul: " ++ show t

dispatch (Div t) = case t of
  IntType => associate @{div_int}
  Int8Type => associate @{div_int8}
  Int16Type => associate @{div_int16}
  Int32Type => associate @{div_int32}
  Int64Type => associate @{div_int64}
  FeltType => associate @{div_felt}
  IntegerType => associate @{div_integer}
  Bits8Type => associate @{div_uint8}
  Bits16Type => associate @{div_uint16}
  Bits32Type => associate @{div_uint32}
  Bits64Type => associate @{div_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for mul: " ++ show t

dispatch (Mod t) = case t of
  IntType => associate @{mod_int}
  Int8Type => associate @{mod_int8}
  Int16Type => associate @{mod_int16}
  Int32Type => associate @{mod_int32}
  Int64Type => associate @{mod_int64}
  -- FeltType => associate @{mod_felt} -- NOT supported
  IntegerType => associate @{mod_integer}
  Bits8Type => associate @{mod_uint8}
  Bits16Type => associate @{mod_uint16}
  Bits32Type => associate @{mod_uint32}
  Bits64Type => associate @{mod_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for mod: " ++ show t

dispatch (Neg t) = case t of
  IntType => associate @{neg_int}
  Int8Type => associate @{neg_int8}
  Int16Type => associate @{neg_int16}
  Int32Type => associate @{neg_int32}
  Int64Type => associate @{neg_int64}
  FeltType => associate @{neg_felt}
  IntegerType => associate @{neg_integer}
  Bits8Type => associate @{neg_uint8}
  Bits16Type => associate @{neg_uint16}
  Bits32Type => associate @{neg_uint32}
  Bits64Type => associate @{neg_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for neg: " ++ show t

dispatch (ShiftL t) = case t of
  IntType => associate @{shl_int}
  Int8Type => associate @{shl_int8}
  Int16Type => associate @{shl_int16}
  Int32Type => associate @{shl_int32}
  Int64Type => associate @{shl_int64}
  -- FeltType => associate @{shl_felt}
  -- IntegerType => associate @{shl_integer}
  Bits8Type => associate @{shl_uint8}
  Bits16Type => associate @{shl_uint16}
  Bits32Type => associate @{shl_uint32}
  Bits64Type => associate @{shl_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for shiftl: " ++ show t

dispatch (ShiftR t) = case t of
  IntType => associate @{shr_int}
  Int8Type => associate @{shr_int8}
  Int16Type => associate @{shr_int16}
  Int32Type => associate @{shr_int32}
  Int64Type => associate @{shr_int64}
  -- FeltType => associate @{shr_felt}
  -- IntegerType => associate @{shr_integer}
  Bits8Type => associate @{shr_uint8}
  Bits16Type => associate @{shr_uint16}
  Bits32Type => associate @{shr_uint32}
  Bits64Type => associate @{shr_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for shiftr: " ++ show t

dispatch (BAnd t) = case t of
  IntType => associate @{and_int}
  Int8Type => associate @{and_int8}
  Int16Type => associate @{and_int16}
  Int32Type => associate @{and_int32}
  Int64Type => associate @{and_int64}
  -- FeltType => associate @{and_felt}
  -- IntegerType => associate @{and_integer}
  Bits8Type => associate @{and_uint8}
  Bits16Type => associate @{and_uint16}
  Bits32Type => associate @{and_uint32}
  Bits64Type => associate @{and_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for band: " ++ show t

dispatch (BOr t) = case t of
  IntType => associate @{or_int}
  Int8Type => associate @{or_int8}
  Int16Type => associate @{or_int16}
  Int32Type => associate @{or_int32}
  Int64Type => associate @{or_int64}
  -- FeltType => associate @{or_felt}
  -- IntegerType => associate @{or_integer}
  Bits8Type => associate @{or_uint8}
  Bits16Type => associate @{or_uint16}
  Bits32Type => associate @{or_uint32}
  Bits64Type => associate @{or_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for bor: " ++ show t

dispatch (BXOr t) = case t of
  IntType => associate @{xor_int}
  Int8Type => associate @{xor_int8}
  Int16Type => associate @{xor_int16}
  Int32Type => associate @{xor_int32}
  Int64Type => associate @{xor_int64}
  -- FeltType => associate @{xor_felt}
  -- IntegerType => associate @{xor_integer}
  Bits8Type => associate @{xor_uint8}
  Bits16Type => associate @{xor_uint16}
  Bits32Type => associate @{xor_uint32}
  Bits64Type => associate @{xor_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for bxor: " ++ show t

dispatch (LT t) = case t of
  IntType => associate @{lt_int}
  Int8Type => associate @{lt_int8}
  Int16Type => associate @{lt_int16}
  Int32Type => associate @{lt_int32}
  Int64Type => associate @{lt_int64}
  -- FeltType => associate @{lt_felt}
  -- IntegerType => associate @{lt_integer}
  Bits8Type => associate @{lt_uint8}
  Bits16Type => associate @{lt_uint16}
  Bits32Type => associate @{lt_uint32}
  Bits64Type => associate @{lt_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for lt: " ++ show t

dispatch (LTE t) = case t of
  IntType => associate @{lte_int}
  Int8Type => associate @{lte_int8}
  Int16Type => associate @{lte_int16}
  Int32Type => associate @{lte_int32}
  Int64Type => associate @{lte_int64}
  -- FeltType => associate @{lte_felt}
  -- IntegerType => associate @{lte_integer}
  Bits8Type => associate @{lte_uint8}
  Bits16Type => associate @{lte_uint16}
  Bits32Type => associate @{lte_uint32}
  Bits64Type => associate @{lte_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for lte: " ++ show t

dispatch (EQ t) = case t of
  IntType => associate @{eq_int}
  Int8Type => associate @{eq_int8}
  Int16Type => associate @{eq_int16}
  Int32Type => associate @{eq_int32}
  Int64Type => associate @{eq_int64}
  FeltType => associate @{eq_felt}
  -- IntegerType => associate @{eq_integer}
  Bits8Type => associate @{eq_uint8}
  Bits16Type => associate @{eq_uint16}
  Bits32Type => associate @{eq_uint32}
  Bits64Type => associate @{eq_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for eq: " ++ show t

dispatch (GTE t) = case t of
  IntType => associate @{gte_int}
  Int8Type => associate @{gte_int8}
  Int16Type => associate @{gte_int16}
  Int32Type => associate @{gte_int32}
  Int64Type => associate @{gte_int64}
  -- FeltType => associate @{gte_felt}
  -- IntegerType => associate @{gte_integer}
  Bits8Type => associate @{gte_uint8}
  Bits16Type => associate @{gte_uint16}
  Bits32Type => associate @{gte_uint32}
  Bits64Type => associate @{gte_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for gte: " ++ show t  

dispatch (GT t) = case t of
  IntType => associate @{gt_int}
  Int8Type => associate @{gt_int8}
  Int16Type => associate @{gt_int16}
  Int32Type => associate @{gt_int32}
  Int64Type => associate @{gt_int64}
  -- FeltType => associate @{gt_felt}
  -- IntegerType => associate @{gt_integer}
  Bits8Type => associate @{gt_uint8}
  Bits16Type => associate @{gt_uint16}
  Bits32Type => associate @{gt_uint32}
  Bits64Type => associate @{gt_uint64}
  _ => assert_total $ idris_crash $ "Type not supported for gt: " ++ show t  

dispatch (Cast IntegerType IntType) = associate @{cast_integer_to_int}
dispatch (Cast _ IntType) = associate @{cast_to_int}

-- Casts to Int8
dispatch (Cast t Int8Type) = case t of
  IntegerType => associate @{cast_integer_to_int8}
  Int8Type => associate @{no_op}
  _ => associate @{cast_to_int8}

-- Casts to Int16
dispatch (Cast t Int16Type) = case t of
  IntegerType => associate @{cast_integer_to_int16}
  Bits8Type => associate @{no_op}
  Int8Type => associate @{no_op}
  Int16Type =>  associate @{no_op}
  _ => associate @{cast_to_int16}

-- Casts to Int32
dispatch (Cast t Int32Type) = case t of
  IntegerType => associate @{cast_integer_to_int32}
  Bits8Type => associate @{no_op}
  Int8Type => associate @{no_op}
  Bits16Type => associate @{no_op}
  Int16Type => associate @{no_op}
  Int32Type => associate @{no_op}
  _ => associate @{cast_to_int32}

-- Casts to Int64
dispatch (Cast t Int64Type) = case t of
  IntegerType => associate @{cast_integer_to_int64}
  Bits8Type => associate @{no_op}
  Int8Type => associate @{no_op}
  Bits16Type => associate @{no_op}
  Int16Type => associate @{no_op}
  Bits32Type => associate @{no_op}
  Int32Type => associate @{no_op}
  Int64Type => associate @{no_op}
  _ => associate @{cast_to_int64}

dispatch (Cast IntegerType FeltType) = associate @{cast_integer_to_felt}
dispatch (Cast _ FeltType) = associate @{cast_to_felt}

dispatch (Cast IntegerType IntegerType) = associate @{no_op}
dispatch (Cast _ IntegerType) = associate @{cast_to_integer}

-- Casts to Bits8
dispatch (Cast t Bits8Type) = case t of
  IntegerType => associate @{cast_integer_to_uint8}
  Bits8Type => associate @{no_op}
  _ => associate @{cast_to_uint8}

-- Casts to Bits16
dispatch (Cast t Bits16Type) = case t of
  IntegerType => associate @{cast_integer_to_uint16}
  Bits8Type => associate @{no_op}
  Bits16Type => associate @{no_op}
  _ => associate @{cast_to_uint16}

-- Casts to Bits32
dispatch (Cast t Bits32Type) = case t of
  IntegerType => associate @{cast_integer_to_uint32}
  Bits8Type => associate @{no_op}
  Bits16Type => associate @{no_op}
  Bits32Type => associate @{no_op}
  _  => associate @{cast_to_uint32}

-- Casts to Bits64
dispatch (Cast t Bits64Type) = case t of
  IntegerType => associate @{cast_integer_to_uint64}
  Bits8Type => associate @{no_op}
  Bits16Type => associate @{no_op}
  Bits32Type => associate @{no_op}
  Bits64Type => associate @{no_op}
  _  => associate @{cast_to_uint64}

dispatch (BelieveMe) = associate @{believeme}
dispatch (Crash) = associate @{crash}

dispatch op = assert_total $ idris_crash $ "Operation not supported: " ++ show op

export
evaluateConstantOp : CairoPrimFn -> List ValueInfo -> Maybe EvalRes
evaluateConstantOp fn args = dispatch fn eval args

export
primFnApStable : CairoPrimFn -> Bool
primFnApStable fn = dispatch fn apStable

export
primFnLinearImplicits : CairoPrimFn -> SortedSet LinearImplicit
primFnLinearImplicits fn = dispatch fn implicits

export
primFnImports : CairoPrimFn -> SortedSet Import
primFnImports fn = dispatch fn imports

export
primFnDependencies : CairoPrimFn -> SortedMap Name (Lazy CairoDef)
primFnDependencies fn = dispatch fn dependencies

export
primFnDependencyNames : CairoPrimFn -> SortedSet Name
primFnDependencyNames = keySet . primFnDependencies

export
generatePrimFnCode : CairoPrimFn -> (res:CairoReg) -> (args:List CairoReg) -> LinearImplicitArgs -> PrimFnCode
generatePrimFnCode fn = dispatch fn generateCode

export
findPrimFnDeps: List (Name, CairoDef) -> List (Name, CairoDef)
findPrimFnDeps defs = map (\(n,d) => (n,d)) $ SortedMap.toList allDeps
  where
    primFnCollector : InstVisit CairoReg -> SortedMap Name (Lazy CairoDef)
    primFnCollector (VisitOp _ _ primFn _) = primFnDependencies primFn
    primFnCollector _ = empty

    allDeps : SortedMap Name (Lazy CairoDef)
    allDeps = snd $ runVisitConcatCairoDefs @{dropDuplicateKeysMonoid} (pureTraversal primFnCollector) defs
