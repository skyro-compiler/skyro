module CairoCode.CairoCode

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

-- According to idris2 docs this should be in prelude but is not found
public export
thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare EQ ord = ord
thenCompare ord _ = ord

-- All the Constants
public export
data CairoConst : Type where
    I : Int -> CairoConst
    I8 : Int8 -> CairoConst
    I16 : Int16 -> CairoConst
    I32 : Int32 -> CairoConst
    I64 : Int64 -> CairoConst
    F : Integer -> CairoConst   -- F stands for Felt
    BI : Integer -> CairoConst
    B8 : Bits8 -> CairoConst
    B16 : Bits16 -> CairoConst
    B32 : Bits32 -> CairoConst
    B64 : Bits64 -> CairoConst
    Str : String -> CairoConst
    Ch : Char -> CairoConst
    IntType : CairoConst
    Int8Type : CairoConst
    Int16Type : CairoConst
    Int32Type : CairoConst
    Int64Type : CairoConst
    IntegerType : CairoConst
    FeltType : CairoConst   -- Note: Only for internal use / idris will use another FeltType representation
    Bits8Type : CairoConst
    Bits16Type : CairoConst
    Bits32Type : CairoConst
    Bits64Type : CairoConst
    StringType : CairoConst
    CharType : CairoConst

-- The level indicates how deeply nested (in case statements) the register is defined
--  the levels can mostly be ignored but are really helpful if we want to eliminate unecessary assignements
public export
data CairoReg : Type where
  Unassigned : Maybe String -> Int -> (level:Int) -> CairoReg   -- the unassigned level is dependent on the level of the let in the adt
  Param : Int -> CairoReg                                       -- params are always level 0
  NamedParam : String -> CairoReg
  Local : Int -> (level:Int) -> CairoReg
  Let : Int -> (level:Int) -> CairoReg
  Temp : Int -> (level:Int) -> CairoReg
  Const : CairoConst -> CairoReg                   -- constant values are always level 0
  Eliminated : CairoReg                         -- eliminated ones do not exist, no level needed


-- All the internal operators
public export
data CairoPrimFn : Type where
     Add : (ty : CairoConst) -> CairoPrimFn
     Sub : (ty : CairoConst) -> CairoPrimFn
     Mul : (ty : CairoConst) -> CairoPrimFn
     Div : (ty : CairoConst) -> CairoPrimFn
     Mod : (ty : CairoConst) -> CairoPrimFn
     Neg : (ty : CairoConst) -> CairoPrimFn
     ShiftL : (ty : CairoConst) -> CairoPrimFn
     ShiftR : (ty : CairoConst) -> CairoPrimFn

     BAnd : (ty : CairoConst) -> CairoPrimFn
     BOr : (ty : CairoConst) -> CairoPrimFn
     BXOr : (ty : CairoConst) -> CairoPrimFn

     LT  : (ty : CairoConst) -> CairoPrimFn
     LTE : (ty : CairoConst) -> CairoPrimFn
     EQ  : (ty : CairoConst) -> CairoPrimFn
     GTE : (ty : CairoConst) -> CairoPrimFn
     GT  : (ty : CairoConst) -> CairoPrimFn

     Cast : CairoConst -> CairoConst -> CairoPrimFn
     BelieveMe : CairoPrimFn
     Crash : CairoPrimFn

public export
data Import : Type where
  MkImport : String -> String -> Import

public export
Show Import where
  show (MkImport modulename function) = 
    "from " ++ modulename ++ " import " ++ function

public export
Eq Import where
  MkImport ns1 f1 == MkImport ns2 f2 = ns1 == ns2 && f1 == f2

public export
Ord Import where
  compare (MkImport ns1 f1) (MkImport ns2 f2) = 
    thenCompare (compare ns1 ns2) (compare f1 f2)

-- Short for: Value Independent Linear Implicit
-- Value Independent : An inst using a Linear Implicit must have a semantic independent of the concrete value of the implicit (as long as it is a valid one)
--   For example: the return of the pederson_hash function (which uses the pederson_ptr Linear Implicit) can be computed without knowing the value of the pederson_ptr
-- Linear : Every Linear Implicit must be used exactly once. Every inst using one must return a fresh and valid one that can be used by another inst
-- Implicit : The compiler injects the code that routes the implicits from one inst to the next
public export
data LinearImplicit : Type where
    MKLinearImplicit : String -> LinearImplicit

public export
LinearImplicitArgs : Type
LinearImplicitArgs = SortedMap LinearImplicit (CairoReg, CairoReg) -- (param, return)

public export
data CairoInst : Type where
     ASSIGN : (res:CairoReg) -> CairoReg -> CairoInst
     MKCON : (res:CairoReg) -> Maybe Int -> (args : List CairoReg) -> CairoInst
     MKCLOSURE : (res:CairoReg) -> Name -> (missing : Nat) -> (args : List CairoReg) -> CairoInst
     APPLY : (res:CairoReg) -> LinearImplicitArgs -> (f : CairoReg) -> (a : CairoReg) -> CairoInst
     MKCONSTANT : (res:CairoReg) -> CairoConst -> CairoInst
     CALL : (res:List CairoReg) -> LinearImplicitArgs -> Name -> (args : List CairoReg) -> CairoInst
     OP : (res:CairoReg) -> LinearImplicitArgs -> CairoPrimFn -> List CairoReg -> CairoInst
     EXTPRIM : List CairoReg -> LinearImplicitArgs -> Name -> List CairoReg -> CairoInst
     CASE : CairoReg -> (alts : List (Int, List CairoInst)) -> (def : Maybe (List CairoInst)) -> CairoInst
     CONSTCASE : CairoReg -> (alts : List (CairoConst, List CairoInst)) -> (def : Maybe (List CairoInst)) -> CairoInst
     PROJECT : (res:CairoReg) -> (value : CairoReg) -> (pos : Nat) -> CairoInst
     RETURN : List CairoReg -> SortedMap LinearImplicit CairoReg -> CairoInst
     NULL : (res:CairoReg) -> CairoInst
     ERROR : (res:CairoReg) -> String -> CairoInst

export
implicitName : LinearImplicit -> String
implicitName (MKLinearImplicit name) = name

export
implicitReg : LinearImplicit -> CairoReg
implicitReg impl = NamedParam (implicitName impl)

public export
Eq LinearImplicit where
  (==) (MKLinearImplicit s1) (MKLinearImplicit s2) = s1 == s2


export
output_builtin : LinearImplicit
output_builtin = MKLinearImplicit "output_ptr"

export
syscall_builtin : LinearImplicit
syscall_builtin = MKLinearImplicit "syscall_ptr"

export
pedersen_builtin : LinearImplicit
pedersen_builtin = MKLinearImplicit "pedersen_ptr"

export
range_check_builtin : LinearImplicit
range_check_builtin = MKLinearImplicit "range_check_ptr"

export 
ecdsa_builtin : LinearImplicit
ecdsa_builtin = MKLinearImplicit "ecdsa_ptr"

export
bitwise_builtin : LinearImplicit
bitwise_builtin = MKLinearImplicit "bitwise_ptr"

public export
Show LinearImplicit where
   show (MKLinearImplicit s) = "implicit{\{s}}"

public export
Ord LinearImplicit where
  compare a b = compare (linearImplicitOrder a) (linearImplicitOrder b)
    where 
      -- builtins must be ordered in a predefined order
      -- Otherwise: Error: The builtins specified by the %builtins directive must be subsequence of ['output', 'pedersen', 'range_check', 'ecdsa', 'bitwise']. Got ['bitwise', 'output', 'range_check'].
      linearImplicitOrder : LinearImplicit -> Int
      linearImplicitOrder (MKLinearImplicit "output_ptr") = 0
      linearImplicitOrder (MKLinearImplicit "syscall_ptr") = 1
      linearImplicitOrder (MKLinearImplicit "pedersen_ptr") = 2
      linearImplicitOrder (MKLinearImplicit "range_check_ptr") = 3
      linearImplicitOrder (MKLinearImplicit "ecdsa_ptr") = 4
      linearImplicitOrder (MKLinearImplicit "bitwise_ptr") = 5
      linearImplicitOrder i = assert_total $ idris_crash $ "Unknown implicit: " ++ show i

public export
data TupleStructure : Type where
 Tupled : (tag: Int) -> List TupleStructure -> TupleStructure
 ReturnValue : TupleStructure

public export
Show TupleStructure where
    show (Tupled t args) = "(" ++ (showSep ", " (assert_total (map show args)))++")"
    show ReturnValue = "_"

public export
Eq TupleStructure where
  (==) (Tupled t1 l1) (Tupled t2 l2) = t1 == t2 && assert_total (l1 == l2)
  (==) ReturnValue ReturnValue = True
  (==) _ _ = False

public export
record ForeignInfo where
    constructor MkForeignInfo
    isApStable: Bool
    untupledSig: Maybe TupleStructure
    implicits: List LinearImplicit
    imports: SortedSet Import
    code: String

public export
Eq ForeignInfo where
  (==) (MkForeignInfo a1 u1 i1 im1 c1) (MkForeignInfo a2 u2 i2 im2 c2) = a1 == a2 && u1 == u2 && i1 == i2 && im1 == im2 && c1 == c2

public export
data CairoDef : Type where
     FunDef : (params : List CairoReg) -> (implicits: SortedMap LinearImplicit CairoReg) -> (rets: List String) -> List CairoInst -> CairoDef
     ForeignDef : (info : ForeignInfo) -> (args:Nat) -> (rets:Nat) -> CairoDef

public export
CairoCodePass : Type
CairoCodePass = CompilationPass CairoDef

export
Show CairoConst where
  show (I a) = "Int_" ++ show a
  show (I8 a) = "Int8_" ++ show a
  show (I16 a) = "Int16_" ++ show a
  show (I32 a) = "Int32_" ++ show a
  show (I64 a) = "Int64_" ++ show a
  show (F a) = "Felt_" ++ show a
  show (BI a) = "Integer_" ++ show a
  show (B8 a) = "Bits8_" ++ show a
  show (B16 a) = "Bits16_" ++ show a
  show (B32 a) = "Bits32_" ++ show a
  show (B64 a) = "Bits64_" ++ show a
  show (Str a) = "Str_" ++ a
  show (Ch a) = "Ch_" ++ show a
  show IntType = "IntType"
  show Int8Type = "Int8Type"
  show Int16Type = "Int16Type"
  show Int32Type = "Int32Type"
  show Int64Type = "Int64Type"
  show FeltType = "FeltType"
  show IntegerType = "IntegerType"
  show Bits8Type = "Bits8Type"
  show Bits16Type = "Bits16Type"
  show Bits32Type = "Bits32Type"
  show Bits64Type = "Bits64Type"
  show StringType = "StringType"
  show CharType = "CharType"

export
Show CairoPrimFn where
  show (Add ty) = "+" ++ show ty
  show (Sub ty) = "-" ++ show ty
  show (Mul ty) = "*" ++ show ty
  show (Div ty) = "/" ++ show ty
  show (Mod ty) = "%" ++ show ty
  show (Neg ty) = "neg " ++ show ty
  show (ShiftL ty) = "shl " ++ show ty
  show (ShiftR ty) = "shr " ++ show ty
  show (BAnd ty) = "and " ++ show ty
  show (BOr ty) = "or " ++ show ty
  show (BXOr ty) = "xor " ++ show ty
  show (LT ty) = "<" ++ show ty
  show (LTE ty) = "<=" ++ show ty
  show (EQ ty) = "==" ++ show ty
  show (GTE ty) = ">=" ++ show ty
  show (GT ty) = ">" ++ show ty
  show (Cast x y) = "cast-" ++ show x ++ "-" ++ show y
  show BelieveMe = "believe_me"
  show Crash = "crash"
  
public export
Eq CairoConst where
    (==) (I a) (I b) = a == b
    (==) (I8 a) (I8 b) = a == b
    (==) (I16 a) (I16 b) = a == b
    (==) (I32 a) (I32 b) = a == b
    (==) (I64 a) (I64 b) = a == b
    (==) (F a) (F b) = a == b
    (==) (BI a) (BI b) = a == b
    (==) (B8 a) (B8 b) = a == b
    (==) (B16 a) (B16 b) = a == b
    (==) (B32 a) (B32 b) = a == b
    (==) (B64 a) (B64 b) = a == b
    (==) (Str a) (Str b) = a == b
    (==) (Ch a) (Ch b) = a == b
    (==) IntType IntType = True
    (==) Int8Type Int8Type = True
    (==) Int16Type Int16Type = True
    (==) Int32Type Int32Type = True
    (==) Int64Type Int64Type = True
    (==) IntegerType IntegerType = True
    (==) Bits8Type Bits8Type = True
    (==) Bits16Type Bits16Type = True
    (==) Bits32Type Bits32Type = True
    (==) Bits64Type Bits64Type = True
    (==) StringType StringType = True
    (==) CharType CharType = True
    (==) _ _ = False

public export
Eq CairoPrimFn where
  (==) (Add c1) (Add c2) = c1 == c2
  (==) (Sub c1) (Sub c2) = c1 == c2
  (==) (Mul c1) (Mul c2) = c1 == c2
  (==) (Div c1) (Div c2) = c1 == c2
  (==) (Mod c1) (Mod c2) = c1 == c2
  (==) (Neg c1) (Neg c2) = c1 == c2
  (==) (ShiftL c1) (ShiftL c2) = c1 == c2
  (==) (ShiftR c1) (ShiftR c2) = c1 == c2
  (==) (BAnd c1) (BAnd c2) = c1 == c2
  (==) (BOr c1) (BOr c2) = c1 == c2
  (==) (BXOr c1) (BXOr c2) = c1 == c2
  (==) (LT c1) (LT c2) = c1 == c2
  (==) (LTE c1) (LTE c2) = c1 == c2
  (==) (EQ c1) (EQ c2) = c1 == c2
  (==) (GTE c1) (GTE c2) = c1 == c2
  (==) (GT c1) (GT c2) = c1 == c2
  (==) (Cast c1 c1') (Cast c2 c2') = c1 == c2 && c1' == c2'
  (==) (BelieveMe) (BelieveMe) = True
  (==) (Crash) (Crash) = True
  (==) _ _ = False

public export
Ord CairoConst where
    compare (I a) (I b) = compare a b
    compare (I8 a) (I8 b) = compare a b
    compare (I16 a) (I16 b) = compare a b
    compare (I32 a) (I32 b) = compare a b
    compare (I64 a) (I64 b) = compare a b
    compare (F a) (F b) = compare a b
    compare (BI a) (BI b) = compare a b
    compare (B8 a) (B8 b) = compare a b
    compare (B16 a) (B16 b) = compare a b
    compare (B32 a) (B32 b) = compare a b
    compare (B64 a) (B64 b) = compare a b
    compare (Str a) (Str b) = compare a b
    compare (Ch a) (Ch b) = compare a b
    compare a b = compare (dataOrder a) (dataOrder b)
        where dataOrder : CairoConst -> Int
              dataOrder (I _) = 0
              dataOrder (I8 _) = 1
              dataOrder (I16 _) = 2
              dataOrder (I32 _) = 3
              dataOrder (I64 _) = 4
              dataOrder (F _) = 5
              dataOrder (BI _) = 6
              dataOrder (B8 _) = 7
              dataOrder (B16 _) = 8
              dataOrder (B32 _) = 9
              dataOrder (B64 _) = 10
              dataOrder (Str _) = 11
              dataOrder (Ch _) = 12
              dataOrder IntType = 13
              dataOrder Int8Type = 14
              dataOrder Int16Type = 15
              dataOrder Int32Type = 16
              dataOrder Int64Type = 17
              dataOrder FeltType = 18
              dataOrder IntegerType = 19
              dataOrder Bits8Type = 20
              dataOrder Bits16Type = 21
              dataOrder Bits32Type = 22
              dataOrder Bits64Type = 23
              dataOrder StringType = 24
              dataOrder CharType = 25


public export
Ord CairoPrimFn where
  compare (Add c1) (Add c2) = compare c1 c2
  compare (Sub c1) (Sub c2) = compare c1 c2
  compare (Mul c1) (Mul c2) = compare c1 c2
  compare (Div c1) (Div c2) = compare c1 c2
  compare (Mod c1) (Mod c2) = compare c1 c2
  compare (Neg c1) (Neg c2) = compare c1 c2
  compare (ShiftL c1) (ShiftL c2) = compare c1 c2
  compare (ShiftR c1) (ShiftR c2) = compare c1 c2
  compare (BAnd c1) (BAnd c2) = compare c1 c2
  compare (BOr c1) (BOr c2) = compare c1 c2
  compare (BXOr c1) (BXOr c2) = compare c1 c2
  compare (LT c1) (LT c2) = compare c1 c2
  compare (LTE c1) (LTE c2) = compare c1 c2
  compare (EQ c1) (EQ c2) = compare c1 c2
  compare (GTE c1) (GTE c2) = compare c1 c2
  compare (GT c1) (GT c2) = compare c1 c2
  compare (Cast c1 c1') (Cast c2 c2') = thenCompare (compare c1 c2) (compare c1' c2')
  compare a b = compare (dataOrder a) (dataOrder b)
        where dataOrder : CairoPrimFn -> Int
              dataOrder (Add _) = 0
              dataOrder (Sub _) = 1
              dataOrder (Mul _) = 2
              dataOrder (Div _) = 3
              dataOrder (Mod _) = 4
              dataOrder (Neg _) = 5
              dataOrder (ShiftL _) = 6
              dataOrder (ShiftR _) = 7
              dataOrder (BAnd _) = 8
              dataOrder (BOr _) = 9
              dataOrder (BXOr _) = 10
              dataOrder (LT _) = 11
              dataOrder (LTE _) = 12
              dataOrder (EQ _) = 13
              dataOrder (GTE _) = 14
              dataOrder (GT _) = 15
              dataOrder (Cast _ _) = 16
              dataOrder BelieveMe = 17
              dataOrder Crash = 18

public export
Eq CairoReg where
  (==) (Unassigned p1 i1 d1) (Unassigned p2 i2 d2) = p1 == p2 && i1 == i2 && d1 == d2
  (==) (Param i1) (Param i2) = i1 == i2
  (==) (NamedParam n1) (NamedParam n2) = n1 == n2
  (==) (Local i1 d1) (Local i2 d2) = d1 == d2 && i1 == i2
  (==) (Let i1 d1) (Let i2 d2) = d1 == d2 && i1 == i2
  (==) (Temp i1 d1) (Temp i2 d2) = d1 == d2 && i1 == i2
  (==) (Const s1) (Const s2) = s1 == s2
  (==) Eliminated Eliminated = True
  (==) _ _ = False

-- These with highest lifetime expectancy come first
dataOrder : CairoReg -> Int
dataOrder (Const _) = 0             -- Constants never become unreachable
dataOrder (NamedParam _) = 1        -- Params are reachable in the whole body
dataOrder (Param _) = 2             -- Params are reachable in the whole body
dataOrder (Local _ _) = 3           -- After assigned Locals are reachable in the whole body
dataOrder (Unassigned _ _ _) = 4    -- Unassigned have the potential to become Local or Const (but could be placed everywhere)
dataOrder (Temp _ _) = 5            -- Just reachable in the current AP region
dataOrder (Let _ _) = 6             -- Same as Temp. However, using multiple times is expensive
dataOrder Eliminated = 7            -- This is never reachable

-- These with highest lifetime expectancy come first
-- Note: StaticOptimizer relies on this order (to be most effective that is)
public export
Ord CairoReg where
  -- First handle the special cases without dept and index
  compare Eliminated Eliminated = EQ
  compare Eliminated _ = GT
  compare _ Eliminated = LT
  compare (Const c1) (Const c2) = compare c1 c2
  compare (Const _) _ = LT
  compare _ (Const _) = GT
  compare (NamedParam n1) (NamedParam n2) = compare n1 n2
  compare (NamedParam _) _ = LT
  compare _ (NamedParam _) = GT
  -- then handle the general case with depth and index
  compare a b = thenCompare
        (compare (depth a) (depth b))
        (thenCompare
            (compare (dataOrder a) (dataOrder b))
            (tiebreaker a b))
    where depth: CairoReg -> Int
          depth (Param _) = 0
          depth (Unassigned _ _ d) = d
          depth (Local _ d) = d
          depth (Temp _ d) = d
          depth (Let _ d) = d
          depth _ = -1
          -- Tie Breaker
          tiebreaker : CairoReg -> CairoReg -> Ordering
          tiebreaker (Param i1) (Param i2) = compare i1 i2
          tiebreaker (Unassigned s1 i1 _) (Unassigned s2 i2 _) = thenCompare (compare i1 i2) (compare s1 s2)
          tiebreaker (Local i1 _) (Local i2 _) = compare i1 i2
          tiebreaker (Temp i1 _) (Temp i2 _) = compare i1 i2
          tiebreaker (Let i1 _) (Let i2 _) = compare i1 i2
          tiebreaker _ _ = EQ -- just to please idris2

public export
Show CairoReg where
  show (Unassigned Nothing i d) = "Unassigned_" ++ show i ++ "(" ++ show d ++ ")"
  show (Unassigned (Just s) i d) = "Unassigned_" ++ s ++ "_" ++ show i ++ "(" ++ show d ++ ")"
  show (Param i) = "Param_" ++ show i
  show (NamedParam n) = n
  show (Local i d) = "Local_" ++ show i ++ "(" ++ show d ++ ")"
  show (Let i d) = "Let_" ++ show i ++ "(" ++ show d ++ ")"
  show (Temp i d) = "Temp_" ++ show i ++ "(" ++ show d ++ ")"
  show (Const s) = "Const_" ++ show s
  show Eliminated = "Eliminated"

public export
Eq CairoInst where
  (==) (ASSIGN r1 c1) (ASSIGN r2 c2) = r1 == r2 && c1 == c2
  (==) (MKCON r1 t1 a1) (MKCON r2 t2 a2) = r1 == r2 && t1 == t2 && a1 == a2
  (==) (MKCLOSURE r1 n1 m1 a1) (MKCLOSURE r2 n2 m2 a2) = r1 == r2 && n1 == n2 && m1 == m2 && a1 == a2
  (==) (APPLY r1 i1 f1 a1) (APPLY r2 i2 f2 a2) = r1 == r2 && i1 == i2 &&  f1 == f2 && a1 == a2
  (==) (MKCONSTANT r1 c1) (MKCONSTANT r2 c2) = r1 == r2 &&  c1 == c2
  (==) (CALL r1 i1 n1 a1) (CALL r2 i2 n2 a2) = r1 == r2 && i1 == i2 && n1 == n2 && a1 == a2
  (==) (OP r1 i1 f1 a1) (OP r2 i2 f2 a2) = r1 == r2 && i1 == i2 && (f1 == f2) && a1 == a2
  (==) (EXTPRIM r1 i1 n1 a1) (EXTPRIM r2 i2 n2 a2) = r1 == r2 && i1 == i2 &&  n1 == n2 && a1 == a2
  (==) (CASE r1 a1 dd1) (CASE r2 a2 dd2) = r1 == r2 && assert_total (a1 == a2) && assert_total (dd1 == dd2)
  (==) (CONSTCASE r1 a1 dd1) (CONSTCASE r2 a2 dd2) = r1 == r2 && assert_total (a1 == a2) && assert_total (dd1 == dd2)
  (==) (RETURN r1 i1) (RETURN r2 i2) = r1 == r2 && i1 == i2
  (==) (PROJECT r1 v1 p1) (PROJECT r2 v2 p2) = r1 == r2 &&  v1 == v2 && p1 == p2
  (==) (NULL r1) (NULL r2) = r1 == r2
  (==) (ERROR r1 m1) (ERROR r2 m2) = r1 == r2 && m1 == m2
  (==) _ _ = False


public export
Show CairoInst where
  show (ASSIGN r c) = "ASSIGN \{show r} \{show c}"
  show (MKCON r t a) = "MKCON \{show r} \{show t} \{show a}"
  show (MKCLOSURE r n m a) = "MKCLOSURE \{show r} \{show n} \{show m} \{show a}"
  show (APPLY r i f a) = "APPLY \{show r} \{show $ SortedMap.toList i} \{show f} \{show a}"
  show (MKCONSTANT r c) = "MKCONSTANT \{show r} \{show c}"
  show (CALL r i n a) = "CALL \{show r} \{show $ SortedMap.toList i} \{show n} \{show a}"
  show (OP r i f a) = "OP \{show r} \{show $ SortedMap.toList i} \{show f} \{show a}"
  show (EXTPRIM r i n a) = "EXTPRIM \{show r} \{show $ SortedMap.toList i} \{show n} \{show a}"
  show (CASE r a d) = assert_total "CASE \{show r} \{show a} \{show d}"
  show (CONSTCASE r a d) = assert_total "CONSTCASE \{show r} \{show a} \{show d}"
  show (RETURN r i) = "RETURN \{show r} [\{show $ SortedMap.toList i}]"
  show (PROJECT r v p) = "PROJECT \{show r} \{show v} \{show p}"
  show (NULL r) = "NULL \{show r}"
  show (ERROR r m) = "ERROR \{show r} \{show m}"

public export
Eq CairoDef where
  (==) (FunDef p1 i1 r1 b1) (FunDef p2 i2 r2 b2) = p1 == p2  && i1 == i2 && r1 == r2 && assert_total (b1 == b2)
  (==) (ForeignDef i1 a1 r1) (ForeignDef i2 a2 r2) = i1 == i2 && a1 == a2 && r1 == r2
  (==) _ _ = False

public export
Show CairoDef where
  show (FunDef p i r b) = "(\{showSep "," (map show p)}){\{showSep "," (map (\(i,r) => (show i) ++ "@" ++ (show r)) (SortedMap.toList i))}} -> (\{showSep "," r}){\n\{showSep "\n" (map show b)}\n}"
  show (ForeignDef _ _ _) = "Foreign" -- Todo:

resolveIndex : SortedMap Int CairoReg -> Int -> CairoReg
resolveIndex subs i = fromMaybe (assert_total $ idris_crash "No Cairo Register bound for ANF Local") (lookup i subs)

resolveReg : SortedMap Int CairoReg -> AVar -> CairoReg
resolveReg subs (ALocal i) = resolveIndex subs i
resolveReg _ ANull = Eliminated

data Result : Type where
   Return : Result
   Assign : CairoReg -> Result

produceResult : (Int,Int) -> Result -> (CairoReg -> CairoInst) -> (Int, List CairoInst)
produceResult (nextReg, _) (Assign c) f = (nextReg, [f c])
produceResult (nextReg, depth) Return f = (nextReg+1, [f c, RETURN [c] empty])
    where c : CairoReg
          c = Unassigned (Just "return") nextReg depth

projectArgs : CairoReg -> Nat -> (fields : List CairoReg) -> List CairoInst
projectArgs src i [] = []
projectArgs src i (field :: fields) = (PROJECT field src i)::(projectArgs src (i + 1) fields)

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
fromANFConst IntType = IntType
fromANFConst Int8Type = Int8Type
fromANFConst Int16Type = Int16Type
fromANFConst Int32Type = Int32Type
fromANFConst Int64Type = Int64Type
fromANFConst IntegerType = IntegerType
fromANFConst Bits8Type = Bits8Type
fromANFConst Bits16Type = Bits16Type
fromANFConst Bits32Type = Bits32Type
fromANFConst Bits64Type = Bits64Type
fromANFConst StringType = StringType
fromANFConst CharType = CharType
fromANFConst _ = assert_total $ idris_crash "Unsupported Constant type"

%hide Core.Context.Context.Constructor.arity
-- TODO take FC for more precise error reporting
fromANFPrimFn : PrimFn arity -> Core CairoPrimFn
fromANFPrimFn (Add a) = pure (Add $ fromANFConst a)
fromANFPrimFn (Sub a) = pure (Sub $ fromANFConst a)
fromANFPrimFn (Mul a) = pure (Mul $ fromANFConst a)
fromANFPrimFn (Div a) = pure (Div $ fromANFConst a)
fromANFPrimFn (Mod a) = pure (Mod $ fromANFConst a)
fromANFPrimFn (Neg a) = pure (Neg $ fromANFConst a)
fromANFPrimFn (ShiftL a) = pure (ShiftL $ fromANFConst a)
fromANFPrimFn (ShiftR a) = pure (ShiftR $ fromANFConst a)
fromANFPrimFn (BAnd a) = pure (BAnd $ fromANFConst a)
fromANFPrimFn (BOr a) = pure (BOr $ fromANFConst a)
fromANFPrimFn (BXOr a) = pure (BXOr $ fromANFConst a)
fromANFPrimFn (LT a) = pure (LT $ fromANFConst a)
fromANFPrimFn (LTE a) = pure (LTE $ fromANFConst a)
fromANFPrimFn (EQ a) = pure (EQ $ fromANFConst a)
fromANFPrimFn (GTE a) = pure (GTE $ fromANFConst a)
fromANFPrimFn (GT a) = pure (GT $ fromANFConst a)
fromANFPrimFn (Cast a b) = pure (Cast (fromANFConst a) (fromANFConst b))
fromANFPrimFn (BelieveMe) = pure BelieveMe
fromANFPrimFn (Crash) = pure Crash
fromANFPrimFn f = throw (UserError ("PrimFn " ++ show f ++ " is not supported"))

fromANFExtPrim : Name -> CairoReg -> List CairoReg -> CairoInst
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Felt")) res args = OP res empty (Cast IntType FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Felt")) res args = OP res empty (Cast Int8Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Felt")) res args = OP res empty (Cast Int16Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Felt")) res args = OP res empty (Cast Int32Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Felt")) res args = OP res empty (Cast Int64Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Felt")) res args = OP res empty (Cast Bits8Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Felt")) res args = OP res empty (Cast Bits16Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Felt")) res args = OP res empty (Cast Bits32Type FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Felt")) res args = OP res empty (Cast Bits64Type FeltType) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Int")) res args = OP res empty (Cast FeltType IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Int")) res args = OP res empty (Cast Int8Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Int")) res args = OP res empty (Cast Int16Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Int")) res args = OP res empty (Cast Int32Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Int")) res args = OP res empty (Cast Int64Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Int")) res args = OP res empty (Cast Bits8Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Int")) res args = OP res empty (Cast Bits16Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Int")) res args = OP res empty (Cast Bits32Type IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Int")) res args = OP res empty (Cast Bits64Type IntType) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Int8")) res args = OP res empty (Cast FeltType Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Int8")) res args = OP res empty (Cast IntType Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Int8")) res args = OP res empty (Cast Int16Type Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Int8")) res args = OP res empty (Cast Int32Type Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Int8")) res args = OP res empty (Cast Int64Type Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Int8")) res args = OP res empty (Cast Bits8Type Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Int8")) res args = OP res empty (Cast Bits16Type Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Int8")) res args = OP res empty (Cast Bits32Type Int8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Int8")) res args = OP res empty (Cast Bits64Type Int8Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Int16")) res args = OP res empty (Cast FeltType Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Int16")) res args = OP res empty (Cast IntType Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Int16")) res args = OP res empty (Cast Int8Type Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Int16")) res args = OP res empty (Cast Int32Type Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Int16")) res args = OP res empty (Cast Int64Type Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Int16")) res args = OP res empty (Cast Bits8Type Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Int16")) res args = OP res empty (Cast Bits16Type Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Int16")) res args = OP res empty (Cast Bits32Type Int16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Int16")) res args = OP res empty (Cast Bits64Type Int16Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Int32")) res args = OP res empty (Cast FeltType Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Int32")) res args = OP res empty (Cast IntType Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Int32")) res args = OP res empty (Cast Int8Type Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Int32")) res args = OP res empty (Cast Int16Type Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Int32")) res args = OP res empty (Cast Int64Type Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Int32")) res args = OP res empty (Cast Bits8Type Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Int32")) res args = OP res empty (Cast Bits16Type Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Int32")) res args = OP res empty (Cast Bits32Type Int32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Int32")) res args = OP res empty (Cast Bits64Type Int32Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Int64")) res args = OP res empty (Cast FeltType Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Int64")) res args = OP res empty (Cast IntType Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Int64")) res args = OP res empty (Cast Int8Type Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Int64")) res args = OP res empty (Cast Int16Type Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Int64")) res args = OP res empty (Cast Int32Type Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Int64")) res args = OP res empty (Cast Bits8Type Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Int64")) res args = OP res empty (Cast Bits16Type Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Int64")) res args = OP res empty (Cast Bits32Type Int64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Int64")) res args = OP res empty (Cast Bits64Type Int64Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Bits8")) res args = OP res empty (Cast FeltType Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Bits8")) res args = OP res empty (Cast IntType Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Bits8")) res args = OP res empty (Cast Int8Type Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Bits8")) res args = OP res empty (Cast Int16Type Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Bits8")) res args = OP res empty (Cast Int32Type Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Bits8")) res args = OP res empty (Cast Int64Type Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Bits8")) res args = OP res empty (Cast Bits16Type Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Bits8")) res args = OP res empty (Cast Bits32Type Bits8Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Bits8")) res args = OP res empty (Cast Bits64Type Bits8Type) args


fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Bits16")) res args = OP res empty (Cast FeltType Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Bits16")) res args = OP res empty (Cast IntType Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Bits16")) res args = OP res empty (Cast Int8Type Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Bits16")) res args = OP res empty (Cast Int16Type Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Bits16")) res args = OP res empty (Cast Int32Type Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Bits16")) res args = OP res empty (Cast Int64Type Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Bits16")) res args = OP res empty (Cast Bits8Type Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Bits16")) res args = OP res empty (Cast Bits32Type Bits16Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Bits16")) res args = OP res empty (Cast Bits64Type Bits16Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Bits32")) res args = OP res empty (Cast FeltType Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Bits32")) res args = OP res empty (Cast IntType Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Bits32")) res args = OP res empty (Cast Int8Type Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Bits32")) res args = OP res empty (Cast Int16Type Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Bits32")) res args = OP res empty (Cast Int32Type Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Bits32")) res args = OP res empty (Cast Int64Type Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Bits32")) res args = OP res empty (Cast Bits8Type Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Bits32")) res args = OP res empty (Cast Bits16Type Bits32Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits64_to_Bits32")) res args = OP res empty (Cast Bits64Type Bits32Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Felt_to_Bits64")) res args = OP res empty (Cast FeltType Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int_to_Bits64")) res args = OP res empty (Cast IntType Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int8_to_Bits64")) res args = OP res empty (Cast Int8Type Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int16_to_Bits64")) res args = OP res empty (Cast Int16Type Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int32_to_Bits64")) res args = OP res empty (Cast Int32Type Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Int64_to_Bits64")) res args = OP res empty (Cast Int64Type Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits8_to_Bits64")) res args = OP res empty (Cast Bits8Type Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits16_to_Bits64")) res args = OP res empty (Cast Bits16Type Bits64Type) args
fromANFExtPrim (NS _ (UN $ Basic "prim__cast_Bits32_to_Bits64")) res args = OP res empty (Cast Bits32Type Bits64Type) args

fromANFExtPrim (NS _ (UN $ Basic "prim__mk_Felt")) res args = OP res empty (Cast IntegerType FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__from_Felt")) res args = OP res empty (Cast FeltType IntType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__eq_Felt")) res args = OP res empty (EQ FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__add_Felt")) res args = OP res empty (Add FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__mul_Felt")) res args = OP res empty (Mul FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__sub_Felt")) res args = OP res empty (Sub FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__div_Felt")) res args = OP res empty (Div FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__mod_Felt")) res args = OP res empty (Mod FeltType) args
fromANFExtPrim (NS _ (UN $ Basic "prim__neg_Felt")) res args = OP res empty (Neg FeltType) args

fromANFExtPrim name res args = EXTPRIM [res] empty name args

-- Nothing in target means return
fromANFInst : (regInfo:(Int,Int)) -> SortedMap Int CairoReg -> (target : Result) -> ANF -> Core (Int, List CairoInst)
fromANFInst (nextReg,_) subs (Assign Eliminated) _ = pure (nextReg, [])
fromANFInst regInfo subs res (AV _ reg) = pure (produceResult regInfo res (\r => ASSIGN r (resolveReg subs reg)))
fromANFInst regInfo subs res (AAppName _ _ name args) = pure (produceResult regInfo res (\r => CALL [r] empty name (map (resolveReg subs) args)))
fromANFInst regInfo subs res (AUnderApp _ name miss args) = pure (produceResult regInfo res (\r => MKCLOSURE r name miss (map (resolveReg subs) args)))
fromANFInst regInfo subs res (AApp _ _ src arg) = pure (produceResult regInfo res (\r => APPLY r empty (resolveReg subs src) (resolveReg subs arg)))
fromANFInst regInfo subs res (ACon _ n ci tag args) = pure (produceResult regInfo res (\r => MKCON r tag (map (resolveReg subs) args)))
fromANFInst regInfo subs res (AOp _ _ fn args)
    = do cairoPrimFn <- fromANFPrimFn fn
         pure (produceResult regInfo res (\r => OP r empty cairoPrimFn (map (resolveReg subs) (toList args))))

fromANFInst regInfo subs res (AExtPrim _ _ name args) = pure (produceResult regInfo res (\r => fromANFExtPrim name r (map (resolveReg subs) args)))
fromANFInst regInfo subs res (APrimVal _ const) = pure (produceResult regInfo res (\r => MKCONSTANT r (fromANFConst const)))
fromANFInst regInfo subs res (AErased _) = pure (produceResult regInfo res (\r => NULL r))
fromANFInst regInfo subs res (ACrash _ err) = pure (produceResult regInfo res (\r => ERROR r err))
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
                  nextRegAndSubs = foldl (\(n,s),i => (n+1, insert i (Unassigned Nothing n depth) s)) (next1, subs) args
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
                             (ns ::: (f :: Nil)) => MkImport ns f
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
                then Tupled 0 (map (innerParse . trim) (filter (\s => (strLength (trim s)) /= 0) (forget (split (== ',') (trimEnds 1 str)))))
                else if str == "_"
                    then ReturnValue
                    else assert_total $ idris_crash (" can not parse " ++ str )
           parse: String -> Maybe TupleStructure
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

collectStrSize : (Name, ANFDef)

MkACon : (tag : Maybe Int) -> (arity : Nat) -> (nt : Maybe Nat) -> ANFDef

export
fromANFDef : (Name, ANFDef) -> Core (List (Name, CairoDef))
fromANFDef (name, MkAFun args body) 
    = do (_, cairoBody) <- fromANFInst (0, 0) subst Return body
         pure [(name, FunDef argRegs empty ["res"] cairoBody)]
    where numArgs : Int
          numArgs = cast (length args)
          argRegs : List CairoReg
          argRegs = map Param (fromZeroTo (numArgs-1))
          subst : SortedMap Int CairoReg
          subst = fromList (zip args argRegs)

fromANFDef (name, MkAForeign ccs cargs ret) = pure [(name, ForeignDef (parseForeign ccs) (length cargs) 1)]
fromANFDef _ = pure Nil
