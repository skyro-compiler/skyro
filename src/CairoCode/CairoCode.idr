module CairoCode.CairoCode

import CairoCode.Name
import Data.List
import Data.String
import Data.Either
import Data.SortedMap
import Data.SortedSet
import CommonDef
import Utils.Helpers

-- All the Constants
public export
data CairoConst : Type where
    I           : Int     -> CairoConst
    I8          : Int8    -> CairoConst
    I16         : Int16   -> CairoConst
    I32         : Int32   -> CairoConst
    I64         : Int64   -> CairoConst
    F           : Integer -> CairoConst  -- F stands for Felt
    BI          : Integer -> CairoConst  -- Big Integer
    B8          : Bits8   -> CairoConst  -- Unsigned
    B16         : Bits16  -> CairoConst
    B32         : Bits32  -> CairoConst
    B64         : Bits64  -> CairoConst
    Str         : String  -> CairoConst
    Ch          : Char    -> CairoConst
    IntType     : CairoConst
    Int8Type    : CairoConst
    Int16Type   : CairoConst
    Int32Type   : CairoConst
    Int64Type   : CairoConst
    FeltType    : CairoConst   -- Note: Only for internal use / idris will use another FeltType representation
    IntegerType : CairoConst
    Bits8Type   : CairoConst
    Bits16Type  : CairoConst
    Bits32Type  : CairoConst
    Bits64Type  : CairoConst
    StringType  : CairoConst
    CharType    : CairoConst
    TypeType    : CairoConst

export
typeOfConst : CairoConst -> CairoConst
typeOfConst (I   _) = IntType
typeOfConst (I8  _) = Int8Type
typeOfConst (I16 _) = Int16Type
typeOfConst (I32 _) = Int32Type
typeOfConst (I64 _) = Int64Type
typeOfConst (F   _) = FeltType
typeOfConst (BI  _) = IntegerType
typeOfConst (B8  _) = Bits8Type
typeOfConst (B16 _) = Bits16Type
typeOfConst (B32 _) = Bits32Type
typeOfConst (B64 _) = Bits64Type
typeOfConst (Str _) = StringType
typeOfConst (Ch  _) = CharType
typeOfConst _ = TypeType

mutual
  public export
  data ElimTracker : Type where
    Replacement : CairoReg -> ElimTracker
    Unreachable : ElimTracker
    Disjoint : ElimTracker
    Null : ElimTracker
    Other : String -> ElimTracker

  -- The level indicates how deeply nested (in case statements) the register is defined
  --  the levels can mostly be ignored but are really helpful if we want to eliminate unecessary assignements
  public export
  data CairoReg : Type where
    -- Maybe String for Name conflict resolutions, as a helper
    -- Not yet decided which Register type
    Unassigned  : Maybe String -> Int -> (level:Int) -> CairoReg  -- the unassigned level is dependent on the level of the let in the adt
    Param       : Int                                -> CairoReg  -- params are always level 0
    CustomReg   : String -> Maybe String             -> CairoReg  -- This should only be used in generated functions (and not in User defined functions)
    -- Locals are relative to [fp] and thus cannot be revoked.
    Local       : Int                 -> (level:Int) -> CairoReg
    -- Let works as a reference - the Cairo compiler replaces it with the appropriate, possibly differing, value at referenced positions.
    Let         : Int                 -> (level:Int) -> CairoReg
    -- Tempvars reserve a cell at [ap] for a value, and then define a let referencing it.
    Temp        : Int                 -> (level:Int) -> CairoReg
    Const       : CairoConst                         -> CairoReg  -- ^ constant values are always level 0
    Eliminated  : ElimTracker                        -> CairoReg  -- eliminated ones do not exist, no level needed, result in a value of 0?

  public export
  level : CairoReg -> Int
  level (Unassigned _ _ l) = l
  level (Param _) = 0
  level (CustomReg _ _) = 0
  level (Local _ l) = l
  level (Let _ l) = l
  level (Temp _ l) = l
  level (Const _ ) = 0
  level (Eliminated _ ) = 0

export
debugElimination : String -> CairoReg
debugElimination s = (Eliminated (Other s))

-- All the internal operators
public export
data CairoPrimFn : Type where
     -- The ty identifies the types at which this is applied
     Add    : (ty : CairoConst) -> CairoPrimFn
     Sub    : (ty : CairoConst) -> CairoPrimFn
     Mul    : (ty : CairoConst) -> CairoPrimFn
     Div    : (ty : CairoConst) -> CairoPrimFn
     Mod    : (ty : CairoConst) -> CairoPrimFn
     Neg    : (ty : CairoConst) -> CairoPrimFn
     ShiftL : (ty : CairoConst) -> CairoPrimFn
     ShiftR : (ty : CairoConst) -> CairoPrimFn

     BAnd : (ty : CairoConst) -> CairoPrimFn
     BOr  : (ty : CairoConst) -> CairoPrimFn
     BXOr : (ty : CairoConst) -> CairoPrimFn

     LT  : (ty : CairoConst) -> CairoPrimFn
     LTE : (ty : CairoConst) -> CairoPrimFn
     EQ  : (ty : CairoConst) -> CairoPrimFn
     GTE : (ty : CairoConst) -> CairoPrimFn
     GT  : (ty : CairoConst) -> CairoPrimFn

     Cast      : CairoConst -> CairoConst -> CairoPrimFn
     -- Unsafe cast operation
     BelieveMe :                             CairoPrimFn
     Crash     :                             CairoPrimFn

public export
data Import : Type where
  MkImport : (ns: String) -> (name: String) -> (as:Maybe String) -> Import

public export
Show Import where
  show (MkImport modulename function Nothing) =  "from " ++ modulename ++ " import " ++ function
  show (MkImport modulename function (Just rename)) =  "from " ++ modulename ++ " import " ++ function ++ " as "++ rename


public export
Eq Import where
  MkImport ns1 f1 r1== MkImport ns2 f2 r2 = ns1 == ns2 && f1 == f2 && r1 == r2

public export
Ord Import where
  compare (MkImport ns1 f1 r1) (MkImport ns2 f2 r2) =
    thenCompare (compare ns1 ns2) (thenCompare (compare f1 f2) (compare r1 r2))

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
data StarkNetIntrinsic = StorageVarAddr CairoName
                       | EventSelector CairoName
                       | FunctionSelector CairoName

public export
data CairoInst : Type where
    -- Assign from register to register
    ASSIGN     : (res : CairoReg)      -> CairoReg   -> CairoInst
    -- Assign a constant to a register
    MKCONSTANT : (res : CairoReg)      -> CairoConst -> CairoInst

    -- Execute the Operator
    OP : (res : CairoReg)      -> LinearImplicitArgs                         -> CairoPrimFn                    -> List CairoReg          -> CairoInst

    -- Represents a constructor call, not the definition, with the given tag and the arguments
    MKCON   : (res : CairoReg)      -> (tag:Maybe Int)                            -> (args : List CairoReg)                                   -> CairoInst
    -- Extract a value from a constructor `value` at position `pos` into `res`
    PROJECT : (res : CairoReg)      -> (value : CairoReg)                         -> (pos : Nat)                                              -> CairoInst

    -- Construct a closure for the given Name, with `missing` args missing and `args` as the applied arguments.
    MKCLOSURE         : (res : CairoReg)      -> CairoName          -> (missing : Nat)   -> (args : List CairoReg) -> CairoInst
    -- Apply one value to the function dynamically, creating a new closure or the result.
    -- Linear implicits get threaded through every time, but only used in the last call.
    APPLY             : (res : CairoReg)      -> LinearImplicitArgs -> (fun : CairoReg)  -> (arg  :      CairoReg) -> CairoInst
    -- Call function and assign results to `res`.
    CALL              : (res : List CairoReg) -> LinearImplicitArgs -> CairoName         -> (args : List CairoReg) -> CairoInst
    -- Call an external primitive presented by the backend.
    EXTPRIM           : (res : List CairoReg) -> LinearImplicitArgs -> CairoName         -> (args : List CairoReg) -> CairoInst
    -- Access an intrinsic by its name
    STARKNETINTRINSIC : (res : CairoReg)      -> LinearImplicitArgs -> StarkNetIntrinsic -> (args : List CairoReg) -> CairoInst

    -- Implicit constraints: `alts`s must be covering if `def` empty; if `alts` empty `def` may not be empty.
    -- Case statement with alternatives, and maybe a default case
    CASE      : CairoReg      -> (alts : List (Int, List CairoInst))        -> (def : Maybe (List CairoInst)) -> CairoInst
    -- Case statement on a constant (on primitives, e.g. Nat)
    CONSTCASE : CairoReg      -> (alts : List (CairoConst, List CairoInst)) -> (def : Maybe (List CairoInst)) -> CairoInst
    -- Return the list of values, including the registers for the implicits at the end. Must be in tail position.
    RETURN    : List CairoReg -> SortedMap LinearImplicit CairoReg                                            -> CairoInst

    -- Generate an irrelevant value. e.g. used for erased types, or for unused parameters in a closure
    NULL  : (res : CairoReg)           -> CairoInst
    -- Crash, but with message (implemented as hint). Register unused but "consumed" for invariant across branches.
    ERROR : (res : CairoReg) -> String -> CairoInst

export
implicitName : LinearImplicit -> String
implicitName (MKLinearImplicit name) = name

export
implicitReg : LinearImplicit -> CairoReg
implicitReg impl = CustomReg (implicitName impl) Nothing -- (Just "felt*")

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

-- Annotation for foreign functions that return multiple values.
-- This helps evading unecessary wrapping since Idris only allows single unwrapped return values.
public export
data TupleStructure : Type where
  Tupled      : (tag: Int) -> List TupleStructure -> TupleStructure
  ReturnValue : TupleStructure

public export
Show TupleStructure where
    show (Tupled t args) = "(" ++ (separate ", " (assert_total (map show args)))++")"
    show ReturnValue = "_"

public export
Eq TupleStructure where
  (==) (Tupled t1 l1) (Tupled t2 l2) = t1 == t2 && assert_total (l1 == l2)
  (==) ReturnValue ReturnValue = True
  (==) _ _ = False

public export
record ForeignInfo where
    constructor MkForeignInfo
    -- Is the change to the value of `ap` statically known.
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
     FunDef : (params : List CairoReg) -> (implicits: SortedMap LinearImplicit CairoReg) -> (rets: List CairoReg) -> List CairoInst -> CairoDef
     ForeignDef : (info : ForeignInfo) -> (args:Nat) -> (rets:Nat) -> CairoDef
     ExtFunDef : (tags : List String) -> (params : List CairoReg) -> (implicits: SortedMap LinearImplicit CairoReg) -> (rets: List CairoReg) -> List CairoInst -> CairoDef


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
  show TypeType = "TypeType"

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
    (==) FeltType FeltType = True
    (==) IntegerType IntegerType = True
    (==) Bits8Type Bits8Type = True
    (==) Bits16Type Bits16Type = True
    (==) Bits32Type Bits32Type = True
    (==) Bits64Type Bits64Type = True
    (==) StringType StringType = True
    (==) CharType CharType = True
    (==) TypeType TypeType = True
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
              dataOrder TypeType = 26


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
Show CairoReg where
  show (Unassigned Nothing i d) = "Unassigned_" ++ show i ++ "(" ++ show d ++ ")"
  show (Unassigned (Just s) i d) = "Unassigned_" ++ s ++ "_" ++ show i ++ "(" ++ show d ++ ")"
  show (Param i) = "Param_" ++ show i
  show (CustomReg n _) = n
  show (Local i d) = "Local_" ++ show i ++ "(" ++ show d ++ ")"
  show (Let i d) = "Let_" ++ show i ++ "(" ++ show d ++ ")"
  show (Temp i d) = "Temp_" ++ show i ++ "(" ++ show d ++ ")"
  show (Const s) = "Const_" ++ show s
  show (Eliminated (Replacement reg@(Eliminated _))) = show reg
  show (Eliminated (Replacement reg)) = "Eliminated: " ++ (show reg)
  show (Eliminated Unreachable) = "Eliminated: Out of Scope"
  show (Eliminated Disjoint) = "Eliminated: No shared source"
  show (Eliminated Null) = "Null"
  show (Eliminated (Other s)) = "Eliminated: " ++ s

public export
Eq CairoReg where
  (==) (Unassigned p1 i1 d1) (Unassigned p2 i2 d2) = p1 == p2 && i1 == i2 && d1 == d2
  (==) (Param i1) (Param i2) = i1 == i2
  (==) (CustomReg n1 _) (CustomReg n2 _) = n1 == n2
  (==) (Local i1 d1) (Local i2 d2) = d1 == d2 && i1 == i2
  (==) (Let i1 d1) (Let i2 d2) = d1 == d2 && i1 == i2
  (==) (Temp i1 d1) (Temp i2 d2) = d1 == d2 && i1 == i2
  (==) (Const s1) (Const s2) = s1 == s2
  (==) (Eliminated _) (Eliminated _) = True
  (==) _ _ = False

-- These with highest lifetime expectancy come first
dataOrder : CairoReg -> Int
dataOrder (Const _) = 0             -- Constants never become unreachable
dataOrder (CustomReg _ _) = 1       -- Params are reachable in the whole body
dataOrder (Param _) = 2             -- Params are reachable in the whole body
dataOrder (Local _ _) = 3           -- After assigned Locals are reachable in the whole body
dataOrder (Unassigned _ _ _) = 4    -- Unassigned have the potential to become Local or Const (but could be placed everywhere)
dataOrder (Temp _ _) = 5            -- Just reachable in the current AP region
dataOrder (Let _ _) = 6             -- Same as Temp. However, using multiple times is expensive
dataOrder (Eliminated _) = 7        -- This is never reachable

-- These with highest lifetime expectancy come first
-- Note: StaticOptimizer relies on this order (to be most effective that is)
public export
Ord CairoReg where
  -- First handle the special cases without dept and index
  compare (Eliminated _) (Eliminated _) = EQ
  compare (Eliminated _) _ = GT
  compare _ (Eliminated _) = LT
  compare (Const c1) (Const c2) = compare c1 c2
  compare (Const _) _ = LT
  compare _ (Const _) = GT
  compare (CustomReg n1 _) (CustomReg n2 _) = compare n1 n2
  compare (CustomReg _ _) _ = LT
  compare _ (CustomReg _ _) = GT
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
          depth r = assert_total $ idris_crash ("reg "++(show r)++" has no depth")
          -- Tie Breaker
          tiebreaker : CairoReg -> CairoReg -> Ordering
          tiebreaker (Param i1) (Param i2) = compare i1 i2
          tiebreaker (Unassigned s1 i1 _) (Unassigned s2 i2 _) = thenCompare (compare i1 i2) (compare s1 s2)
          tiebreaker (Local i1 _) (Local i2 _) = compare i1 i2
          tiebreaker (Temp i1 _) (Temp i2 _) = compare i1 i2
          tiebreaker (Let i1 _) (Let i2 _) = compare i1 i2
          tiebreaker _ _ = assert_total $ idris_crash "Should Not Happen"

public export
Eq StarkNetIntrinsic where
  (==) (StorageVarAddr n1) (StorageVarAddr n2) = n1 == n2
  (==) (EventSelector n1) (EventSelector n2) = n1 == n2
  (==) (FunctionSelector n1) (FunctionSelector n2) = n1 == n2
  (==) _ _ = False


public export
Ord StarkNetIntrinsic where
    compare (StorageVarAddr n1) (StorageVarAddr n2) = compare n1 n2
    compare (EventSelector n1) (EventSelector n2) = compare n1 n2
    compare (FunctionSelector n1) (FunctionSelector n2) = compare n1 n2
    compare i1 i2 = compare (order i1) (order i2)
    where order : StarkNetIntrinsic -> Int
          order (StorageVarAddr _) = 0
          order (EventSelector _) = 1
          order (FunctionSelector _) = 2


public export
Eq CairoInst where
  (==) (ASSIGN r1 c1) (ASSIGN r2 c2) = r1 == r2 && c1 == c2
  (==) (STARKNETINTRINSIC r1 i1 inter1 a1) (STARKNETINTRINSIC r2 i2 inter2 a2) = r1 == r2 && i1 == i2 && inter1 == inter2 && a1 == a2
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
Show StarkNetIntrinsic where
  show (StorageVarAddr n) = "StorageVarAddr(\{show n})"
  show (EventSelector n) = "EventSelector(\{show n})"
  show (FunctionSelector n) = "FunctionSelector(\{show n})"

public export
Show CairoInst where
  show (ASSIGN r c) = "ASSIGN \{show r} \{show c}"
  show (STARKNETINTRINSIC r i inter a) = "STARKNETINTRINSIC \{show r} \{show $ SortedMap.toList i} \{show inter} \{show a}"
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
  (==) (ExtFunDef t1 p1 i1 r1 b1) (ExtFunDef t2 p2 i2 r2 b2) = t1 == t2 && p1 == p2  && i1 == i2 && r1 == r2 && assert_total (b1 == b2)
  (==) _ _ = False

public export
Show CairoDef where
  show (FunDef p i r b) = "(\{separate "," (map show p)}){\{separate "," (map (\(i,r) => (show i) ++ "@" ++ (show r)) (SortedMap.toList i))}} -> (\{separate "," (map show r)}){\n\{separate "\n" (map show b)}\n}"
  show (ExtFunDef t p i r b) = "{\{separate "," t} \{separate "," (map (\(i,r) => (show i) ++ "@" ++ (show r)) (SortedMap.toList i))}}(\{separate "," (map show p)}):(\{separate "," (map show r)}){\n\{separate "\n" (map show b)}\n}"
  -- Todo: Code
  show (ForeignDef (MkForeignInfo isApStable untupledSig implicits imports code) args rets) = "Foreign (\{show args}->\{show rets}) \{show isApStable} \{show untupledSig} \{show implicits} \{show imports} (code not represented)"
