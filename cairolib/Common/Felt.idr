module Common.Felt

-- Idris2 does not support pattern matching on [external] types.
-- Do not declare public since it allows to write pattern matching code which does not work
export
data Felt : Type where [external]

public export %extern
prim__mk_Felt : Integer -> Felt

public export %extern
prim__from_Felt : Felt -> Integer

public export %extern
prim__add_Felt : Felt -> Felt -> Felt

public export %extern
prim__mul_Felt : Felt -> Felt -> Felt 

public export %extern
prim__sub_Felt : Felt -> Felt -> Felt

public export %extern
prim__div_Felt : Felt -> Felt -> Felt

public export %extern
prim__eq_Felt : Felt -> Felt -> Bool

public export %inline
Eq Felt where
  (==) = prim__eq_Felt

public export %inline
Num Felt where
  (+) = prim__add_Felt
  (*) = prim__mul_Felt
  fromInteger = prim__mk_Felt

public export %inline
Neg Felt where
  negate x = assert_total $ prim__sub_Felt (fromInteger 0) x
  a - b = prim__sub_Felt a b

public export %inline
Integral Felt where
  div = prim__div_Felt
  mod _ _ = prim__mk_Felt 0 -- In a primefield divisions do not have a rest

public export %inline
Show Felt where
  show = show . prim__from_Felt

public export %inline
[PlusFeltSemi] Semigroup Felt using Semigroup.Additive where
  (<+>) x y = x + y

public export %inline
[MultFeltSemi] Semigroup Felt using Semigroup.Multiplicative where
  (<+>) x y = x * y

public export %inline
[PlusFeltMonoid] Monoid Felt using Monoid.Additive PlusFeltSemi where
  neutral = 0

public export %inline
[MultFeltMonoid] Monoid Felt using Monoid.Multiplicative MultFeltSemi where
  neutral = 1

{-
TODO: How to treat partiallity?

%inline
partial
public export
Integral Felt where
  div x y
      = case y == 0 of
             False => prim__div_Felt x y
  mod x y
      = case y == 0 of
             False => prim__mod_Felt x y

-}


public export %inline
Cast Bool Felt where
  cast True = 1
  cast False = 0


export
%foreign 
    "imports:starkware.cairo.common.math_cmp is_le_felt"
    "linear_implicits:range_check_ptr"
    """
    code:
    func Common_Felt_is_le_felt(range_check_ptr, a, b) -> (res, range_check_ptr):
       let (res) = is_le_felt{range_check_ptr = range_check_ptr}(a,b)
       return (res, range_check_ptr)
    end
    """
is_le_felt : (a: Felt) -> (b: Felt) -> Bool
