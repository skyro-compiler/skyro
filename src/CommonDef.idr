module CommonDef

import Compiler.VMCode
import Core.Name.Namespace
import Core.Context
import Compiler.Common
import Protocol.Hex
import System
import System.File
import Libraries.Utils.Path
import Data.String

%default total

-- https://github.com/idris-community/Idris2-Ocaml/blob/master/src/Ocaml/Expr.idr#L51
-- https://github.com/idris-lang/Idris2/blob/aa27ccbdb655c1c55560857ce8a92156260df62d/src/Compiler/ES/ES.idr#L99
-- adapted
cairoIdent : String -> String
-- we reserve names ending on _ for use in code gen
cairoIdent s = if isSuffixOf "_" full
  then full ++ "_"
  else full
  where
    okchar : Char -> String
    okchar '_' = "_"
    okchar '=' = "eq_"
    okchar '<' = "lt_"
    okchar '>' = "gt_"
    okchar '\'' = "prime_"
    okchar '(' = "lpar_"
    okchar ')' = "rpar_"
    okchar '{' = "lcurl_"
    okchar '}' = "rcurl_"
    okchar '[' = "lbrack_"
    okchar ']' = "rbrack_"
    okchar '$' = "dollar_"
    okchar ',' = "comma_"
    okchar ' ' = "space_" -- TODO: how can the space be part of the name? Data_Vect_map_Functor_lpar_Vectspace_dollar_nrpar_
    okchar c = if isAlphaNum c then cast c else "_" ++ asHex (cast c)
    full : String
    full = concatMap okchar (unpack s)

cairoUserName : UserName -> String
cairoUserName (Basic n) = cairoIdent n
cairoUserName (Field n) = "rf__" ++ cairoIdent n
cairoUserName Underscore = cairoIdent "_"

public export
cairoName : Name -> String
cairoName (NS ns x) = case cairoIdent (showNSWithSep "_" ns) of
   "" => cairoName x
   ns => ns ++ "_" ++ cairoName x
cairoName (UN x) = cairoUserName x
cairoName (MN x y) = "mn__" ++ cairoIdent x ++ "_" ++ show y
cairoName (PV x y) = "pat__" ++ cairoName x ++ "_" ++ show y
cairoName (DN x y) = cairoName y
cairoName (Nested (i, x) n) = "nested__" ++ show i ++ "_" ++ show x ++ "_" ++ cairoName n
cairoName (CaseBlock x y) = "case__" ++ cairoIdent x ++ "_" ++ show y
cairoName (WithBlock x y) = "with__" ++ cairoIdent x ++ "_" ++ show y
cairoName (Resolved x) = "fn__" ++ show x

export
makeName : String -> String -> Name
makeName ns name = NS (mkNamespace ns) (UN $ Basic name)

-- MAIN Entry
export
cairo_main : Name
cairo_main = makeName "Main" "main"

export
entry_name : Name
entry_name = NS (mkNamespace "") (UN $ Basic "main")

public export
fromZeroTo : Int -> List Int
fromZeroTo 0 = [0]
fromZeroTo n = if n < 0 then [] else fromZeroTo (assert_smaller n (n-1)) ++ [n]

public export
CompilationPass : Type -> Type
CompilationPass a = List (Name, a) -> List (Name, a)

public export
data TargetType = Cairo | StarkNet

-- According to idris2 docs this should be in prelude but is not found
public export
thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare EQ ord = ord
thenCompare ord _ = ord
