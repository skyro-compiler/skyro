module CairoCode.Name

import Data.List1
import Data.List
import Data.String
import Protocol.Hex

public export
data CairoName : Type where
    RawName : List String -> String -> CairoName
    Extension : String -> Maybe Int -> CairoName -> CairoName

public export
Show CairoName where
    show (RawName ns name) = foldr (\ns,n => "\{ns}.\{n}") name ns
    show (Extension name (Just iter) rest) = assert_total $ "\{name}$\{show iter}+\{show rest}"
    show (Extension name Nothing rest) = assert_total $ "\{name}+\{show rest}"

-- Reverse of Show
export
parseName : String -> CairoName
parseName n = parse $ forget $ split (== '+') n
    where parse : List String -> CairoName
          parse (x::Nil) = let names = split (== '.') x in RawName (init names) (last names)
          parse (x::xs) = case forget (split (== '$') x) of
            (e::Nil) => Extension e Nothing (parse xs)
            (e::i::_) => Extension e (parseInteger i) (parse xs)
            -- Somehow I can not match on List1 thus forget & this case
            Nil => parse xs
          -- Somehow I can not match on List1 thus forget & this case
          parse Nil = assert_total $ idris_crash "can not happen"

export
extractNamespace : CairoName -> List String
extractNamespace (RawName ns _) = ns
extractNamespace (Extension _ _ rest) = extractNamespace rest

export
extractName : CairoName -> String
extractName (RawName _ n) = n
extractName (Extension _ _ rest) = extractName rest

-- Alternate show that is Cairo Compatible --
export
toCairoIdent : CairoName -> String
toCairoIdent (RawName ns name) = foldr (\ns,n => "\{ns}_\{n}") name ns
toCairoIdent (Extension name (Just iter) rest) = "\{name}_\{show iter}__\{toCairoIdent rest}"
toCairoIdent (Extension name Nothing rest) = "\{name}__\{toCairoIdent rest}"

-- Duplicated but otherwise we have a cyclic dependency
-- Todo: Reorganize so we get rid of cycle and can still share
thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare EQ ord = ord
thenCompare ord _ = ord

infixr 11 `thenCompare`

public export
Eq CairoName where
    (==) (RawName ns1 n1) (RawName ns2 n2) = ns1 == ns2 && n1 == n2
    (==) (Extension n1 i1 r1) (Extension n2 i2 r2) = assert_total $ n1 == n2 && i1 == i2 && r1 == r2
    (==) _ _ = False

public export
Ord CairoName where
    compare (RawName ns1 n1) (RawName ns2 n2) = (compare ns1 ns2) `thenCompare` (compare n1 n2)
    compare (RawName _ _) _ = LT
    compare _ (RawName _ _) = GT
    compare (Extension n1 Nothing r1) (Extension n2 Nothing r2) = assert_total $ (compare n1 n2) `thenCompare` (compare r1 r2)
    compare (Extension n1 (Just i1) r1) (Extension n2 (Just i2) r2) = assert_total $ (compare n1 n2) `thenCompare` (compare i1 i2) `thenCompare` (compare r1 r2)
    compare (Extension _ Nothing _) (Extension _ (Just i) _) = LT
    compare (Extension _ (Just i) _) (Extension _ Nothing _) = GT

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

export
extendNamePlain : String -> CairoName -> CairoName
extendNamePlain ext name = if all (\c => isAlphaNum c || c == '_') (unpack ext)
    then Extension ext Nothing name
    else assert_total $ idris_crash "Cairo name extensions contains invalid character: \{ext}"

export
noMangle: CairoName -> CairoName
noMangle = extendNamePlain "no_mangle"

export
externalName : String -> CairoName
externalName name = noMangle (RawName Nil name)

export
isMachineGenerated : CairoName -> Bool
isMachineGenerated (Extension "generated" _ _) = True
isMachineGenerated (Extension _ _ rest) = isMachineGenerated rest
isMachineGenerated (RawName _ _) = False

export
nameFromString : String -> CairoName
nameFromString name = RawName [] (cairoIdent name)

export
fullName : List String -> String -> CairoName
fullName ns name = RawName (map cairoIdent ns) (cairoIdent name)

export
extendName : String -> Int -> CairoName -> CairoName
extendName ext iter name = if all (\c => isAlphaNum c || c == '_') (unpack ext)
    then Extension ext (Just iter) name
    else assert_total $ idris_crash "Cairo name extensions contains invalid character: \{ext}"

export
incrementalExtendName : String -> CairoName -> CairoName
incrementalExtendName ext r@(Extension ext2 (Just i) oldR) = if ext == ext2
    then Extension ext (Just (i+1)) oldR
    else Extension ext (Just 0) r
incrementalExtendName ext r = Extension ext (Just 0) r

export
asCairoIdent : CairoName -> String
asCairoIdent (Extension "no_mangle" Nothing name) = toCairoIdent name
asCairoIdent name = toCairoIdent $ extendNamePlain "_def" name

export
asNamespaceIdent : CairoName -> String
asNamespaceIdent (Extension "no_mangle" Nothing name) = toCairoIdent name
asNamespaceIdent name = toCairoIdent $ extendNamePlain "_ns" name

--- This does not work as events & storageVars are declared as Functions ---
--- Todo: However would be nice but requires extending the ExtFun defs over a type
--        Or adding a type to Raw Name
-- export
-- asFunctionIdent : CairoName -> String
-- asFunctionIdent (Extension "no_mangle" Nothing name) = toCairoIdent name
-- asFunctionIdent name = toCairoIdent $ extendNamePlain "_func" name

-- export
-- asStorageVarIdent : CairoName -> String
-- asStorageVarIdent (Extension "no_mangle" Nothing name) = toCairoIdent name
-- asStorageVarIdent name = toCairoIdent $ extendNamePlain "_var" name

-- export
-- asEventIdent : CairoName -> String
-- asEventIdent (Extension "no_mangle" Nothing name) = toCairoIdent name
-- asEventIdent name = toCairoIdent $ extendNamePlain "_event" name
