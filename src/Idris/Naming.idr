module Idris.Naming

import Data.List
import Data.String
import Core.Name.Namespace
import Core.Context
import CairoCode.Name

cairoName : Name -> (List String,String)
cairoName (NS ns x) = case (reverse $ unsafeUnfoldNamespace ns) of
   Nil => cairoName x
   ns => case cairoName x of
     (suffix, name) => (ns ++ suffix, name)
cairoName (UN (Basic n)) = (Nil, n)
cairoName (UN (Field n)) = (Nil, "rf__" ++ n)
cairoName (UN Underscore) = (Nil, "_")
cairoName (MN x y) = (Nil, "mn__" ++ x ++ "_" ++ show y)
cairoName (PV x y) = case cairoName x of
    (suffix, name) => (suffix, "pat_var_"++name)
cairoName (DN x y) = cairoName y
cairoName (Nested (i, x) n) = case cairoName n of
    (suffix, name) => (suffix, "nested__" ++ show i ++ "_" ++ name)
cairoName (CaseBlock x y) = (Nil, "case__" ++ x ++ "_" ++ show y)
cairoName (WithBlock x y) = (Nil, "with__" ++ x ++ "_" ++ show y)
cairoName (Resolved x) = (Nil, "fn__" ++ show x)

isMachineName : Name -> Bool
isMachineName (NS _ innerName) = isMachineName innerName
isMachineName (PV innerName _) = isMachineName innerName
isMachineName (DN _ innerName) = isMachineName innerName
isMachineName (Nested _ innerName) = isMachineName innerName
isMachineName (UN _ ) = False
isMachineName (MN _ _) = True
isMachineName _ = True

export
fromIdrisName : Name -> CairoName
fromIdrisName n = case cairoName n of
    (ns, name) => if isMachineName n
        then extendNamePlain "generated" (fullName ns name)
        else fullName ns name
