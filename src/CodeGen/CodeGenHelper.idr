module CodeGen.CodeGenHelper

import Protocol.Hex
import CairoCode.CairoCode
import Core.Context
import CairoCode.CairoCodeUtils
import Data.SortedMap
import Data.SortedSet

import Debug.Trace

%hide Prelude.toList

export
-- Constant Operations
constToInteger : CairoConst -> Maybe Integer
constToInteger (I x) = Just $ cast x
constToInteger (I8 x) = Just $ cast x
constToInteger (I16 x) = Just $ cast x
constToInteger (I32 x) = Just $ cast x
constToInteger (I64 x) = Just $ cast x
constToInteger (F x) = Just  x
constToInteger (BI x) = Just  x
constToInteger (Ch x) = Just $ cast x
constToInteger (B8 x) = Just $ cast x
constToInteger (B16 x) = Just $ cast x
constToInteger (B32 x) = Just $ cast x
constToInteger (B64 x) = Just $ cast x
-- Todo: is this correct? How are non primitive types represented? conflict?
-- Negative numbers in case it is incorrect to reduce conflict potential.
constToInteger IntType = Just (-1)
constToInteger Int8Type = Just (-2)
constToInteger Int16Type = Just (-3)
constToInteger Int32Type = Just (-4)
constToInteger Int64Type = Just (-5)
constToInteger FeltType = Just (-6)
constToInteger IntegerType = Just (-7)
constToInteger StringType = Just (-8)
constToInteger CharType = Just (-9)
constToInteger Bits8Type = Just (-10)
constToInteger Bits16Type = Just (-11)
constToInteger Bits32Type = Just (-12)
constToInteger Bits64Type = Just (-13)
constToInteger _ = Nothing

export
compileConst: CairoConst -> String
compileConst (I x) = show x
compileConst (I8 x) = show x
compileConst (I16 x) = show x
compileConst (I32 x) = show x
compileConst (I64 x) = show x
compileConst (F x) = show x 
compileConst (BI x) = show x  -- Todo: We don't have BigInteger. Temporary hack until we have.
compileConst (Ch x) = assert_total $ idris_crash "Char is not supported yet." 
compileConst (Str x) = assert_total $ idris_crash "String is not supported yet."
-- compileConst (Named x) = x
compileConst (B8 x) = show x
compileConst (B16 x) = show x
compileConst (B32 x) = show x
compileConst (B64 x) = show x
compileConst typ = show $ constToInteger typ


export
regName : CairoReg -> String
regName (Unassigned Nothing n d) = "u_" ++ show n ++ "_" ++ show d
regName (Unassigned (Just p) n d) = "_" ++ p ++ "_" ++ show n ++ "_" ++ show d
regName (CustomReg n Nothing) = n
regName (CustomReg n _) = "c_" ++ n
regName (Param i) = "p_" ++ show i
regName (Local i _) = "l_" ++ show i
regName (Let i _) = "b_" ++ show i
regName (Temp i _) = "t_" ++ show i
regName (Const v) = "inlined_constant"
regName (Eliminated Null) = "null"
regName (Eliminated (Other r)) = "eliminated_by_" ++ r
regName (Eliminated (Replacement c@(Eliminated _))) = regName c
regName (Eliminated (Replacement c)) = "discarded_register_" ++ (regName c)
regName (Eliminated Disjoint) = "disjoint_registers"
regName (Eliminated Unreachable) = "out_of_scope_sources"

export
paramRegName :  CairoReg -> String
paramRegName (CustomReg n _) = n
paramRegName r = regName r

export
paramReg : CairoReg -> String
paramReg r@(CustomReg n (Just t)) = (paramRegName r) ++ " : " ++ t
paramReg r = paramRegName r

export
compileReg : CairoReg -> String
compileReg (Const v) = compileConst v
compileReg (Eliminated Null) = "0"

compileReg e@(Eliminated _) = "0" -- trace "warning debug code active in CodeGenHelper" (regName e)
compileReg reg = regName reg

export
compileRegDeclCommon : CairoReg -> String -> String -> String -> String
compileRegDeclCommon (Unassigned Nothing i d) localS _ _ = localS ++ "u_" ++ show i ++ "_" ++ show d
compileRegDeclCommon (Unassigned (Just p) i d) localS _ _ = localS ++ "_" ++ p ++ "_" ++ show i ++ "_" ++ show d
compileRegDeclCommon (Local i _) localS _ _ = localS ++ "l_" ++ show i
compileRegDeclCommon (Let i _) _ _ letS = letS ++ " b_" ++ show i
compileRegDeclCommon (Temp i _) _ tempS _ = tempS ++ " t_" ++ show i
compileRegDeclCommon (Const v) _ _ letS = letS ++ " inlined_constant"
compileRegDeclCommon e@(Eliminated _) _ _ letS = letS ++ " " ++ (regName e)
-- allows to use CustomRegs in Manifestations
compileRegDeclCommon (CustomReg n Nothing) _ _ letS = letS ++ " " ++ n
compileRegDeclCommon _ _ _ _ = ""

export
compileRegDecl : CairoReg -> String
compileRegDecl r = compileRegDeclCommon r "assert " "tempvar" "let"

export
compileRegDeclDirect : CairoReg -> String
compileRegDeclDirect  r = compileRegDeclCommon r "" "tempvar" "let"

export
compileNestRegDecl : CairoReg -> String
compileNestRegDecl r = compileRegDeclCommon r "assert " "tempvar" "tempvar"

export
compileConstRegDecl : CairoReg -> String
compileConstRegDecl = compileRegDecl
-- made problems because scoping rules seem not to apply to const
-- compileConstRegDecl r = compileRegDeclCommon r "assert " "const" "const"

export
compileRegDeclRef : CairoReg -> String
compileRegDeclRef r = compileRegDeclCommon r "assert " "let" "let"

export
compileRegManifest : CairoReg -> String
compileRegManifest r = if isLocal r then "" else compileRegDeclCommon r " " "tempvar" "tempvar"

export
ensureManifested : CairoReg -> String -> (String, String)
ensureManifested reg@(Let _ _) tempName = ("tempvar \{tempName} = \{compileReg reg}\n", tempName)
ensureManifested reg tempName = ("", compileReg reg)

-- records do not have tags
export
tagToString : Maybe Int -> String
tagToString (Just tag) = show tag
tagToString Nothing = "0"

export
impossibleCase : CairoReg -> String -> String
impossibleCase reg msg = """
    with_attr error_message(\"\{ msg }\"):
        assert 1 = 0
    end
    \{ compileRegDecl reg } = 0

    """

export
extendName : Name -> String -> Name
extendName (NS ns innerName) ext = NS ns (extendName innerName ext)
extendName (Nested idx innerName) ext = Nested idx (extendName innerName ext)
extendName (UN (Basic name)) ext = (UN (Basic (name ++ ext)))
extendName (DN str name) ext =  DN (str++ext) (extendName name ext)
extendName _ ext = assert_total $ idris_crash "Not supported for now"
