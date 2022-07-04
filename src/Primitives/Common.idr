module Primitives.Common

import Core.Context
import CairoCode.CairoCode
import CairoCode.CairoCodeUtils
import CommonDef
import Data.SortedSet
import Data.SortedMap
import CodeGen.CodeGenHelper
import Debug.Trace


-- This is a separate module to avoid cyclic dependencies

-- Currently simplified we may add information if necessary but I have the feeling this is enough
public export
data ValueInfo : Type where
     UnknownValue : ValueInfo
     ConstValue : CairoConst -> ValueInfo
     CompositeValue : (tag:Int) -> List ValueInfo -> ValueInfo
     ClosureValue : Name -> (missing:Nat) -> List ValueInfo -> ValueInfo

public export
data EvalRes : Type where
     Failure : String -> EvalRes
     NewValue : ValueInfo -> EvalRes
     ArgValue : Nat -> EvalRes

public export
data PrimFnCode = Instructions (List CairoInst) | Raw String

public export
interface PrimFn where
    apStable : Bool
    apStable = True

    implicits : SortedSet LinearImplicit
    implicits = empty

    imports : SortedSet Import
    imports = empty

    eval: List ValueInfo -> Maybe EvalRes

    generateCode : String -> (res:CairoReg) -> (args:List CairoReg) -> LinearImplicitArgs -> PrimFnCode

public export
interface ConstReg where
    -- Some things are hard to implement for these so unless needed do not do them
    -- this always need to be apStable for now
    -- apStable : Bool
    -- this are not allowed to have implicits for now
    -- implicits : SortedSet LinearImplicit
    -- there are not allowed to have imports for now (this may be the most likely to be needed)
    -- imports : SortedSet Import
    manifestConstantReg : String -> CairoReg -> (Maybe String, CairoReg)
    assignConstantReg : CairoReg -> CairoConst -> String
    -- default is no manifest is needed, reg can be used directly inline
    manifestConstantReg _ r@(Const c) = (Nothing,r)
    manifestConstantReg _ r = assert_total $ idris_crash $ "Not a constant: " ++ (show r)
    -- default is const can simply be assigned
    assignConstantReg  r c =
        if (isLocal r) then "\{ compileRegDeclDirect r } = \{ compileConst c }\n"
        else if (isConst r) then  ""
        else compileConstRegDecl r ++ " = \{ compileConst c }\n"

export
makeBuiltinName : String -> Name
makeBuiltinName fnName = (UN $ Basic fnName)

export
genRuntimeNote : Maybe (String -> (res:CairoReg) -> (args:List CairoReg) -> LinearImplicitArgs -> PrimFnCode)
genRuntimeNote = Just (\n,r,_,_ => Raw ("#Error: Missing primop: " ++ n ++ " - target: " ++ show r ++ "\n"))

export 
generateMissingCodeError : String -> Maybe (String -> a) -> a
generateMissingCodeError name (Just fallback) = trace ("Missing primop: " ++ name) (fallback name)
generateMissingCodeError name _ = assert_total $ idris_crash $ "Missing primop: " ++ name

export 
pow2 : Nat -> Integer
pow2 nBits = product $ replicate nBits 2

-- Helpers
public export
toInt : Bool -> CairoConst
toInt True = I 1
toInt False = I 0

export
bitwiseBuiltinImport : Import
bitwiseBuiltinImport = MkImport "starkware.cairo.common.cairo_builtins" "BitwiseBuiltin" Nothing

-- This currently is ugly for things like if a == b then ... as it gens two ifs
--  But while eliminating it would be possible its not worth the trouble yet
--   For the record it would be over introducing (IF res function args ifcase elsecase) as Opcode
-- compileCairoInst _ (OP r linImpls (EQ _) [a,b]) = compileEqOp a b linImpls r
export
compileEqOp : String -> CairoReg -> List CairoReg -> LinearImplicitArgs -> String
compileEqOp primFnName reg [a,b] linImpls = 
  if linImpls == empty 
    then """
      if \{ compileReg a } == \{ compileReg b }:
        \{compileNestRegDecl reg} = 1
      else:
        \{compileNestRegDecl reg} = 0
      end

    """
    else assert_total $ idris_crash "no implicits expected for Eq \{primFnName}" 
compileEqOp primFnName _ _ _ = assert_total $ idris_crash "Bad arguments to generateCode compileEqOp \{primFnName}"
