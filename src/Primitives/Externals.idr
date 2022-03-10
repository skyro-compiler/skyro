module Primitives.Externals

import Primitives.Common
import Primitives.Felt
import Primitives.Primitives
import CairoCode.CairoCode
import Core.Context
import CairoCode.CairoCodeUtils
import CodeGen.CodeGenHelper
import Data.SortedMap
import Data.SortedSet

interface External where
  apStable : Bool
  tupleSig : Maybe TupleStructure
  implicits : List LinearImplicit
  imports : SortedSet Import
  genCode : List CairoReg -> LinearImplicitArgs -> List CairoReg -> String
  eval: (numRes:Nat) -> List ValueInfo -> Maybe (List EvalRes)

%spec f
associate : (rec:External) => (f:(External -> a)) -> a
associate fun = fun rec

 -- Definitions
[pedersen_hash] External where
    apStable = True
    tupleSig = Nothing
    implicits = [pedersen_builtin]
    imports = empty
    eval _ _ = Nothing -- Todo: add pedersen_hash impl in idris2
    -- tupled
    genCode [r] impls [a,b] = """
        #cairopedersenhash
        assert [\{ ptrName }] = \{ compileReg a }
        assert [\{ ptrName } + 1] = \{ compileReg b }
        \{ compileRegDecl r } = [\{ ptrName } + 2]
        \{ compileRegDecl (snd ptr) } = \{ ptrName } + 3

        """
        where ptr: (CairoReg, CairoReg)
              ptr = fromMaybe (assert_total $ idris_crash "pedersen_ptr is missing") (lookup pedersen_builtin impls)
              ptrName : String
              ptrName = compileReg (fst ptr)
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairopedersenhash"

[cairo_output] External where
    apStable = True
    tupleSig = Nothing
    implicits = [] -- Will use a Monadic implementation for the builtin
    imports = empty
    eval _ _ = Nothing -- output can not be constant folded
    genCode [r] impls [ptr,val] = """
        #cairooutput
        assert [\{ compileReg ptr }] = \{ compileReg val }
        \{ compileRegDecl r } = \{ compileReg ptr } + 1

        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairooutput"

 -- Dispatch
%inline
dispatch : (name:Name) -> ((External => a) -> a)
dispatch (NS _ (UN $ Basic "cairopedersenhash")) = associate @{pedersen_hash}
dispatch (NS _ (UN $ Basic "cairooutput")) = associate @{cairo_output}
dispatch n = (\f => assert_total $ idris_crash ("No implementation for external " ++ show n ++ " available"))

 -- Accessors
export
externalApStable : Name -> Bool
externalApStable name = dispatch name apStable

export
externalLinearImplicits : Name -> List LinearImplicit
externalLinearImplicits name = dispatch name implicits

export
externalImports : Name -> SortedSet Import
externalImports name = dispatch name imports

export
externalCodeGen : Name -> List CairoReg -> LinearImplicitArgs -> List CairoReg -> String
externalCodeGen name res impls args = dispatch name genCode res checkedImpls args
    where expectedImpls : List LinearImplicit
          expectedImpls = externalLinearImplicits name
          checkedImpls : LinearImplicitArgs
          checkedImpls = if (length (keys impls)) == (length expectedImpls) && all (\i => isJust $ lookup i impls) expectedImpls
            then impls
            else assert_total $ idris_crash ("implicits are not correct for " ++ (show name))

export
externalTupleSig : Name -> Maybe TupleStructure
externalTupleSig name = dispatch name tupleSig

export
externalEval : Name -> (numRes:Nat) -> List ValueInfo -> Maybe (List EvalRes)
externalEval name numRets args = dispatch name eval numRets args
