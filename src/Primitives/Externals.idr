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

[cairo_capture_ptr] External where
    apStable = True
    tupleSig = Nothing
    implicits = [] -- Will use a Monadic implementation for the builtin
    imports = empty
    eval _ _ = Nothing -- output can not be constant folded
    genCode [valOut] impls [_,valIn] = """
        \{ compileRegDecl valOut } = \{ compileReg valIn }
        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_capture_ptr"

[cairo_write_ptr] External where
    apStable = True
    tupleSig = Nothing
    implicits = []
    imports = empty
    eval _ _ = Nothing
    -- we use direct here as otherwise we can get a type error as s_ptr can be of type felt*
    --  it should be safe as s_ptr should behave quite predictable (otherwise we need to cast here depending on what s_ptr is)
    genCode [n_ptr] impls [s_ptr,val] = """
        #writeFelt
        assert [\{ compileReg s_ptr }] = \{ compileReg val }
        \{ compileRegDeclDirect n_ptr } = \{ compileReg s_ptr } + 1
        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_write_ptr"

[cairo_read_ptr] External where
    apStable = True
    tupleSig = Nothing
    implicits = []
    imports = empty
    eval _ _ = Nothing
    genCode [(Eliminated _), val] impls [s_ptr] = """
        #readFelt
        \{ compileRegDecl val } =  [\{ compileReg s_ptr }]
        """
    -- we use direct here as otherwise we can get a type error as s_ptr can be of type felt*
    --  it should be safe as s_ptr should behave quite predictable (otherwise we need to cast here depending on what s_ptr is)
    genCode [n_ptr, (Eliminated _)] impls [s_ptr] = """
        #readFelt
        \{ compileRegDeclDirect n_ptr } = cast(\{ compileReg s_ptr } + 1,felt)
        """
    genCode [n_ptr, val] impls [s_ptr] = """
        #readFelt
        \{ compileRegDecl val } =  [\{ compileReg s_ptr }]
        \{ compileRegDeclDirect n_ptr } = \{ compileReg s_ptr } + 1
        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_write_ptr"

[cairo_create_ptr] External where
    apStable = True
    tupleSig = Nothing
    implicits = []
    imports = singleton (MkImport "starkware.cairo.common.alloc" "alloc" Nothing)
    eval _ _ = Nothing
    -- we use direct here as otherwise we can get a type error as s_ptr can be of type felt*
    -- it should be safe as s_ptr should behave quite predictable (otherwise we need to cast here depending on what s_ptr is)
    genCode [n_ptr] impls [] = """
        #createSegment
        let (\{ regName n_ptr }_tmp_) = alloc()
        \{ compileRegDeclDirect n_ptr} = cast(\{ compileReg n_ptr }_tmp_,felt)
        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_create_ptr"

[read_tag] External where
    apStable = True
    tupleSig = Nothing
    implicits = []
    imports = empty
    eval _ _ = Nothing
    genCode [tagReg] impls [valReg] = """
        #readtag
        \{ compileRegDecl tagReg } =  [\{ compileReg valReg }]
        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_create_ptr"

[make_tagless] External where
    apStable = True
    tupleSig = Nothing
    implicits = []
    imports = empty
    eval _ _ = Nothing
    genCode [reg] impls args = """
        #MKCON
        tempvar \{ ptrName } = new ( \{ showSep ", " (map compileReg args) } )
        \{ compileRegDeclRef reg } = cast(\{ ptrName },felt)
        """
        where ptrName : String
              ptrName = compileReg reg ++ "_ptr_" ++ show (length args)
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_create_ptr"

[cairo_mem_copy] External where
    apStable = False
    tupleSig = Nothing
    implicits = []
    imports = singleton (MkImport "starkware.cairo.common.memcpy" "memcpy" Nothing)
    eval _ _ = Nothing
    -- we use direct here as otherwise we can get a type error as s_ptr can be of type felt*
    -- it should be safe as s_ptr should behave quite predictable (otherwise we need to cast here depending on what s_ptr is)
    genCode [n_ptr] impls [fromPtr,toPtr,lenReg] = """
        memcpy(cast( \{ compileReg toPtr },felt*), cast( \{ compileReg fromPtr },felt*), \{ compileReg lenReg })
        \{ compileRegDeclDirect n_ptr } = \{ compileReg toPtr } + \{ compileReg lenReg }
        """
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for cairo_create_ptr"

[bounded_tag] External where
    apStable = True
    tupleSig = Nothing
    implicits = [range_check_builtin]
    imports = empty
    eval 1 [ConstValue (F a), ConstValue (I b)] = if (a < (cast b))
        then Just $ [ArgValue 0]
        else Just $ [Failure "\{show a} < \{show b} always fails"]
    eval _ _ = Nothing
    genCode [reg] impls [val, (Const (I bound))] = """
        #Checks that supplied Tag is valid
        assert [\{ ptrName }] = \{ compileReg val }
        assert [\{ ptrName } + 1] = \{show (bound-1)} - \{ compileReg val }
        \{ compileRegDecl (snd ptr) } = \{ ptrName } + 2
        \{ compileRegDeclRef reg } = \{ compileReg val }
        """
        where ptr: (CairoReg, CairoReg)
              ptr = fromMaybe (assert_total $ idris_crash "range_check_ptr is missing") (lookup range_check_builtin impls)
              ptrName : String
              ptrName = compileReg (fst ptr)
    genCode _ _ _ = assert_total $ idris_crash "unsupported signature for bounded_tag"

 -- Dispatch
%inline
dispatch : (name:Name) -> ((External => a) -> a)
dispatch (NS _ (UN $ Basic "cairocaptureptr")) = associate @{cairo_capture_ptr}
dispatch (NS _ (UN $ Basic "cairowriteptr")) = associate @{cairo_write_ptr}
dispatch (NS _ (UN $ Basic "cairoreadptr")) = associate @{cairo_read_ptr}
dispatch (NS _ (UN $ Basic "readtag")) = associate @{read_tag}
dispatch (NS _ (UN $ Basic "maketagless")) = associate @{make_tagless}
dispatch (NS _ (UN $ Basic "cairocreateptr")) = associate @{cairo_create_ptr}
dispatch (NS _ (UN $ Basic "cairopedersenhash")) = associate @{pedersen_hash}
dispatch (NS _ (UN $ Basic "cairooutput")) = associate @{cairo_output}
dispatch (NS _ (UN $ Basic "cairomemcopy")) = associate @{cairo_mem_copy}
dispatch (NS _ (UN $ Basic "boundedtag")) = associate @{bounded_tag}

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
