module CommonDef

import CairoCode.Name
import Protocol.Hex
import System
import System.File
import Libraries.Utils.Path
import Data.String

%default total

-- MAIN Entry
export
cairo_main : CairoName
cairo_main = fullName ["Main"] "main"

export
entry_name : CairoName
entry_name = externalName "main"

public export
fromZeroTo : Int -> List Int
fromZeroTo 0 = [0]
fromZeroTo n = if n < 0 then [] else fromZeroTo (assert_smaller n (n-1)) ++ [n]

public export
CompilationPass : Type -> Type
CompilationPass a = List (CairoName, a) -> List (CairoName, a)

public export
data TargetType = Cairo | StarkNet

-- According to idris2 docs this should be in prelude but is not found
public export
thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare EQ ord = ord
thenCompare ord _ = ord
