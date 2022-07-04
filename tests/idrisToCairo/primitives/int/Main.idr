module Main

import Cairo
import Data.Bits

-- The following functions are required to avoid that the constantfolder
-- evaluates the expressions at compile time.
-- Maybe we should disable the constantfolder and write the tests more direct.


%foreign
  """
  code:
  func Main_f_3() -> (r):
      return (3)
  end
  """
f_3 : Felt

%foreign 
  """
  code:
  func Main_f_100() -> (r):
      return (100)
  end
  """
f_100 : Felt

%foreign 
  """
  code:
  func Main_f_50() -> (r):
      return (50)
  end
  """
f_50 : Felt

i8_3 : Int8
i8_3 = cast {to=Int8} f_3

i8_100 : Int8
i8_100 = cast {to=Int8} f_100

i8_50 : Int8
i8_50 = cast {to=Int8} f_50

out : Cast a Felt => a -> Cairo ()
out = output . cast


%noinline
main : Cairo ()
main = do

  out $ assert_total $ i8_3 `div` (the Int8 2)
  out $ assert_total $ i8_3 `mod` (the Int8 2)

  out $ assert_total $ (-i8_3) `div` (the Int8 (-2))
  out $ assert_total $ (-i8_3) `mod` (the Int8 (-2))

  out $ assert_total $ (-i8_3) `div` (the Int8 2)
  out $ assert_total $ (-i8_3) `mod` (the Int8 2)

  out $ assert_total $ i8_3 `div` (the Int8 (-2))
  out $ assert_total $ i8_3 `mod` (the Int8 (-2))

  out $ i8_100 + i8_50 
  out $ i8_100 - i8_50
  out $ i8_100 * i8_50
  -- BUG, this returns 0!!!
  -- Patternmachting on felt famously does not work. 
  -- Best would be to make it work - otherwise throw an error at compile time or at least crash at runtime.
  -- out $ case b of 0 => 0 ; x => (cast {to=Bits8} a) `div` (cast {to=Bits8} x)
  out $ assert_total $ i8_100 `div` (the Int8 7)
  out $ assert_total $ i8_100 `mod` (the Int8 7)
  out $ - i8_50
  out $ i8_100 .&. i8_50
  out $ i8_100 .|. i8_50 
  out $ i8_100 `xor` i8_50
  out $ i8_50 `shiftL` 1 -- Index is of type Nat. Not implemented yet
  out $ i8_100 `shiftR` 1
  out $ i8_100 < i8_50
  out $ i8_100 <= i8_50
  out $ i8_100 == i8_50
  out $ i8_100 >= i8_50
  out $ i8_100 > i8_50
