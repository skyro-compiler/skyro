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

i8_3 : Integer
i8_3 = cast {to=Integer} f_3

i8_100 : Integer
i8_100 = cast {to=Integer} f_100

i8_50 : Integer
i8_50 = cast {to=Integer} f_50

out : Cast a Felt => a -> Cairo ()
out = output . cast


%noinline
main : Cairo ()
main = do

  out $ assert_total $ i8_3 `div` (the Integer 2)
  out $ assert_total $ i8_3 `mod` (the Integer 2)

  out $ assert_total $ (-i8_3) `div` (the Integer (-2))
  out $ assert_total $ (-i8_3) `mod` (the Integer (-2))

  out $ assert_total $ (-i8_3) `div` (the Integer 2)
  out $ assert_total $ (-i8_3) `mod` (the Integer 2)

  out $ assert_total $ i8_3 `div` (the Integer (-2))
  out $ assert_total $ i8_3 `mod` (the Integer (-2))

  out $ i8_100 + i8_50 
  out $ i8_100 - i8_50
  out $ i8_100 * i8_50

  out $ assert_total $ i8_100 `div` (the Integer 7)
  out $ assert_total $ i8_100 `mod` (the Integer 7)
  out $ - i8_50

  -- Bitwise ops not yet supported
  -- out $ i8_100 .&. i8_50
  -- out $ i8_100 .|. i8_50
  -- out $ i8_100 `xor` i8_50
  -- out $ i8_50 `shiftL` 1
  -- out $ i8_100 `shiftR` 1

  out $ i8_100 < i8_50
  out $ i8_100 <= i8_50
  out $ i8_100 == i8_50
  out $ i8_100 >= i8_50
  out $ i8_100 > i8_50
