module Main

import Cairo
import Data.Bits

-- The following functions are required to avoid that the constantfolder
-- evaluates the expressions at compile time.
-- Maybe we should disable the constantfolder and write the tests more direct.


%foreign
  """
  code:
  func $name$() -> (r):
      return (3)
  end
  """
f_3 : Felt

%foreign
  """
  code:
  func $name$() -> (r):
      return (4)
  end
  """
f_4 : Felt

%foreign 
  """
  code:
  func $name$() -> (r):
      return (100)
  end
  """
f_100 : Felt

%foreign 
  """
  code:
  func $name$() -> (r):
      return (50)
  end
  """
f_50 : Felt


bigFelt : Felt
bigFelt = 1361129467683753853853498429727072845824 -- 2^130

bigInt : Integer
bigInt = cast bigFelt

bi_3 : Integer
bi_3 = (cast {to=Integer} f_3) * bigInt

bi_4 : Integer
bi_4 = (cast {to=Integer} f_4) * bigInt

bi_100 : Integer
bi_100 = (cast {to=Integer} f_100) * bigInt

bi_50 : Integer
bi_50 = (cast {to=Integer} f_50) * bigInt

outNormal : Cast a Felt => a -> Cairo ()
outNormal = output . cast

outScaled : Cast Integer Felt => Integer -> Cairo ()
outScaled b = outNormal (b `div` bigInt)

outSuperScaled : Cast Integer Felt => Integer -> Cairo ()
outSuperScaled b = outNormal (b `div` (bigInt*bigInt))

%noinline
main : Cairo ()
main = do
  outNormal $ bigInt

  outNormal $ assert_total $ bi_3 `div` (2*bigInt)
  outScaled $ assert_total $ bi_3 `mod` (2*bigInt)
  outNormal $ assert_total $ bi_3 `mod` (2*bigInt)

  outNormal $ assert_total $ (-bi_3) `div` ((-2)*bigInt)
  outScaled $ assert_total $ (-bi_3) `mod` ((-2)*bigInt)
  outNormal $ assert_total $ (-bi_3) `mod` ((-2)*bigInt)

  outNormal $ assert_total $ (-bi_3) `div` (2*bigInt)
  outScaled $ assert_total $ (-bi_3) `mod` (2*bigInt)
  outNormal $ assert_total $ (-bi_3) `mod` (2*bigInt)

  outNormal $ assert_total $ bi_3 `div` ((-2)*bigInt)
  outScaled $ assert_total $ bi_3 `mod` ((-2)*bigInt)
  outNormal $ assert_total $ bi_3 `mod` ((-2)*bigInt)

  outNormal $ assert_total $ bi_4 `div` (2*bigInt)
  outScaled $ assert_total $ bi_4 `mod` (2*bigInt)
  outNormal $ assert_total $ bi_4 `mod` (2*bigInt)

  outNormal $ assert_total $ (-bi_4) `div` ((-2)*bigInt)
  outScaled $ assert_total $ (-bi_4) `mod` ((-2)*bigInt)
  outNormal $ assert_total $ (-bi_4) `mod` ((-2)*bigInt)

  outNormal $ assert_total $ (-bi_4) `div` (2*bigInt)
  outScaled $ assert_total $ (-bi_4) `mod` (2*bigInt)
  outNormal $ assert_total $ (-bi_4) `mod` (2*bigInt)

  outNormal $ assert_total $ bi_4 `div` ((-2)*bigInt)
  outScaled $ assert_total $ bi_4 `mod` ((-2)*bigInt)
  outNormal $ assert_total $ bi_4 `mod` ((-2)*bigInt)

  outScaled $ bi_100 + bi_50
  outScaled $ bi_100 - bi_50
  outSuperScaled $ bi_100 * bi_50
  outScaled $ -bi_50

  outNormal $ bi_100 + bi_50
  outNormal $ bi_100 - bi_50
  outScaled $ bi_100 * bi_50
  outNormal $ -bi_50

  outNormal $ bi_100 < bi_50
  outNormal $ bi_100 <= bi_50
  outNormal $ bi_100 == bi_50
  outNormal $ bi_100 >= bi_50
  outNormal $ bi_100 > bi_50
