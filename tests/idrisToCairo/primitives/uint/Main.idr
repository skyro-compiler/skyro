module Main

import Cairo
import Data.Bits

-- The following functions are required to avoid that the constantfolder
-- evaluates the expressions at compile time.
-- Maybe we should disable the constantfolder and write the tests more direct.

%foreign 
  """
  code:
  func Main_f_200() -> (r):
      return (200)
  end
  """
f_200 : Felt

%foreign 
  """
  code:
  func Main_f_100() -> (r):
      return (100)
  end
  """
f_100 : Felt

u_200 : Bits8
u_200 = cast {to=Bits8} f_200

u_100 : Bits8
u_100 = cast {to=Bits8} f_100

out : Cast a Felt => a -> Cairo ()
out = output . cast


%noinline
main : Cairo ()
main = do
  out $ u_200 + u_100
  out $ u_200 - u_100
  out $ u_200 * u_100
  -- BUG, this returns 0!!!
  -- Patternmachting on felt famously does not work. 
  -- Best would be to make it work - otherwise throw an error at compile time or at least crash at runtime.
  -- out $ case b of 0 => 0 ; x => (cast {to=Bits8} a) `div` (cast {to=Bits8} x)
  out $ assert_total $ u_200 `div` 7
  out $ assert_total $ u_200 `mod` 7
  out $ - u_100
  out $ u_200 .&. u_100
  out $ u_200 .|. u_100 
  out $ u_200 `xor` u_100
  out $ u_200 < u_100
  out $ u_200 <= u_100
  out $ u_200 == u_100
  out $ u_200 >= u_100
  out $ u_200 > u_100
  -- out $ u_100 `shiftL` 1 -- Index is of type Nat. Not implemented yet
  -- out $ u_100 `shiftR` 1