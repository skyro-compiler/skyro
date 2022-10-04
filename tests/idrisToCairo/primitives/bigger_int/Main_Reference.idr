module Main
import Data.Bits

boolToInteger : Bool -> Integer
boolToInteger True = 1
boolToInteger False = 0

bigInt : Integer
bigInt = 1361129467683753853853498429727072845824 -- 2^130

showNormal : Integer -> IO ()
showNormal = putStrLn . show

showScaled : Integer -> IO ()
showScaled b = putStrLn . show $ b `div` (bigInt)

showSuperScaled : Integer -> IO ()
showSuperScaled b = putStrLn . show $ b `div` (bigInt*bigInt)

main : IO ()
main = do
  showNormal $ bigInt

  showNormal $ (3*bigInt) `div` (2*bigInt)
  showScaled $ (3*bigInt) `mod` (2*bigInt)
  showNormal $ (3*bigInt) `mod` (2*bigInt)

  showNormal $ ((-3)*bigInt) `div` ((-2)*bigInt)
  showScaled $ ((-3)*bigInt) `mod` ((-2)*bigInt)
  showNormal $ ((-3)*bigInt) `mod` ((-2)*bigInt)

  showNormal $ ((-3)*bigInt) `div` (2*bigInt)
  showScaled $ ((-3)*bigInt) `mod` (2*bigInt)
  showNormal $ ((-3)*bigInt) `mod` (2*bigInt)

  showNormal $ (3*bigInt) `div` ((-2)*bigInt)
  showScaled $ (3*bigInt) `mod` ((-2)*bigInt)
  showNormal $ (3*bigInt) `mod` ((-2)*bigInt)

  showNormal $ (4*bigInt) `div` (2*bigInt)
  showScaled $ (4*bigInt) `mod` (2*bigInt)
  showNormal $ (4*bigInt) `mod` (2*bigInt)

  showNormal $ ((-4)*bigInt) `div` ((-2)*bigInt)
  showScaled $ ((-4)*bigInt) `mod` ((-2)*bigInt)
  showNormal $ ((-4)*bigInt) `mod` ((-2)*bigInt)

  showNormal $ ((-4)*bigInt) `div` (2*bigInt)
  showScaled $ ((-4)*bigInt) `mod` (2*bigInt)
  showNormal $ ((-4)*bigInt) `mod` (2*bigInt)

  showNormal $ (4*bigInt) `div` ((-2)*bigInt)
  showScaled $ (4*bigInt) `mod` ((-2)*bigInt)
  showNormal $ (4*bigInt) `mod` ((-2)*bigInt)

  showScaled $ (100*bigInt) + (50*bigInt)
  showScaled $ (100*bigInt) - (50*bigInt)
  showSuperScaled $ (100*bigInt) * (50*bigInt)
  showScaled $ -(50*bigInt)

  showNormal $ (100*bigInt) + (50*bigInt)
  showNormal $ (100*bigInt) - (50*bigInt)
  showScaled $ (100*bigInt) * (50*bigInt)
  showNormal $ -(50*bigInt)

  putStrLn . show . boolToInteger $ (100*bigInt)  < (50*bigInt)
  putStrLn . show . boolToInteger $ (100*bigInt)  <= (50*bigInt)
  putStrLn . show . boolToInteger $ (100*bigInt)  == (50*bigInt)
  putStrLn . show . boolToInteger $ (100*bigInt)  >= (50*bigInt)
  putStrLn . show . boolToInteger $ (100*bigInt)  > (50*bigInt)


  
