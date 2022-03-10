module Main
import Data.Bits

boolToInt : Bool -> Int
boolToInt True = 1
boolToInt False = 0

main : IO ()
main = do
  putStrLn . show $ (the Bits8 200) + (the Bits8 100)
  putStrLn . show $ (the Bits8 200) - (the Bits8 100)
  putStrLn . show $ (the Bits8 200) * (the Bits8 100)
  putStrLn . show $ (the Bits8 200) `div` (the Bits8 7)
  putStrLn . show $ (the Bits8 200) `mod` (the Bits8 7)
  putStrLn . show $ -(the Bits8 100)
  putStrLn . show $ the Bits8 200 .&. the Bits8 100
  putStrLn . show $ the Bits8 200 .|. the Bits8 100
  putStrLn . show $ the Bits8 200 `xor` the Bits8 100
  putStrLn . show . boolToInt $ the Bits8 200 < the Bits8 100
  putStrLn . show . boolToInt $ the Bits8 200 <= the Bits8 100
  putStrLn . show . boolToInt $ the Bits8 200 == the Bits8 100
  putStrLn . show . boolToInt $ the Bits8 200 >= the Bits8 100
  putStrLn . show . boolToInt $ the Bits8 200 > the Bits8 100
  -- putStrLn . show  $ the Bits8 100 `shiftL` 1
  -- putStrLn . show  $ the Bits8 100 `shiftR` 1
  
