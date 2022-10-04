module Main
import Data.Bits

boolToInteger : Bool -> Integer
boolToInteger True = 1
boolToInteger False = 0

main : IO ()
main = do
  putStrLn . show $ (the Integer 3) `div` (the Integer 2)
  putStrLn . show $ (the Integer 3) `mod` (the Integer 2)

  putStrLn . show $ (the Integer (-3)) `div` (the Integer (-2))
  putStrLn . show $ (the Integer (-3)) `mod` (the Integer (-2))

  putStrLn . show $ (the Integer (-3)) `div` (the Integer (2))
  putStrLn . show $ (the Integer (-3)) `mod` (the Integer (2))

  putStrLn . show $ (the Integer (3)) `div` (the Integer (-2))
  putStrLn . show $ (the Integer (3)) `mod` (the Integer (-2))

  putStrLn . show $ (the Integer 4) `div` (the Integer 2)
  putStrLn . show $ (the Integer 4) `mod` (the Integer 2)

  putStrLn . show $ (the Integer (-4)) `div` (the Integer (-2))
  putStrLn . show $ (the Integer (-4)) `mod` (the Integer (-2))

  putStrLn . show $ (the Integer (-4)) `div` (the Integer (2))
  putStrLn . show $ (the Integer (-4)) `mod` (the Integer (2))

  putStrLn . show $ (the Integer (4)) `div` (the Integer (-2))
  putStrLn . show $ (the Integer (4)) `mod` (the Integer (-2))

  putStrLn . show $ (the Integer 100) + (the Integer 50)
  putStrLn . show $ (the Integer 100) - (the Integer 50)
  putStrLn . show $ (the Integer 100) * (the Integer 50)
  putStrLn . show $ (the Integer 100) `div` (the Integer 7)
  putStrLn . show $ (the Integer 100) `mod` (the Integer 7)
  putStrLn . show $ -(the Integer 50)

  -- bitwise ops not yet supported
  -- putStrLn . show $ the Integer 100 .&. the Integer 50
  -- putStrLn . show $ the Integer 100 .|. the Integer 50
  -- putStrLn . show $ the Integer 100 `xor` the Integer 50
  -- putStrLn . show $ the Integer 50 `shiftL` 1
  -- putStrLn . show $ the Integer 100 `shiftR` 1

  putStrLn . show . boolToInteger $ the Integer 100 < the Integer 50
  putStrLn . show . boolToInteger $ the Integer 100 <= the Integer 50
  putStrLn . show . boolToInteger $ the Integer 100 == the Integer 50
  putStrLn . show . boolToInteger $ the Integer 100 >= the Integer 50
  putStrLn . show . boolToInteger $ the Integer 100 > the Integer 50


  
