module Main
import Data.Bits

boolToInt : Bool -> Int
boolToInt True = 1
boolToInt False = 0

main : IO ()
main = do
  putStrLn . show $ (the Int8 3) `div` (the Int8 2)
  putStrLn . show $ (the Int8 3) `mod` (the Int8 2)

  putStrLn . show $ (the Int8 (-3)) `div` (the Int8 (-2))
  putStrLn . show $ (the Int8 (-3)) `mod` (the Int8 (-2))

  putStrLn . show $ (the Int8 (-3)) `div` (the Int8 (2))
  putStrLn . show $ (the Int8 (-3)) `mod` (the Int8 (2))

  putStrLn . show $ (the Int8 (3)) `div` (the Int8 (-2))
  putStrLn . show $ (the Int8 (3)) `mod` (the Int8 (-2))

  putStrLn . show $ (the Int8 4) `div` (the Int8 2)
  putStrLn . show $ (the Int8 4) `mod` (the Int8 2)

  putStrLn . show $ (the Int8 (-4)) `div` (the Int8 (-2))
  putStrLn . show $ (the Int8 (-4)) `mod` (the Int8 (-2))

  putStrLn . show $ (the Int8 (-4)) `div` (the Int8 (2))
  putStrLn . show $ (the Int8 (-4)) `mod` (the Int8 (2))

  putStrLn . show $ (the Int8 (4)) `div` (the Int8 (-2))
  putStrLn . show $ (the Int8 (4)) `mod` (the Int8 (-2))

  putStrLn . show $ (the Int8 100) + (the Int8 50) 
  putStrLn . show $ (the Int8 100) - (the Int8 50)
  putStrLn . show $ (the Int8 100) * (the Int8 50)
  putStrLn . show $ (the Int8 100) `div` (the Int8 7)
  putStrLn . show $ (the Int8 100) `mod` (the Int8 7)
  putStrLn . show $ -(the Int8 50)
  
  putStrLn . show $ the Int8 100 .&. the Int8 50
  putStrLn . show $ the Int8 100 .|. the Int8 50
  putStrLn . show $ the Int8 100 `xor` the Int8 50
  putStrLn . show  $ the Int8 50 `shiftL` 1
  putStrLn . show  $ the Int8 100 `shiftR` 1

  putStrLn . show . boolToInt $ the Int8 100 < the Int8 50
  putStrLn . show . boolToInt $ the Int8 100 <= the Int8 50
  putStrLn . show . boolToInt $ the Int8 100 == the Int8 50
  putStrLn . show . boolToInt $ the Int8 100 >= the Int8 50
  putStrLn . show . boolToInt $ the Int8 100 > the Int8 50

  
