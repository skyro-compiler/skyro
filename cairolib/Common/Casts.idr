module Common.Casts

import Common.Felt

public export
interface LosslessCast a b where
    lossless_cast : a -> b

public export %inline
(lc:LosslessCast a b) => Cast a b where
    cast = lossless_cast @{lc}

-- Casts to Felt
%extern prim__cast_Int_to_Felt : Int -> Felt
public export %inline LosslessCast Int Felt where lossless_cast = prim__cast_Int_to_Felt

%extern prim__cast_Int8_to_Felt : Int8 -> Felt
public export %inline LosslessCast Int8 Felt where lossless_cast = prim__cast_Int8_to_Felt

%extern prim__cast_Int16_to_Felt : Int16 -> Felt
public export %inline LosslessCast Int16 Felt where lossless_cast = prim__cast_Int16_to_Felt

%extern prim__cast_Int32_to_Felt : Int32 -> Felt
public export %inline LosslessCast Int32 Felt where lossless_cast = prim__cast_Int32_to_Felt

%extern prim__cast_Int64_to_Felt : Int64 -> Felt
public export %inline LosslessCast Int64 Felt where lossless_cast = prim__cast_Int64_to_Felt

%extern prim__cast_Integer_to_Felt : Integer -> Felt
public export %inline Cast Integer Felt where cast = prim__cast_Integer_to_Felt
public export %inline Cast Nat Felt where cast f = prim__cast_Integer_to_Felt (believe_me f)

%extern prim__cast_Bits8_to_Felt : Bits8 -> Felt
public export %inline LosslessCast Bits8 Felt where lossless_cast = prim__cast_Bits8_to_Felt

%extern prim__cast_Bits16_to_Felt : Bits16 -> Felt
public export %inline LosslessCast Bits16 Felt where lossless_cast = prim__cast_Bits16_to_Felt

%extern prim__cast_Bits32_to_Felt : Bits32 -> Felt
public export %inline LosslessCast Bits32 Felt where lossless_cast = prim__cast_Bits32_to_Felt

%extern prim__cast_Bits64_to_Felt : Bits64 -> Felt
public export %inline LosslessCast Bits64 Felt where lossless_cast = prim__cast_Bits64_to_Felt


-- Casts to Int
%extern prim__cast_Felt_to_Int : Felt -> Int
public export %inline Cast Felt Int where cast = prim__cast_Felt_to_Int

%extern prim__cast_Int_to_Int : Int -> Int
public export %inline LosslessCast Int Int where lossless_cast = prim__cast_Int_to_Int

%extern prim__cast_Int8_to_Int : Int8 -> Int
public export %inline LosslessCast Int8 Int where lossless_cast = prim__cast_Int8_to_Int

%extern prim__cast_Int16_to_Int : Int16 -> Int
public export %inline LosslessCast Int16 Int where lossless_cast = prim__cast_Int16_to_Int

%extern prim__cast_Int32_to_Int : Int32 -> Int
public export %inline LosslessCast Int32 Int where lossless_cast = prim__cast_Int32_to_Int

%extern prim__cast_Int64_to_Int : Int64 -> Int
public export %inline LosslessCast Int64 Int where lossless_cast = prim__cast_Int64_to_Int

%extern prim__cast_Integer_to_Int : Integer -> Int
public export %inline Cast Integer Int where cast = prim__cast_Integer_to_Int
public export %inline Cast Nat Int where cast f = prim__cast_Integer_to_Int (believe_me f)

%extern prim__cast_Bits8_to_Int : Bits8 -> Int
public export %inline LosslessCast Bits8 Int where lossless_cast = prim__cast_Bits8_to_Int

%extern prim__cast_Bits16_to_Int : Bits16 -> Int
public export %inline LosslessCast Bits16 Int where lossless_cast = prim__cast_Bits16_to_Int

%extern prim__cast_Bits32_to_Int : Bits32 -> Int
public export %inline LosslessCast Bits32 Int where lossless_cast = prim__cast_Bits32_to_Int

%extern prim__cast_Bits64_to_Int : Bits64 -> Int
public export %inline Cast Bits64 Int where cast = prim__cast_Bits64_to_Int


-- Casts to Int8
%extern prim__cast_Felt_to_Int8 : Felt -> Int8
public export %inline Cast Felt Int8 where cast = prim__cast_Felt_to_Int8

%extern prim__cast_Int_to_Int8 : Int -> Int8
public export %inline Cast Int Int8 where cast = prim__cast_Int_to_Int8

%extern prim__cast_Int8_to_Int8 : Int8 -> Int8
public export %inline LosslessCast Int8 Int8 where lossless_cast = prim__cast_Int8_to_Int8

%extern prim__cast_Int16_to_Int8 : Int16 -> Int8
public export %inline Cast Int16 Int8 where cast = prim__cast_Int16_to_Int8

%extern prim__cast_Int32_to_Int8 : Int32 -> Int8
public export %inline Cast Int32 Int8 where cast = prim__cast_Int32_to_Int8

%extern prim__cast_Int64_to_Int8 : Int64 -> Int8
public export %inline Cast Int64 Int8 where cast = prim__cast_Int64_to_Int8

%extern prim__cast_Integer_to_Int8 : Integer -> Int8
public export %inline Cast Integer Int8 where cast = prim__cast_Integer_to_Int8
public export %inline Cast Nat Int8 where cast f = prim__cast_Integer_to_Int8 (believe_me f)

%extern prim__cast_Bits8_to_Int8 : Bits8 -> Int8
public export %inline Cast Bits8 Int8 where cast = prim__cast_Bits8_to_Int8

%extern prim__cast_Bits16_to_Int8 : Bits16 -> Int8
public export %inline Cast Bits16 Int8 where cast = prim__cast_Bits16_to_Int8

%extern prim__cast_Bits32_to_Int8 : Bits32 -> Int8
public export %inline Cast Bits32 Int8 where cast = prim__cast_Bits32_to_Int8

%extern prim__cast_Bits64_to_Int8 : Bits64 -> Int8
public export %inline Cast Bits64 Int8 where cast = prim__cast_Bits64_to_Int8


-- Casts to Int16
%extern prim__cast_Felt_to_Int16 : Felt -> Int16
public export %inline Cast Felt Int16 where cast = prim__cast_Felt_to_Int16

%extern prim__cast_Int_to_Int16 : Int -> Int16
public export %inline Cast Int Int16 where cast = prim__cast_Int_to_Int16

%extern prim__cast_Int8_to_Int16 : Int8 -> Int16
public export %inline LosslessCast Int8 Int16 where lossless_cast = prim__cast_Int8_to_Int16

%extern prim__cast_Int16_to_Int16 : Int16 -> Int16
public export %inline LosslessCast Int16 Int16 where lossless_cast = prim__cast_Int16_to_Int16

%extern prim__cast_Int32_to_Int16 : Int32 -> Int16
public export %inline Cast Int32 Int16 where cast = prim__cast_Int32_to_Int16

%extern prim__cast_Int64_to_Int16 : Int64 -> Int16
public export %inline Cast Int64 Int16  where cast = prim__cast_Int64_to_Int16

%extern prim__cast_Integer_to_Int16 : Integer -> Int16
public export %inline Cast Integer Int16  where cast = prim__cast_Integer_to_Int16
public export %inline Cast Nat Int16  where cast f = prim__cast_Integer_to_Int16 (believe_me f)

%extern prim__cast_Bits8_to_Int16 : Bits8 -> Int16
public export %inline LosslessCast Bits8 Int16 where lossless_cast = prim__cast_Bits8_to_Int16

%extern prim__cast_Bits16_to_Int16 : Bits16 -> Int16
public export %inline Cast Bits16 Int16 where cast = prim__cast_Bits16_to_Int16

%extern prim__cast_Bits32_to_Int16 : Bits32 -> Int16
public export %inline Cast Bits32 Int16 where cast = prim__cast_Bits32_to_Int16

%extern prim__cast_Bits64_to_Int16 : Bits64 -> Int16
public export %inline Cast Bits64 Int16 where cast = prim__cast_Bits64_to_Int16


-- Casts to Int32
%extern prim__cast_Felt_to_Int32 : Felt -> Int32
public export %inline Cast Felt Int32 where cast = prim__cast_Felt_to_Int32

%extern prim__cast_Int_to_Int32 : Int -> Int32
public export %inline Cast Int Int32 where cast = prim__cast_Int_to_Int32

%extern prim__cast_Int8_to_Int32 : Int8 -> Int32
public export %inline LosslessCast Int8 Int32 where lossless_cast = prim__cast_Int8_to_Int32

%extern prim__cast_Int16_to_Int32 : Int16 -> Int32
public export %inline LosslessCast Int16 Int32 where lossless_cast = prim__cast_Int16_to_Int32

%extern prim__cast_Int32_to_Int32 : Int32-> Int32
public export %inline LosslessCast Int32 Int32 where lossless_cast = prim__cast_Int32_to_Int32

%extern prim__cast_Int64_to_Int32 : Int64 -> Int32
public export %inline Cast Int64 Int32 where cast = prim__cast_Int64_to_Int32

%extern prim__cast_Integer_to_Int32 : Integer -> Int32
public export %inline Cast Integer Int32 where cast = prim__cast_Integer_to_Int32
public export %inline Cast Nat Int32 where cast f = prim__cast_Integer_to_Int32 (believe_me f)

%extern prim__cast_Bits8_to_Int32 : Bits8 -> Int32
public export %inline LosslessCast Bits8 Int32 where lossless_cast = prim__cast_Bits8_to_Int32

%extern prim__cast_Bits16_to_Int32 : Bits16 -> Int32
public export %inline LosslessCast Bits16 Int32 where lossless_cast = prim__cast_Bits16_to_Int32

%extern prim__cast_Bits32_to_Int32 : Bits32 -> Int32
public export %inline Cast Bits32 Int32 where cast = prim__cast_Bits32_to_Int32

%extern prim__cast_Bits64_to_Int32 : Bits64 -> Int32
public export %inline Cast Bits64 Int32 where cast = prim__cast_Bits64_to_Int32


-- Casts to Int64
%extern prim__cast_Felt_to_Int64 : Felt -> Int64
public export %inline Cast Felt Int64 where cast = prim__cast_Felt_to_Int64

%extern prim__cast_Int_to_Int64 : Int -> Int64
public export %inline LosslessCast Int Int64 where lossless_cast = prim__cast_Int_to_Int64

%extern prim__cast_Int8_to_Int64 : Int8 -> Int64
public export %inline LosslessCast Int8 Int64 where lossless_cast = prim__cast_Int8_to_Int64

%extern prim__cast_Int16_to_Int64 : Int16 -> Int64
public export %inline LosslessCast Int16 Int64 where lossless_cast = prim__cast_Int16_to_Int64

%extern prim__cast_Int32_to_Int64 : Int32 -> Int64
public export %inline LosslessCast Int32 Int64 where lossless_cast = prim__cast_Int32_to_Int64

%extern prim__cast_Int64_to_Int64 : Int64 -> Int64
public export %inline LosslessCast Int64 Int64 where lossless_cast = prim__cast_Int64_to_Int64

%extern prim__cast_Integer_to_Int64 : Integer -> Int64
public export %inline Cast Integer Int64 where cast = prim__cast_Integer_to_Int64
public export %inline Cast Nat Int64 where cast f = prim__cast_Integer_to_Int64 (believe_me f)

%extern prim__cast_Bits8_to_Int64 : Bits8 -> Int64
public export %inline LosslessCast Bits8 Int64 where lossless_cast = prim__cast_Bits8_to_Int64

%extern prim__cast_Bits16_to_Int64 : Bits16 -> Int64
public export %inline LosslessCast Bits16 Int64 where lossless_cast = prim__cast_Bits16_to_Int64

%extern prim__cast_Bits32_to_Int64 : Bits32 -> Int64
public export %inline LosslessCast Bits32 Int64 where lossless_cast = prim__cast_Bits32_to_Int64

%extern prim__cast_Bits64_to_Int64 : Bits64 -> Int64
public export %inline Cast Bits64 Int64 where cast = prim__cast_Bits64_to_Int64


-- Casts to Integer
%extern prim__cast_Felt_to_Integer : Felt -> Integer
public export %inline LosslessCast Felt Integer where lossless_cast = prim__cast_Felt_to_Integer

%extern prim__cast_Int_to_Integer : Int -> Integer
public export %inline LosslessCast Int Integer where lossless_cast = prim__cast_Int_to_Integer

%extern prim__cast_Int8_to_Integer : Int8 -> Integer
public export %inline LosslessCast Int8 Integer where lossless_cast = prim__cast_Int8_to_Integer

%extern prim__cast_Int16_to_Integer : Int16 -> Integer
public export %inline LosslessCast Int16 Integer where lossless_cast = prim__cast_Int16_to_Integer

%extern prim__cast_Int32_to_Integer : Int32 -> Integer
public export %inline LosslessCast Int32 Integer where lossless_cast = prim__cast_Int32_to_Integer

%extern prim__cast_Int64_to_Integer : Int64 -> Integer
public export %inline LosslessCast Int64 Integer where lossless_cast = prim__cast_Int64_to_Integer

%extern prim__cast_Integer_to_Integer : Integer -> Integer
public export %inline LosslessCast Integer Integer where lossless_cast = prim__cast_Integer_to_Integer
public export %inline LosslessCast Nat Integer where lossless_cast f = prim__cast_Integer_to_Integer (believe_me f)

%extern prim__cast_Bits8_to_Integer : Bits8 -> Integer
public export %inline LosslessCast Bits8 Integer where lossless_cast = prim__cast_Bits8_to_Integer

%extern prim__cast_Bits16_to_Integer : Bits16 -> Integer
public export %inline LosslessCast Bits16 Integer where lossless_cast = prim__cast_Bits16_to_Integer

%extern prim__cast_Bits32_to_Integer : Bits32 -> Integer
public export %inline LosslessCast Bits32 Integer where lossless_cast = prim__cast_Bits32_to_Integer

%extern prim__cast_Bits64_to_Integer : Bits64 -> Integer
public export %inline LosslessCast Bits64 Integer where lossless_cast = prim__cast_Bits64_to_Integer

-- Casts to Nat
public export %inline Cast Felt Nat where cast f = believe_me $ prim__cast_Felt_to_Integer f
public export %inline Cast Int Nat where cast f = believe_me $ prim__cast_Int_to_Integer f
public export %inline Cast Int8 Nat where cast f = believe_me $ prim__cast_Int8_to_Integer f
public export %inline Cast Int16 Nat where cast f = believe_me $ prim__cast_Int16_to_Integer f
public export %inline Cast Int32 Nat where cast f = believe_me $ prim__cast_Int32_to_Integer f
public export %inline Cast Int64 Nat where cast f = believe_me $ prim__cast_Int64_to_Integer f
public export %inline Cast Integer Nat where cast f = believe_me $ prim__cast_Integer_to_Integer f
public export %inline LosslessCast Nat Nat where lossless_cast f = believe_me $ prim__cast_Integer_to_Integer (believe_me f)
public export %inline LosslessCast Bits8 Nat where lossless_cast f = believe_me $ prim__cast_Bits8_to_Integer f
public export %inline LosslessCast Bits16 Nat where lossless_cast f = believe_me $ prim__cast_Bits16_to_Integer f
public export %inline LosslessCast Bits32 Nat where lossless_cast f = believe_me $ prim__cast_Bits32_to_Integer f
public export %inline LosslessCast Bits64 Nat where lossless_cast f = believe_me $ prim__cast_Bits64_to_Integer f

-- Casts to Bits8
%extern prim__cast_Felt_to_Bits8 : Felt -> Bits8
public export %inline Cast Felt Bits8 where cast = prim__cast_Felt_to_Bits8

%extern prim__cast_Int_to_Bits8 : Int -> Bits8
public export %inline Cast Int Bits8 where cast = prim__cast_Int_to_Bits8

%extern prim__cast_Int8_to_Bits8 : Int8 -> Bits8
public export %inline Cast Int8 Bits8 where cast = prim__cast_Int8_to_Bits8

%extern prim__cast_Int16_to_Bits8 : Int16 -> Bits8
public export %inline Cast Int16 Bits8 where cast = prim__cast_Int16_to_Bits8

%extern prim__cast_Int32_to_Bits8 : Int32 -> Bits8
public export %inline Cast Int32 Bits8 where cast = prim__cast_Int32_to_Bits8

%extern prim__cast_Int64_to_Bits8 : Int64 -> Bits8
public export %inline Cast Int64 Bits8 where cast = prim__cast_Int64_to_Bits8

%extern prim__cast_Integer_to_Bits8 : Integer -> Bits8
public export %inline Cast Integer Bits8 where cast = prim__cast_Integer_to_Bits8
public export %inline Cast Nat Bits8 where cast f = prim__cast_Integer_to_Bits8 (believe_me f)

%extern prim__cast_Bits8_to_Bits8 : Bits8 -> Bits8
public export %inline LosslessCast Bits8 Bits8 where lossless_cast = prim__cast_Bits8_to_Bits8

%extern prim__cast_Bits16_to_Bits8 : Bits16 -> Bits8
public export %inline Cast Bits16 Bits8 where cast = prim__cast_Bits16_to_Bits8

%extern prim__cast_Bits32_to_Bits8 : Bits32 -> Bits8
public export %inline Cast Bits32 Bits8 where cast = prim__cast_Bits32_to_Bits8

%extern prim__cast_Bits64_to_Bits8 : Bits64 -> Bits8
public export %inline Cast Bits64 Bits8 where cast = prim__cast_Bits64_to_Bits8

-- Casts to Bits16
%extern prim__cast_Felt_to_Bits16 : Felt -> Bits16
public export %inline Cast Felt Bits16 where cast = prim__cast_Felt_to_Bits16

%extern prim__cast_Int_to_Bits16 : Int -> Bits16
public export %inline Cast Int Bits16 where cast = prim__cast_Int_to_Bits16

%extern prim__cast_Int8_to_Bits16 : Int8 -> Bits16
public export %inline Cast Int8 Bits16 where cast = prim__cast_Int8_to_Bits16

%extern prim__cast_Int16_to_Bits16 : Int16 -> Bits16
public export %inline Cast Int16 Bits16 where cast = prim__cast_Int16_to_Bits16

%extern prim__cast_Int32_to_Bits16 : Int32 -> Bits16
public export %inline Cast Int32 Bits16 where cast = prim__cast_Int32_to_Bits16

%extern prim__cast_Int64_to_Bits16 : Int64 -> Bits16
public export %inline Cast Int64 Bits16 where cast = prim__cast_Int64_to_Bits16

%extern prim__cast_Integer_to_Bits16 : Integer -> Bits16
public export %inline Cast Integer Bits16 where cast = prim__cast_Integer_to_Bits16
public export %inline Cast Nat Bits16 where cast f = prim__cast_Integer_to_Bits16 (believe_me f)

%extern prim__cast_Bits8_to_Bits16 : Bits8 -> Bits16
public export %inline LosslessCast Bits8 Bits16 where lossless_cast = prim__cast_Bits8_to_Bits16

%extern prim__cast_Bits16_to_Bits16 : Bits16 -> Bits16
public export %inline LosslessCast Bits16 Bits16 where lossless_cast = prim__cast_Bits16_to_Bits16

%extern prim__cast_Bits32_to_Bits16 : Bits32 -> Bits16
public export %inline Cast Bits32 Bits16 where cast = prim__cast_Bits32_to_Bits16

%extern prim__cast_Bits64_to_Bits16 : Bits64 -> Bits16
public export %inline Cast Bits64 Bits16 where cast = prim__cast_Bits64_to_Bits16

-- Casts to Bits32
%extern prim__cast_Felt_to_Bits32 : Felt -> Bits32
public export %inline Cast Felt Bits32 where cast = prim__cast_Felt_to_Bits32

%extern prim__cast_Int_to_Bits32 : Int -> Bits32
public export %inline Cast Int Bits32 where cast = prim__cast_Int_to_Bits32

%extern prim__cast_Int8_to_Bits32 : Int8 -> Bits32
public export %inline Cast Int8 Bits32 where cast = prim__cast_Int8_to_Bits32

%extern prim__cast_Int16_to_Bits32 : Int16 -> Bits32
public export %inline Cast Int16 Bits32 where cast = prim__cast_Int16_to_Bits32

%extern prim__cast_Int32_to_Bits32 : Int32 -> Bits32
public export %inline Cast Int32 Bits32 where cast = prim__cast_Int32_to_Bits32

%extern prim__cast_Int64_to_Bits32 : Int64 -> Bits32
public export %inline Cast Int64 Bits32 where cast = prim__cast_Int64_to_Bits32

%extern prim__cast_Integer_to_Bits32 : Integer -> Bits32
public export %inline Cast Integer Bits32 where cast = prim__cast_Integer_to_Bits32
public export %inline Cast Nat Bits32 where cast f = prim__cast_Integer_to_Bits32 (believe_me f)

%extern prim__cast_Bits8_to_Bits32 : Bits8 -> Bits32
public export %inline LosslessCast Bits8 Bits32 where lossless_cast = prim__cast_Bits8_to_Bits32

%extern prim__cast_Bits16_to_Bits32 : Bits16 -> Bits32
public export %inline LosslessCast Bits16 Bits32 where lossless_cast = prim__cast_Bits16_to_Bits32

%extern prim__cast_Bits32_to_Bits32 : Bits32 -> Bits32
public export %inline LosslessCast Bits32 Bits32 where lossless_cast = prim__cast_Bits32_to_Bits32

%extern prim__cast_Bits64_to_Bits32 : Bits64 -> Bits32
public export %inline Cast Bits64 Bits32 where cast = prim__cast_Bits64_to_Bits32

-- Casts to Bits64
%extern prim__cast_Felt_to_Bits64 : Felt -> Bits64
public export %inline Cast Felt Bits64 where cast = prim__cast_Felt_to_Bits64

%extern prim__cast_Int_to_Bits64 : Int -> Bits64
public export %inline Cast Int Bits64 where cast = prim__cast_Int_to_Bits64

%extern prim__cast_Int8_to_Bits64 : Int8 -> Bits64
public export %inline Cast Int8 Bits64 where cast = prim__cast_Int8_to_Bits64

%extern prim__cast_Int16_to_Bits64 : Int16 -> Bits64
public export %inline Cast Int16 Bits64 where cast = prim__cast_Int16_to_Bits64

%extern prim__cast_Int32_to_Bits64 : Int32 -> Bits64
public export %inline Cast Int32 Bits64 where cast = prim__cast_Int32_to_Bits64

%extern prim__cast_Int64_to_Bits64 : Int64 -> Bits64
public export %inline Cast Int64 Bits64 where cast = prim__cast_Int64_to_Bits64

%extern prim__cast_Integer_to_Bits64 : Integer -> Bits64
public export %inline Cast Integer Bits64 where cast = prim__cast_Integer_to_Bits64
public export %inline Cast Nat Bits64 where cast f = prim__cast_Integer_to_Bits64 (believe_me f)

%extern prim__cast_Bits8_to_Bits64 : Bits8 -> Bits64
public export %inline LosslessCast Bits8 Bits64 where lossless_cast = prim__cast_Bits8_to_Bits64

%extern prim__cast_Bits16_to_Bits64 : Bits16 -> Bits64
public export %inline LosslessCast Bits16 Bits64 where lossless_cast = prim__cast_Bits16_to_Bits64

%extern prim__cast_Bits32_to_Bits64 : Bits32 -> Bits64
public export %inline LosslessCast Bits32 Bits64 where lossless_cast = prim__cast_Bits32_to_Bits64

%extern prim__cast_Bits64_to_Bits64 : Bits64 -> Bits64
public export %inline LosslessCast Bits64 Bits64 where lossless_cast = prim__cast_Bits64_to_Bits64
