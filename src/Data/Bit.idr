module Data.Bit

import Data.Vect
import Data.Primitives.Views

import Data.Prim

%access export

-- **TODO**: Describe `Bit`s and `Word`s.

public export
data Bit : Type where
  O : Bit
  I : Bit

||| A binary word is a vector of bits.
public export
Word : Nat -> Type
Word n = Vect n Bit

intBitsRev : Int -> List Bit
intBitsRev 0 = []
intBitsRev i with (divides i 2)
  intBits (2*j+b) | DivBy _ = (if b==0 then O else I) :: intBitsRev j

pad16 : List Bit -> List Bit
pad16 xs = let l = length xs in 
           if l < 16 then replicate (16 `minus` l) O ++ xs else xs

charToBits : Char -> List Bit
charToBits = pad16 . reverse . intBitsRev . ord

toBits : String -> List Bit
toBits s with (strM s)
  toBits "" | StrNil = []
  toBits (strCons c s') | StrCons c s' = charToBits c ++ toBits s'