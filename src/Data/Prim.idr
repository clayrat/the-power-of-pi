module Data.Prim

import Data.Vect

%access export

charEqRefl : (a : Char) -> a == a = True
charEqRefl a = really_believe_me a

strConsS : (c : Char) -> (s : String) -> length (strCons c s) = S (length s)
strConsS c s = really_believe_me ()

v : (s : String) -> Vect (length s) Char
v s with (strM s)
  v ""             | StrNil = []
  v (strCons c xs) | StrCons c xs = rewrite strConsS c xs in c :: v xs