module Data.U

import Data.Vect 

import Data.Bit

%access public export

data U : Type where
  BIT : U
  CHAR : U
  NAT : U
  VECT : Nat -> U -> U

Eq U where
  BIT         == BIT  = True
  CHAR        == CHAR = True
  NAT         == NAT  = True
  (VECT n u1) == (VECT m u2) = n == m && u1 == u2
  _           == _    = False

el : U -> Type
el BIT        = Bit
el CHAR       = Char
el NAT        = Nat
el (VECT n u) = Vect n (el u)