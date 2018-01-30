> module Data.Bit

> import Data.Vect

**TODO**: Describe `Bit`s and `Word`s.

> public export
> data Bit : Type where
>   O : Bit
>   I : Bit

> ||| A binary word is a vector of bits.
> public export
> Word : Nat -> Type
> Word n = Vect n Bit