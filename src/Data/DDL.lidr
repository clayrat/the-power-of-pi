> module Data.DDL

> import Data.Bit
> import Data.Vect
> import Data.Primitives.Views

> public export
> data U : Type where
>   BIT : U
>   CHAR : U
>   NAT : U
>   VECT : Nat -> U -> U
>
> public export
> el : U -> Type
> el BIT        = Bit
> el CHAR       = Char
> el NAT        = Nat
> el (VECT n u) = Vect n (el u)

> parens : String -> String
> parens str = "(" ++ str ++ ")"

> export
> show : {u : U} -> el u -> String
> show {u = BIT} O       = "O"
> show {u = BIT} I       = "I"
> show {u = CHAR} c      = singleton c
> show {u = NAT} Z       = "Zero"
> show {u = NAT} (S k)   = "Succ " ++ parens (show {u = NAT} k)
> show {u = VECT Z a} [] = "Nil"
> show {u = VECT (S k) a} (x :: xs)
>   = parens (show {u = a} x) ++ " :: " ++ parens (show {u = VECT k a} xs)

> export
> read : (u : U) -> List Bit -> Maybe (el u, List Bit)
> read BIT        xs = MkPair <$> head' xs <*> tail' xs
> read CHAR       xs = if length xs < 16 then Nothing else         -- Idris' `Char`s are supposedly 2 bytes wide
>                      let (h, t) = splitAt 16 xs in
>                      do (n, []) <- read NAT h | _ => Nothing     -- TODO breaks totality
>                         pure (chr $ toIntNat n, t)
> read NAT        xs = Just (go xs Z, [])
>   where 
>   go : List Bit -> Nat -> Nat
>   go [] acc = acc
>   go (O::bs) acc = go bs (2*acc)
>   go (I::bs) acc = go bs (S (2*acc))
> read (VECT k x) xs = rewrite plusCommutative 0 k in go k x xs [] 
>   where
>   go : (n : Nat) -> (u : U) -> List Bit -> Vect m (el u) -> Maybe (Vect (n+m) (el u), List Bit)
>   go {m} Z _ xs acc = Just (reverse acc, xs)
>   go {m} (S k) u xs acc = case read u xs of 
>                             Nothing => Nothing
>                             Just (el,xs') => rewrite plusSuccRightSucc k m in go k u xs' (el :: acc)

> mutual
>   public export
>   data Format : Type where
>     Bad : Format
>     End : Format
>     Base : U -> Format
>     Plus : Format -> Format -> Format
>     Skip : (f : Format) -> Fmt f -> Format -> Format
>     Read : (f : Format) -> (Fmt f -> Format) -> Format

>   public export
>   Fmt : Format -> Type
>   Fmt Bad = Void
>   Fmt End = Unit
>   Fmt (Base u) = el u
>   Fmt (Plus f1 f2) = Either (Fmt f1) (Fmt f2)
>   Fmt (Read f1 f2) = (x : Fmt f1 ** Fmt (f2 x))
>   Fmt (Skip _ _ f) = Fmt f

=== Format combinators

> export
> char : Char -> Format
> char c = Read (Base CHAR) (\x => if c == x then End else Bad)

> export
> satisfy : (f : Format) -> (Fmt f -> Bool) -> Format
> satisfy f pred = Read f (\x => if pred x then End else Bad)

> charEqRefl : (a : Char) -> a == a = True
> charEqRefl a = really_believe_me a

> infixr 4 .>
> (.>) : Char -> Format -> Format
> c .> f = Skip (char c) (c ** rewrite charEqRefl c in ()) f

> (>>=) : (f : Format) -> (Fmt f -> Format) -> Format
> x >>= f = Read x f

> export
> pbm : Format
> pbm = 'P' .>
>       '4' .> 
>       ' ' .>
>       Base NAT >>= \n =>
>       ' ' .>
>       Base NAT >>= \m =>
>       '\n' .>
>       Base (VECT n (VECT m BIT)) >>= \bs =>
>       End

=== Generic parsers

> export
> parse : (f : Format) -> List Bit -> Maybe (Fmt f, List Bit)
> parse Bad bs       = Nothing
> parse End bs       = Just ((), bs)
> parse (Base u) bs  = read u bs
> parse (Plus f1 f2) bs with (parse f1 bs)
>   | Just (x, cs)   = Just (Left x, cs)
>   | Nothing with (parse f2 bs)
>     | Just (y, ds) = Just (Right y, ds)
>     | Nothing      = Nothing
> parse (Skip f1 _ f2) bs with (parse f1 bs)
>   | Nothing        = Nothing
>   | Just (_, cs)   = parse f2 cs
> parse (Read f1 f2) bs with (parse f1 bs)
>   | Nothing        = Nothing
>   | Just (x, cs) with (parse (f2 x) cs)
>     | Nothing      = Nothing
>     | Just (y, ds) = Just ((x ** y), ds)

> intBitsRev : Int -> List Bit
> intBitsRev 0 = []
> intBitsRev i with (divides i 2)
>   intBits (2*j+b) | DivBy _ = (if b==0 then O else I) :: intBitsRev j

> pad16 : List Bit -> List Bit
> pad16 xs = let l = length xs in 
>            if l < 16 then replicate (16 `minus` l) O ++ xs else xs

> charToBits : Char -> List Bit
> charToBits = pad16 . reverse . intBitsRev . ord

> toBits : String -> List Bit
> toBits s with (strM s)
>   toBits "" | StrNil = []
>   toBits (strCons c s') | StrCons c s' = charToBits c ++ toBits s'
 
> export
> print : (f : Format) -> Fmt f -> List Bit
> print  Bad           _         impossible
> print  End           ()        = []
> print (Base u)       x         = toBits (show {u} x)
> print (Plus f1 _ )   (Left x)  = print f1 x
> print (Plus _  f2)   (Right x) = print f2 x
> print (Skip f1 v f2) x         = print f1 v ++ print f2 x
> print (Read f1 f2)   (x ** y)  = print f1 x ++ print (f2 x) y



