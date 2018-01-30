module Data.DB

import Data.So
import Data.Vect

import Data.Bit
import Data.U
import Data.Prim

%access export
%language ElabReflection  

Attribute : Type
Attribute = (String, U)

Schema : Type
Schema = List Attribute

Cars : Schema
Cars = [("Model", VECT 20 CHAR)
       ,("Time" , VECT 6 CHAR)
       ,("Wet"  , BIT)                 -- BOOL in the paper :/
       ]

data Row : Schema -> Type where
  EmptyRow : Row []
  ConsRow : el u -> Row s -> Row ((name, u) :: s)

Table : Schema -> Type  
Table s = List (Row s)

zonda : Row Cars
zonda = ConsRow (v "Pagani Zonda C12 F  ") $ ConsRow (v "1:18.4") $ ConsRow O $ EmptyRow

Handle : Schema -> Type

ServerName : Type

TableName : Type

connect : ServerName -> TableName -> (s : Schema) -> IO (Handle s)

disjoint : Schema -> Schema -> Bool

sub : Schema -> Schema -> Bool
sub s1 s = all (\e => List.elem e s) s1

data Occurs : String -> Schema -> Type where
  OHere : Occurs s ((s, u) :: ss)
  OThere : Occurs s ss -> Occurs s (su :: ss)

lookup : (nm : String) -> (s : Schema) -> Occurs nm s -> U
lookup nm ((nm, u) :: _) OHere = u
lookup nm (su :: ss) (OThere o) = lookup nm ss o

data Expr : Schema -> U -> Type where
  Equal : Expr s u -> Expr s u -> Expr s BIT
  LessThan : Expr s u -> Expr s u -> Expr s BIT
  Get : (s : Schema) -> (nm : String) -> {el : Occurs nm s} -> Expr s (lookup nm s el)

data RA : Schema -> Type where
  Read : Handle s -> RA s
  Union : RA s -> RA s -> RA s
  Diff : RA s -> RA s -> RA s
  Product : {dj : So (disjoint s s1)} -> RA s -> RA s1 -> RA (s ++ s1)
  Project : (s1 : Schema) -> RA s -> {sb : So (sub s1 s)} -> RA s1
  Select : Expr s BIT -> RA s -> RA s

Models : Schema
Models = [("Model", VECT 20 CHAR)]

models : Handle Cars -> RA Models
models h = Project Models (Read h) {sb = %runElab search}

wet : Handle Cars -> RA Models
wet h = Project Models (Select (Get {el = %runElab search} Cars "Wet") (Read h)) {sb = %runElab search} 

toSQL : RA s -> String

query : RA s -> IO (List (Row s))
