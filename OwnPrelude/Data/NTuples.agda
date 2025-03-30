{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.NTuples where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality

open ExistsSyntax
open PolyUnit

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L S S1 S2 : Set i
        F G M : Set i -> Set j
        a b x y z m s : A
        f g : A -> B

NTup : Set i -> Nat -> Set i
NTup _ 0      = Unit
NTup A 1      = A
NTup A (1+ n) = A -x- NTup A n

_`$\back^_$` = NTup

_,-_ : A -> NTup A n -> NTup A (1+ n)
_,-_ {n = 0} a t = a
_,-_ {n = 1+ n} a t = a , t 

_of_toTuple : (n : Nat) -> A -> NTup A n
0 of a toTuple = unit
1 of a toTuple = a
(1+ 1+ n) of a toTuple = a , (1+ n) of a toTuple

mapNTup : (A -> B) -> NTup A n -> NTup B n
mapNTup {n = 0} f _ = unit
mapNTup {n = 1} f t = f t
mapNTup {n = 1+ 1+ n} f (a , t) = f a , mapNTup f t

foldNTup' : (A -> B -> B) -> (A -> B) -> B -> NTup A n -> B
foldNTup' {n = 0} fabb fab b _ = b
foldNTup' {n = 1} fabb fab b t = fab t
foldNTup' {n = 1+ 1+ n} fabb fab b (t , ts) = fabb t (foldNTup' fabb fab b ts)

foldNTup : (A -> B -> B) -> B -> NTup A n -> B
foldNTup fabb b = foldNTup' fabb (flip fabb b) b

foldNTupIdx' : (Nat -> A -> B -> B) -> (A -> B) -> B -> NTup A n -> B
foldNTupIdx' {n = 0} fabb fab b _ = b
foldNTupIdx' {n = 1} fabb fab b t = fab t
foldNTupIdx' {n = 1+ 1+ n} fabb fab b (t , ts) = fabb (1+ n) t (foldNTupIdx' fabb fab b ts)

foldNTupIdx : (Nat -> A -> B -> B) -> B -> NTup A n -> B
foldNTupIdx fabb b = foldNTupIdx' fabb (flip (fabb 0) b) b

foldNTupPi' : {B : Nat -> Set i} -> 
    ((n : Nat) -> A -> B n -> B (1+ n)) -> 
    (A -> B 1) -> B 0 -> NTup A n -> B n
foldNTupPi' {n = 0} fabb fab b _ = b
foldNTupPi' {n = 1} fabb fab b t = fab t
foldNTupPi' {n = 1+ 1+ n} fabb fab b (t , ts) = fabb (1+ n) t (foldNTupPi' fabb fab b ts)

foldNTupPi : {B : Nat -> Set i} -> 
    ((n : Nat) -> A -> B n -> B (1+ n)) -> 
    B 0 -> NTup A n -> B n
foldNTupPi fabb b = foldNTupPi' fabb (flip (fabb 0) b) b

toList : NTup A n -> List A
toList = foldNTup _::_ []

private
    _^_ = NTup
{-# DISPLAY _`$\back^_$` A n = A ^ n #-}

HTup : List (Set i) -> Set i
HTup []        = Unit
HTup (A :: []) = A
HTup (A :: AS) = A -x- HTup AS