{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.CoLists where

open import ASCIIPrelude.ASCIIPrelude 
-- open NatOp
open PolyUnit
open PolyZero
open NatOp hiding (_^_) renaming (_leq_ to _leqB_)
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp
open import OwnPrelude.Equality
open import Level.Literals

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Relation.Functions

open ExistsSyntax


data CoListOut (A : Set i) (B : Set i) : Set i where
    nil  : CoListOut A B
    ctd  : (xs : B) -> CoListOut A B
    cons : (x : A) -> (xs : B) -> CoListOut A B


module _ {X Y : Set i} where
    CoverCoListOut : CoListOut X Y -> CoListOut X Y -> Set i
    CoverCoListOut nil nil                 = Unit
    CoverCoListOut (ctd x) (ctd y)         = x === y
    CoverCoListOut (cons x xs) (cons y ys) = (x === y) and (xs === ys)
    CoverCoListOut _ _                     = Zero

    encodeReflCoListOut : CoverCoListOut a a
    encodeReflCoListOut {a = nil} = unit
    encodeReflCoListOut {a = ctd xs}      = refl
    encodeReflCoListOut {a = cons x xs}   = refl , refl

    encodeCoListOut : {a b : CoListOut X Y} -> a === b -> CoverCoListOut a b
    encodeCoListOut {a} = J (\b _ -> CoverCoListOut a b) encodeReflCoListOut

[_]nil:_ctd:_out:_ : CoListOut A B -> C -> (B -> C) -> (A -> B -> C) -> C
[ nil ]nil: n ctd: c out: ot = n
[ ctd xs ]nil: n ctd: c out: ot = c xs
[ cons x xs ]nil: n ctd: c out: ot = ot x xs


record CoList (A : Set i) : Set i where
    coinductive
    constructor CoListC
    field
        next : CoListOut A (CoList A)
open CoList

bisim : next xs === next ys -> xs === ys
next (bisim eq i) = eq i

data [_]\_ (A : Set i) (_P_ : A -> A -> Set j) : Set (i ~U~ j) where
    Qval : A -> [ A ]\ _P_
    P-eq : forall a b -> a P b -> Qval a === Qval b

data CtdCoListEqP (A : Set i) (a b : CoList A) : Set i where
    ctd-nil  : (nexta=ctd : next a === ctd b) -> (nextb=nil : next b === nil) -> CtdCoListEqP A a b
    ctd-cons : (nexta=ctd : next a === ctd b) -> (nextb=cons : next b === (cons x xs)) -> CtdCoListEqP A a b 

CtdCoList : Set i -> Set i
CtdCoList A = [ CoList A ]\ CtdCoListEqP A

map : (A -> B) -> CoList A -> CoList B
next (map f lst) with next lst
... | nil       = nil
... | ctd xs    = ctd (map f xs)
... | cons x xs = cons (f x) (map f xs)

map-ctd : next a === ctd xs -> next (map f a) === ctd (map f xs)
map-ctd {a} {f} eq with next a
... | nil = absurd (encodeCoListOut eq)
... | ctd xs = encodeCoListOut eq || ctd o map f
... | cons x xs = absurd (encodeCoListOut eq)

map-nil : next a === nil -> next (map f a) === nil
map-nil {a} eq with next a
... | nil = refl
... | ctd xs = absurd (encodeCoListOut eq)
... | cons x xs = absurd (encodeCoListOut eq)

map-cons : next a === cons x xs -> next (map f a) === cons (f x) (map f xs)
map-cons {a} {f} eq with next a 
... | nil = absurd (encodeCoListOut eq)
... | ctd xs = absurd (encodeCoListOut eq)
... | cons x' xs' = let (x=x' , xs=xs') = encodeCoListOut eq in \i -> cons (f (x=x' i)) (map f (xs=xs' i))

mapCL : (A -> B) -> CtdCoList A -> CtdCoList B
mapCL f (Qval xs) = Qval (map f xs)
mapCL f (P-eq a b (ctd-nil nexta=ctd nextb=nil) i) with next a in nexta-eq | next b in nextb-eq 
... | nil | r2            = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nexta=ctd) i
... | cons x xs | r2      = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nexta=ctd) i
... | ctd xs | ctd xs1    = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nextb=nil) i
... | ctd xs | cons x xs1 = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nextb=nil) i
... | ctd xs | nil = P-eq (map f a) (map f b) 
    (ctd-nil (trans (map-ctd {a = a} (propToPath nexta-eq)) (encodeCoListOut nexta=ctd || ctd o map f)) 
    (map-nil {a = b} (propToPath nextb-eq))) i
mapCL f (P-eq a b (ctd-cons nexta=ctd nextb=cons) i) with next a in nexta-eq | next b in nextb-eq 
... | nil | r2 = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nexta=ctd) i
... | cons x xs | r2 = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nexta=ctd) i
... | ctd xs | nil = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nextb=cons) i
... | ctd xs | ctd xs1 = absurd {A = Qval (map f a) === Qval (map f b)} (encodeCoListOut nextb=cons) i
... | ctd xs | cons x xs1 = P-eq (map f a) (map f b) (ctd-cons 
    (trans (map-ctd {a = a} (propToPath nexta-eq)) (encodeCoListOut nexta=ctd || ctd o map f)) 
    (map-cons {a = b} (propToPath nextb-eq))) i

