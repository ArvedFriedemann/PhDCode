{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Examples.MonadicIndexingExample where

open import ASCIIPrelude.ASCIIPrelude hiding (List ; [] ; _::_)
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import OwnPrelude.Data.Decidables

open ExistsSyntax

-- \tagcode{MonadicIndexingExample}

private
    variable
        ST : Set _
        a b c d e f g h i j k l m n p p1 p2 p3 p' q r s s' s1 s2 s3 t u v w x y z i' j' k' l' A B C X Y K M F : ST

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

length : List A -> Nat
length [] = 0
length (x :: lst) = 1+ (length lst)

data Vec (A : Set) : Nat -> Set where
    [] : Vec A 0
    _::_ : A -> Vec A n -> Vec A (1+ n)

Vec' : (A : Set) (n : Nat) -> Set
Vec' A n = Sigma (List A) (\lst -> length lst === n)  

open Monads

module _ {M : Set -> Set} {mon : Monad M} (fail : forall {A} -> M A) where
    open Monad mon
    
    toVec : (n : Nat) -> List A -> M (Vec A n)
    toVec 0      []         = (| [] |)
    toVec (1+ n) (x :: lst) = (| (x ::_) (toVec n lst) |)
    toVec _      _          = fail
    
    module _ {A : Set} {B : A -> Set} (B? : forall (a : A) -> Dec (B a)) where
        filterM : A -> M (Sigma A B)
        filterM a with B? a
        ... | yes Ba = return (a , Ba)
        ... | no ¬Ba = fail

