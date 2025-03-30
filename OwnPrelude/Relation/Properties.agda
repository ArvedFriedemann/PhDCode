{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Relation.Properties where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monads

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G M : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

LeftAbsorbing_over_ : {M : Set i -> Set j}(empty : {A : Set i} -> M A) -> RawMonad M -> Set (lsuc i ~U~ j)
LeftAbsorbing_over_ {i} {M} empty rawMonad = forall {A B : Set i} {m : A -> M B} -> empty >>= m === empty
    where open RawMonad rawMonad