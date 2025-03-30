{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.Monoids where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

record RawMonoid (A : Set i) : Set i where
    infixr 20 _<>_
    field
        epsilon : A
        _<>_ : A -> A -> A

record IsMonoid {A : Set i} (rawMonoid : RawMonoid A) : Set i where
    open RawMonoid rawMonoid
    field
        left-identity : epsilon <> a === a
        right-identity : a <> epsilon === a
        associative : (a <> b) <> c === a <> (b <> c)


record Monoid (A : Set i) : Set i where
    field
        rawMonoid : RawMonoid A
        isMonoid  : IsMonoid rawMonoid
    open RawMonoid rawMonoid public
    open IsMonoid  isMonoid  public