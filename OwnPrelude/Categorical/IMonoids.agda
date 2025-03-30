{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.IMonoids where

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

record RawIMonoid (I : Set j) (A : I -> I -> Set i) : Set (i ~U~ j) where
    infixr 20 _<>_
    field
        epsilon : A a a
        _<>_ : A a b -> A b c -> A a c

record IsIMonoid {I : Set j} {A : I -> I -> Set i} (rawIMonoid : RawIMonoid I A) : Set (i ~U~ j) where
    open RawIMonoid rawIMonoid
    field
        left-identity : epsilon <> a === a
        right-identity : a <> epsilon === a
        associative : (a <> b) <> c === a <> (b <> c)


record IMonoid (I : Set j) (A : I -> I -> Set i) : Set (i ~U~ j) where
    field
        rawIMonoid : RawIMonoid I A
        isIMonoid  : IsIMonoid rawIMonoid
    open RawIMonoid rawIMonoid public
    open IsIMonoid  isIMonoid  public