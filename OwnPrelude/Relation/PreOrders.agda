{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Relation.PreOrders where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Categorical.IMonoids

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m p p' p'' : A
        f g : A -> B

record IsPreOrder {A : Set i} (_P_ : A -> A -> Set k) : Set (i ~U~ k) where
    field
        reflexive  : a P a
        transitive : a P b -> b P c -> a P c

    infixr 10 _P-<=_
    _P-<=_ = transitive
    
    rawIMonoid : RawIMonoid A _P_
    RawIMonoid.epsilon rawIMonoid = reflexive
    RawIMonoid._<>_    rawIMonoid = transitive

record PreOrder i k : Set (lsuc i ~U~ lsuc k) where
    field
        Carrier : Set i
        _P_ : Carrier -> Carrier -> Set k
        isPreOrder : IsPreOrder _P_
    open IsPreOrder isPreOrder public 