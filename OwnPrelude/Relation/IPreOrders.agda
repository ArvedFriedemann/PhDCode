{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Relation.IPreOrders where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Categorical.IMonoids

private
    variable
        il jl ul kl : Level
        n n' : Nat
        A B C X Y Z L S : Set il
        F G : Set il -> Set jl
        x y z m : A
        f g : A -> B

module _ {I : Set ul} {A : I -> Set il} where 
    private variable
            h i j k : I

    module _ {A : I -> Set il} where 
        private variable
            a b c : A i

        record IsIPreOrder (_P'_ : (i j : I) -> A i -> A j -> Set kl) : Set (il ~U~ kl ~U~ ul) where
            _P_ : {i j : I} -> A i -> A j -> Set kl
            _P_ {i} {j} = _P'_ i j
            field
                reflexive  : {i : I} -> {a : A i} -> a P a
                transitive : {i j k : I} {a : A i} {b : A j} {c : A k} -> 
                    a P b -> b P c -> a P c
            
            rawIMonoid : RawIMonoid (Sigma I A) (\{(_ , a) (_ , b) -> a P b})
            RawIMonoid.epsilon rawIMonoid = reflexive
            RawIMonoid._<>_    rawIMonoid = transitive

record IPreOrder (I : Set ul) il kl : Set (lsuc il ~U~ lsuc kl ~U~ ul) where
    field
        Carrier : I -> Set il
        _P'_ : (i j : I) -> Carrier i -> Carrier j -> Set kl
        isIPreOrder : IsIPreOrder {A = Carrier} _P'_
    open IsIPreOrder isIPreOrder public 