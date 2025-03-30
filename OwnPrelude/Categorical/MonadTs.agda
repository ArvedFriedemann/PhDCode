{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.MonadTs where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monads

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

record RawMonadT (M : Set i -> Set j) (T : Set i -> Set k) : Set (lsuc i ~U~ j ~U~ k) where
    field
        rawInnerMonad : RawMonad M
        rawOuterMonad : RawMonad T
        lift : M A -> T A

record IsMonadT 
    {M : Set i -> Set j} 
    {T : Set i -> Set k}
    (rawMonadT : RawMonadT M T) 
    : Set (lsuc i ~U~ j ~U~ k) where
    open RawMonadT rawMonadT
    open RawMonad rawInnerMonad renaming (return to returnM; _>>=_ to _>>=M_)
    open RawMonad rawOuterMonad renaming (return to returnT; _>>=_ to _>>=T_)
    field
        isInnerMonad : IsMonad rawInnerMonad
        isOuterMonad : IsMonad rawOuterMonad
        lift-return  : lift o returnM  === returnT {A = A}
        lift-bind    : lift (m >>=M f) === (lift m) >>=T (lift o f)

record MonadT (M : Set i -> Set j) (T : Set i -> Set k) : Set (lsuc i ~U~ j ~U~ k) where
    field
        rawMonadT : RawMonadT M T
        isMonadT  : IsMonadT rawMonadT
    open RawMonadT rawMonadT public
    open IsMonadT  isMonadT  public 

    innerMonad : Monad M
    Monad.rawMonad innerMonad = rawInnerMonad
    Monad.isMonad  innerMonad = isInnerMonad

    outerMonad : Monad T
    Monad.rawMonad outerMonad = rawOuterMonad
    Monad.isMonad  outerMonad = isOuterMonad