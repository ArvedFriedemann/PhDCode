{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.MaybeCategorical where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.ASCIIPreludeProofs
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Monads

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

module _ {i} where
    rawMonad : RawMonad {i} Maybe
    RawMonad.return rawMonad = just
    RawMonad._>>=_  rawMonad (just x) fmb = fmb x
    RawMonad._>>=_  rawMonad nothing  fmb = nothing

    monad : Monad {i} Maybe
    Monad.rawMonad monad = rawMonad
    IsMonad.left-identity (Monad.isMonad monad) = refl
    IsMonad.right-identity (Monad.isMonad monad) {m = just x} = refl
    IsMonad.right-identity (Monad.isMonad monad) {m = nothing} = refl
    IsMonad.associative (Monad.isMonad monad) {m = just x}  {f = f} {g = g} = refl
    IsMonad.associative (Monad.isMonad monad) {m = nothing} {f = f} {g = g} = refl

    rawApplicative = Monad.rawApplicative monad
    applicative    = Monad.applicative monad

    rawFunctor = Monad.rawFunctor monad
    functor    = Monad.functor monad