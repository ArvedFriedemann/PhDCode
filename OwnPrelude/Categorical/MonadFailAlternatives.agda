{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.MonadFailAlternatives where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Alternatives

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

record RawMonadFailAlternativeOver {M : Set i -> Set j} (rawMonad : RawMonad M) : Set (lsuc i ~U~ j) where
    field
        rawAlternativeOver : RawAlternativeOver (RawMonad.rawApplicative rawMonad)

    open RawAlternativeOver rawAlternativeOver public
    
record IsMonadFailAlternativeOver
    {M : Set i -> Set j}
    (monad : Monad M)
    (rawMonadFailAlternativeOver : RawMonadFailAlternativeOver (Monad.rawMonad monad)) : Set (lsuc i ~U~ j) where
    open RawMonadFailAlternativeOver rawMonadFailAlternativeOver
    field
        isAlternativeOver : IsAlternativeOver (Monad.applicative monad) rawAlternativeOver
    open IsAlternativeOver isAlternativeOver public 
        renaming
        ( left-identity to left-identity-monoid
            ; right-identity to right-identity-monoid
            ; associative to associative-monoid) public
    open Monad monad
    field
        left-absorb  : empty >>= f === empty

record MonadFailAlternativeOver {M : Set i -> Set j} (monad : Monad M) : Set (lsuc i ~U~ j) where
    field
        rawMonadFailAlternativeOver : RawMonadFailAlternativeOver (Monad.rawMonad monad)
        isMonadFailAlternativeOver  : IsMonadFailAlternativeOver monad rawMonadFailAlternativeOver
    open RawMonadFailAlternativeOver rawMonadFailAlternativeOver public
    open IsMonadFailAlternativeOver  isMonadFailAlternativeOver  public

record MonadFailAlternative (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        monad : Monad M
        rawMonadFailAlternativeOver : RawMonadFailAlternativeOver (Monad.rawMonad monad)
        isMonadFailAlternativeOver  : IsMonadFailAlternativeOver monad rawMonadFailAlternativeOver
    open RawMonadFailAlternativeOver rawMonadFailAlternativeOver public
    open IsMonadFailAlternativeOver  isMonadFailAlternativeOver  public