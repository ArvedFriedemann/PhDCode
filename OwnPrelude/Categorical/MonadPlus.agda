{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.MonadPlus where

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

record RawMonadPlus (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawMonoid : RawMonoid (M A)
        rawMonad : RawMonad M

    open RawMonad  rawMonad  public
    module _ {A} where
        open RawMonoid (rawMonoid {A}) public renaming (
              epsilon to mzero
            ; _<>_ to mplus
            )

    rawAlternativeOver : RawAlternativeOver rawApplicative
    RawAlternativeOver.rawMonoid rawAlternativeOver = rawMonoid

    rawAlternative = toRawAlternative rawAlternativeOver

    open RawAlternativeOver rawAlternativeOver public
        hiding (rawMonoid)
    
record IsMonadPlus 
    {M : Set i -> Set j}
    (rawMonadPlus : RawMonadPlus M) : Set (lsuc i ~U~ j) where
    open RawMonadPlus rawMonadPlus
    field
        isMonoid : IsMonoid (rawMonoid {A = A})
        isMonad  : IsMonad rawMonad
        left-absorb  : mzero >>= f === mzero
        right-absorb : m >> mzero {A = A}  === mzero

    module _ {A : Set i} where
        open IsMonoid (isMonoid {A = A}) renaming 
            ( left-identity to left-identity-monoid
            ; right-identity to right-identity-monoid
            ; associative to associative-monoid) public
    open IsMonad  isMonad  public
        
    isAlternative : IsAlternative rawAlternative
    IsAlternative.isMonoid isAlternative = isMonoid
    IsAlternative.isApplicative isAlternative = isApplicative

record MonadPlus (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawMonadPlus : RawMonadPlus M
        isMonadPlus  : IsMonadPlus rawMonadPlus
    open RawMonadPlus rawMonadPlus public
    open IsMonadPlus  isMonadPlus  public

    monad : Monad M
    Monad.rawMonad monad = rawMonad
    Monad.isMonad  monad = isMonad