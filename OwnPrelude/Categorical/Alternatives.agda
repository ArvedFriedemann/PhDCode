{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.Alternatives where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Categorical.Applicatives
open PolyUnit

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

record RawAlternativeOver {F : Set i -> Set j} (rawApplicative : RawApplicative F) : Set (lsuc i ~U~ j) where
    field
        rawMonoid : RawMonoid (F A)
    open RawApplicative rawApplicative
    module _ {A} where
        open RawMonoid (rawMonoid {A}) public renaming (
            epsilon to empty
            ; _<>_ to _<|>_)

    guard : Bool -> F Unit
    guard true  = pure unit
    guard false = empty

    guardMaybe : Maybe X -> F X
    guardMaybe (just x) = pure x
    guardMaybe nothing  = empty

    fail : F A
    fail = empty

record RawAlternative (F : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawMonoid : RawMonoid (F A)
        rawApplicative : RawApplicative F
    open RawAlternativeOver {rawApplicative = rawApplicative} (record{rawMonoid = rawMonoid}) public
        hiding (rawMonoid)
    open RawApplicative rawApplicative public

module _ {app : RawApplicative F} (rawapp : RawAlternativeOver app) where
    open RawAlternativeOver rawapp
    
    toRawAlternative : RawAlternative F
    RawAlternative.rawMonoid toRawAlternative = rawMonoid
    RawAlternative.rawApplicative toRawAlternative = app

record IsAlternative 
    {F : Set i -> Set j}
    (rawAlternative : RawAlternative F) : Set (lsuc i ~U~ j) where
    open RawAlternative rawAlternative
    field
        isMonoid : IsMonoid (rawMonoid {A = A})
        isApplicative : IsApplicative rawApplicative

    module _ {A : Set i} where
        open IsMonoid (isMonoid {A}) public
    open IsApplicative isApplicative public
        -- laws are experimental
        -- incompatible with errors
        -- right-distr : {f g : F (A -> B)} ->
        --     (f <|> g) <*> a === (f <*> a) <|> (g <*> a)
        -- left-distr  : {f : F (A -> B)} ->
        --     f <*> (a <|> b) === (f <*> a) <|> (f <*> b)

        -- this law is compatible with errors, but should be derived from monad instance
        -- left-absorb : {A B : Set i} -> 
        --     empty <*> a === empty {A -> B}

        -- incompatible with errors
        -- right-absorb : {A B : Set i} {a : F (A -> B)} -> 
        --     a <*> empty === empty

record IsAlternativeOver 
    {F : Set i -> Set j}
    (app : Applicative F) 
    (rawAlternativeOver : RawAlternativeOver (Applicative.rawApplicative app)) : Set (lsuc i ~U~ j) where

    open RawAlternativeOver rawAlternativeOver
    field
        isMonoid : IsMonoid (rawMonoid {A = A})

    module _ {A : Set i} where
        open IsMonoid (isMonoid {A}) public
     


record Alternative (F : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawAlternative : RawAlternative F
        isAlternative  : IsAlternative rawAlternative
    open RawAlternative rawAlternative public
    open IsAlternative  isAlternative  public

record AlternativeOver {F : Set i -> Set j} (app : Applicative F) : Set (lsuc i ~U~ j) where
    field
        rawAlternativeOver : RawAlternativeOver (Applicative.rawApplicative app)
        isAlternativeOver : IsAlternativeOver app rawAlternativeOver

    open IsAlternativeOver  isAlternativeOver public
    open RawAlternativeOver rawAlternativeOver public