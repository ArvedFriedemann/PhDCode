{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.MonadicVariables where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monads
open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L S S1 S2 : Set i
        F G M : Set i -> Set j
        a b x y z m s : A
        f g : A -> B

-- \tagcode{MonadicVariable}

module MonadicVariables {M : Set i -> Set j} (mon : Monad M) where
    open Monad mon
    open PolyUnit
    record MonadicVariable (X : Set i) : Set (lsuc i ~U~ j) where
        field
            read : M X
            write : X -> M Unit
            commutative : forall {m' : M Y}{f : Y -> X -> M Z} ->
                (read >>= \_ -> m' >>= \y -> read >>= \x2 -> f y x2) === (read >>= \x1 -> m' >>= \y -> read >>= \_ -> f y x1)
            read-write : forall {x : X}{m' : M Y}{f : Y -> X -> M Z} ->
                (write x >> (m' >>= \y -> read >>= \x' -> f y x')) === (write x >> (m' >>= \y -> read >>= \_ -> f y x))

