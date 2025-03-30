{-# OPTIONS --cubical --guardedness --no-postfix --hidden-argument-puns #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.States where

private
    variable
        ST : Set _
        a b c d e f g h i j k l m n n' p q r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z : ST

open import OwnPrelude.Equality


open import ASCIIPrelude.ASCIIPrelude 
-- open NatOp
open PolyUnit
open PolyZero
open ListOp
open NatOp hiding (_^_) renaming (_leq_ to _leqB_)
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp
open import OwnPrelude.Equality
open import Level.Literals

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Relation.Functions


State : Set i -> Set j -> Set (i ~U~ j)
State S X = S -> (S -x- X)

get : State S S
get s = (s , s)

put : S -> State S (Unit {i})
put s _ = (s , unit)

monad : Monad {i} (State S)
RawMonad.return (Monad.rawMonad monad) x s = (s , x)
RawMonad._>>=_ (Monad.rawMonad monad) mx fmy s = let (s' , x) = mx s in fmy x s'
IsMonad.left-identity (Monad.isMonad monad)  = refl
IsMonad.right-identity (Monad.isMonad monad) = refl
IsMonad.associative (Monad.isMonad monad)    = refl