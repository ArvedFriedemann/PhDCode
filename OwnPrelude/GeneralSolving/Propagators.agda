{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-postfix #-}
-- {-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.Propagators where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality

open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadTs
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Data.LatticeStates
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.ConstrainedStates

open ExistsSyntax

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d f g h i j k l m n n' p q r s s' st t u v w x x' y z fm i' j' k' l' A B C D E F G H K L M N O Q R S T W X Y Z alg Ctx  : ST

module ConstrainedPropagatorState
    (S : Set u)
    (_P_ : S -> S -> Set c) where

    CPState : 
        Set i -> Set (u ~U~ c ~U~ i)
    CPState X = (s : S) -> (exists[ s' of S ] (s P s')) -x- X

module ContinuationMonadTransformer  where

    ContT : Set i ->  (M : Set i -> Set j) -> Set i -> Set (i ~U~ j)
    ContT A M X = (X -> M A) -> M A

    module MonadInstance (mon : Monad M) where
        open Monad mon

        lift : M A -> ContT X M A
        lift mx xma = mx >>= xma

    module contOnFail {M : Set i -> Set i} (mon : Monad M) where
        open Monad mon

        contOnFail : M (Maybe X) -> ContT A M (X or (X -> M A))
        contOnFail m cont = m >>= 
            \{(just x) -> cont (left x)
            ;  nothing -> cont (right (cont o left))}
        
        contOnFail' : M (Maybe X) -> ContT A M (X or (M (Maybe X) -x- (X -> M A)))
        contOnFail' m cont = m >>= 
            \{(just x) -> cont (left x)
            ;  nothing -> cont (right (m , cont o left))}

        -- contOnFail' : M (Maybe X) -> ContT A M (X or (exists[ Y of Set i ] (M Y -x- (Y -> M A))))
        -- contOnFail' = {!!}


module ContLatticeState
    {S : Set u}
    (bsl : BoundedSemilattice S) 
    {M : Set (i ~U~ u) -> Set (i ~U~ u)} 
    (monadM : Monad M) where
    
    open BoundedSemilattice bsl hiding (associative; e)
    open Monad monadM
    open LatticeState {i = i} {j = i} bsl monadM
    open LBVar renaming (read to readL; write to writeL)
    open ContinuationMonadTransformer

    module _ {X : Set (i ~U~ u)} where
        read : V X -> ContT A LState (X or (X -> LState A) or Unit {i})
        read v cont s = 
            unas: cont ((right {A = X} o left) (cont o left)) s
            conf: cont ((right o right) unit) s
            asm:  (flip cont s o left)
            (readL v s)


