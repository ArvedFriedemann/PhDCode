{-# OPTIONS --cubical --guardedness --no-postfix --hidden-argument-puns #-}
module Preliminaries.PreliminariesPartII where

private
    variable
        ST : Set _
        a b c d e f g h i j k l m n n' p q r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z : ST

open import OwnPrelude.Equality


-- \tagcode{PreliminariesPtII}

open import ASCIIPrelude.ASCIIPrelude 
-- open NatOp
open PolyUnit
open PolyZero
open ListOp
open BoolOp renaming (notBool to not``Bool)
open NatOp hiding (_^_) renaming (_leq_ to _leqB_)
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp
open import OwnPrelude.Equality
open import Level.Literals

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.Perhaps
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Data.TrivialLattices hiding (TB)
open import OwnPrelude.Data.States

module TB {i} = Monad {i} monadTB

data Atom (A : Set i) : Set i where
    pos : A -> Atom A
    neg : A -> Atom A

Clause : Set i -> Set i
Clause A = List (Atom A)

Formula : Set i -> Set i
Formula A = List (Clause A)

Asm : Set i -> Set i
Asm A = List (A tb)

read : Nat -> Asm A -> A tb
read n      []         = topTB
read 0      (x :: asm) = x
read (1+ n) (x :: asm) = read n asm

readAtom : Atom Nat -> Asm Bool -> Bool tb
readAtom (pos x) asm = (read x asm)
readAtom (neg x) asm = TB.fmap not``Bool (read x asm)

isPositiveAtom? : Asm Bool -> Atom Nat -> Bool
isPositiveAtom? asm x with readAtom x asm 
... | valTB true = true
... | _          = false 

isUnassigned? : A tb -> Bool
isUnassigned? topTB = true
isUnassigned? _     = false

atomUnassigned? : Asm Bool -> Atom Nat -> Bool
atomUnassigned? asm x = isUnassigned? (readAtom x asm)

module _ {{deq : DecEq Bool}} where
    open DecEq deq
    open TrivialLattice deq
    open Lattice trivialLattice

    write : Nat -> Bool tb -> Asm Bool -> Asm Bool
    write 0      a []         = a :: []
    write 0      a (x :: asm) = a /\ x :: asm
    write (1+ n) a []         = topTB :: write n a []
    write (1+ n) a (x :: asm) = x :: write n a asm

    assignAtom : Atom Nat -> Asm Bool -> Asm Bool
    assignAtom (pos x) asm = write x (valTB true) asm
    assignAtom (neg x) asm = write x (valTB false) asm

    isSatisfied : Asm Bool -> Clause Nat -> Bool
    isSatisfied asm = any (isPositiveAtom? asm)

    unassigned : Asm Bool -> Clause Nat -> Clause Nat
    unassigned asm = filter (atomUnassigned? asm)

    AssignUnit : Asm Bool -> Clause Nat -> Asm Bool
    AssignUnit asm cls with isSatisfied asm cls
    ... | true  = asm
    ... | false with unassigned asm cls
    ... | (x :: []) = assignAtom x asm
    ... | _         = asm

    UnitPropStep : Asm Bool -> Formula Nat -> Asm Bool
    UnitPropStep asm []        = asm
    UnitPropStep asm (c :: cs) = AssignUnit (UnitPropStep asm cs) c 

    splitAsmAt : Nat -> Asm Bool -> List (Asm Bool)
    splitAsmAt n asm = write n (valTB true) asm :: write n (valTB false) asm :: []
    -- ^-- remove assignments that are already unconsistent to decrease branching

    module _ where
        open import OwnPrelude.Data.ListCategorical
        module _ {i} where open Monad {i} listMonad public

        allSplitsUntil : Nat -> Asm Bool -> List (Asm Bool)
        allSplitsUntil 0      asm = splitAsmAt 0 asm
        allSplitsUntil (1+ n) asm = splitAsmAt (1+ n) asm >>= allSplitsUntil n
            


-- read : Nat -> State (Asm A) (A tb)
-- read 0      asm = {!   !} 
-- read (1+ n) asm = {!   !}