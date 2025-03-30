{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-} 
module OwnPrelude.Data.VarAsms where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Lattices
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

data VarAsm (X : Set i) : Set i where
    unassigned : VarAsm X
    asm : X -> VarAsm X
    conflict : VarAsm X

module _ {X : Set i} where
    CoverVarAsm : VarAsm X -> VarAsm X -> Set i
    CoverVarAsm unassigned unassigned = Unit
    CoverVarAsm (asm x) (asm y)       = x === y
    CoverVarAsm conflict conflict     = Unit
    CoverVarAsm _ _                   = Zero

    encodeReflVarAsm : CoverVarAsm a a
    encodeReflVarAsm {a = unassigned} = unit
    encodeReflVarAsm {a = asm x}      = refl
    encodeReflVarAsm {a = conflict}   = unit

    encodeVarAsm : {a b : VarAsm X} -> a === b -> CoverVarAsm a b
    encodeVarAsm {a} = J (\b _ -> CoverVarAsm a b) encodeReflVarAsm


asm-injective : asm x === asm y -> x === y
asm-injective {x} {y} = encodeVarAsm

unas:_conf:_asm: : X -> X -> (Y -> X) -> VarAsm Y -> X
unas:_conf:_asm: unas conf fasm unassigned = unas
unas:_conf:_asm: unas conf fasm (asm x)    = fasm x
unas:_conf:_asm: unas conf fasm conflict   = conf

mapVarAsm : (X -> Y) -> VarAsm X -> VarAsm Y
mapVarAsm f unassigned = unassigned
mapVarAsm f (asm x)    = asm (f x)
mapVarAsm f conflict   = conflict

joinVarAsm : VarAsm (VarAsm X) -> VarAsm X
joinVarAsm unassigned = unassigned
joinVarAsm (asm va) = va
joinVarAsm conflict = conflict

_>>=VarAsm_ : VarAsm A -> (A -> VarAsm B) -> VarAsm B
va >>=VarAsm fvb = joinVarAsm (mapVarAsm fvb va)

_>=>VarAsm_ : (A -> VarAsm B) -> (B -> VarAsm C) -> A -> VarAsm C
(fb >=>VarAsm fc) a = fb a >>=VarAsm fc 

_<*>VarAsm_ : VarAsm (A -> B) -> VarAsm A -> VarAsm B
_<*>VarAsm_ vf va = vf >>=VarAsm flip mapVarAsm va

module MonadNames where
    _>>=_ = _>>=VarAsm_
    _>=>_ = _>=>VarAsm_

    _<=<_ : (B -> VarAsm C) -> (A -> VarAsm B) -> A -> VarAsm C
    _<=<_ = flip _>=>_
    
    _<*>_ = _<*>VarAsm_
    _<$>_ = mapVarAsm
    fmap = _<$>_
    
    pure : A -> VarAsm A
    pure = asm

    return : A -> VarAsm A
    return = asm

rawMonad : RawMonad {i} VarAsm
RawMonad.return rawMonad = asm
RawMonad._>>=_ rawMonad = _>>=VarAsm_

module _ {i} where
    open RawMonad {i} rawMonad
    
    monad : Monad {i} VarAsm
    Monad.rawMonad monad = rawMonad
    IsMonad.left-identity (Monad.isMonad monad) = refl
    IsMonad.right-identity (Monad.isMonad monad) {m = unassigned} = refl
    IsMonad.right-identity (Monad.isMonad monad) {m = asm x} = refl
    IsMonad.right-identity (Monad.isMonad monad) {m = conflict} = refl
    IsMonad.associative (Monad.isMonad monad) {m = unassigned} = refl
    IsMonad.associative (Monad.isMonad monad) {m = asm x} = refl
    IsMonad.associative (Monad.isMonad monad) {m = conflict} = refl

    left-absorb-unassigned : unassigned >>= m === unassigned
    left-absorb-unassigned = refl

    left-absorb-conflict : conflict >>= m === conflict
    left-absorb-conflict = refl