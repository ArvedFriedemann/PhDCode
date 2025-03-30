{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.ThresholdVariables where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.LatticeConstructions
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Data.MaybeCategorical renaming (monad to maybeMonad)
open import OwnPrelude.Data.NTuples
private
    _^_ = NTup
{-# DISPLAY _`$\back^_$` A n = A ^ n #-}
open ListOp

-- \tagcode{ThresholdVariables}

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L S S1 S2 : Set i
        F G M : Set i -> Set j
        a b x y z m s : A
        f g : A -> B

module Thresholds {S : Set i} {_P_ : S -> S -> Set j} 
    (isPreOrder : IsPreOrder _P_) where
    open IsPreOrder isPreOrder
    open PolyUnit
    open PolyZero

    module _ {X : Set u} where
        _=incMab=_ : Maybe X -> Maybe X -> Set u
        (just x) =incMab= nothing  = Zero
        (just x) =incMab= (just y) = x === y
        nothing  =incMab= _        = Unit

        IsThresholdRead : (f : S -> Maybe X) -> Set (i ~U~ j ~U~ u)
        IsThresholdRead f = forall s s' -> s P s' -> f s =incMab= f s'


module _ {k} where 
    open Monad {k} maybeMonad renaming
        ( left-identity to left-identity-Maybe
        ; right-identity to right-identity-Maybe
        ; associative to associative-Maybe)

record RawLVar 
    (S : Set i)
    (X : Set u) : Set (i ~U~ u) where  
    field
        read : S -> Maybe X
        write : X -> S

-- X should be from Set u, but functors are not sufficiently polymorphic
record LVar
    (S : Set i)
    (lat : BoundedSemilattice S)
    (X : Set j) : Set (i ~U~ j) where 
    open BoundedSemilattice lat
    open Thresholds isPreOrder   
    field
        rawLVar : RawLVar S X
    open RawLVar rawLVar public
    field
        isThresholdRead : IsThresholdRead read
        write-read : read (write x) === just x
        -- read-write-read : (| write (read s) |) >>= read === read s
        read-write-read : joinMaybe (mapMaybe read (mapMaybe write (read s))) === read s
        -- ^ - needs to be written like that because categorical stack is not sufficiently universe polymorphic


module _ 
    {S1 S2 : Set j}
    {L1 : BoundedSemilattice S1} 
    {L2 : BoundedSemilattice S2} where
    
    open BoundedSemilattice L1 using () renaming
        (semilattice to semilattice1)
    open BoundedSemilattice L2 using () renaming
        (semilattice to semilattice2)
    open ProductSemilatticeProperties semilattice1 semilattice2
    open BoundedSemilattice (L1 -xBSLx- L2)
    open Thresholds isPreOrder  

    e1 = fst e
    e2 = snd e

    module _ where
        open LVar

        module _ (v1 : LVar S1 L1 X) where 
            rawLVarFst : RawLVar (S1 -x- S2) X
            RawLVar.read rawLVarFst = read v1 o fst
            RawLVar.write rawLVarFst s = write v1 s , e2

        module _ (v2 : LVar S2 L2 Y) where 
            rawLVarSnd : RawLVar (S1 -x- S2) Y
            RawLVar.read rawLVarSnd = read v2 o snd
            RawLVar.write rawLVarSnd s = e1 , write v2 s

    module _ where
        open PolyUnit
        open LVar using () renaming 
            ( read to read'
            ; write to write'
            ; isThresholdRead to isThresholdRead'
            ; write-read to write-read'
            ; read-write-read to read-write-read')

        module _ (v1 : LVar S1 L1 X) where 
            LVarProductFst : LVar (S1 -x- S2) (L1 -xBSLx- L2) X
            LVar.rawLVar LVarProductFst = rawLVarFst v1
            LVar.isThresholdRead LVarProductFst (s1 , _) (s1' , _) sPs' = isThresholdRead' v1 s1 s1' (relatesProductFst sPs')
            LVar.write-read LVarProductFst = write-read' v1
            LVar.read-write-read LVarProductFst {s} with read' v1 (fst s) 
            ...| nothing  = refl
            ...| (just x) = write-read' LVarProductFst

        module _ (v2 : LVar S2 L2 Y) where
            LVarProductSnd : LVar (S1 -x- S2) (L1 -xBSLx- L2) Y
            LVar.rawLVar LVarProductSnd = rawLVarSnd v2
            LVar.isThresholdRead LVarProductSnd (_ , s2) (_ , s2') sPs' = isThresholdRead' v2 s2 s2' (relatesProductSnd sPs')
            LVar.write-read LVarProductSnd = write-read' v2
            LVar.read-write-read LVarProductSnd {s} with read' v2 (snd s) 
            ...| nothing  = refl
            ...| (just x) = write-read' LVarProductSnd

module LVarBundle where
    record LVar' : Set (lsuc i) where
        field
            Carrier : Set i
            Aim : Set i
            boundedSemilattice : BoundedSemilattice Carrier
            lVar : LVar Carrier boundedSemilattice Aim
        open LVar lVar

    toLVarBundle : forall {S BSL X} -> LVar {i} S BSL X -> LVar' {i}
    toLVarBundle {S} {BSL} {X} v = record
        { Carrier = S 
        ; Aim = X 
        ; boundedSemilattice = BSL 
        ; lVar = v }

module _ {i} where 
    open LVarBundle using (module LVar'; toLVarBundle) renaming (LVar' to LVarBundle)
    LVar' = LVarBundle {i}
    open LVar'

    LiftProdByVarCtx : LVar' -> (LVar' `$\back^ n $`) -> (LVar' `$\back^ n $`)
    LiftProdByVarCtx {n = 0} v unit = unit
    LiftProdByVarCtx {n = 1} v v' = toLVarBundle (LVarProductSnd {L1 = boundedSemilattice v} (lVar v'))
    LiftProdByVarCtx {n = 1+ 1+ n} v (v' , vars) = 
        ( toLVarBundle (LVarProductSnd {L1 = boundedSemilattice v} (lVar v'))
        , LiftProdByVarCtx v vars )

    LVarProductSpace : (LVar' `$\back^ n $`) -> (LVar' `$\back^ n $`)
    LVarProductSpace {n = 0} _        = unit
    LVarProductSpace {n = 1} v        = v
    LVarProductSpace {n = 2} (v , v') = 
        ( toLVarBundle (LVarProductFst {L2 = boundedSemilattice v'} (lVar v))
        , toLVarBundle (LVarProductSnd {L1 = boundedSemilattice v } (lVar v')))
    LVarProductSpace {n = 1+ 1+ 1+ n} (v , v' , vars) = 
        ( toLVarBundle (LVarProductFst {L2 = boundedSemilattice v'} (lVar v))
        , LiftProdByVarCtx {n = 1+ 1+ n} v (v' , vars) )