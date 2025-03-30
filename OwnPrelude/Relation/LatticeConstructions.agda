{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Relation.LatticeConstructions where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp 
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Categorical.IMonoids
open import OwnPrelude.Data.NTuples
open import OwnPrelude.Data.TrivialLattices

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L L1 L2 S S1 S2 : Set i
        F G M : Set i -> Set j
        a b x y z m x1 x2 y1 y2 z1 z2 : A
        f g : A -> B


module _ (sl1 : Semilattice L1) (sl2 : Semilattice L2) where
    open Semilattice sl1 renaming 
        (_<>_ to _<>1_
        ; _P_ to _P1_
        ; associative to associative1
        ; commutative to commutative1
        ; idempotent  to idempotent1 )
    open Semilattice sl2 renaming 
        (_<>_ to _<>2_
        ; _P_ to _P2_
        ; associative to associative2
        ; commutative to commutative2
        ; idempotent  to idempotent2 )
    
    rawSemilatticeProduct : RawSemilattice (L1 -x- L2)
    RawSemilattice._<>_ rawSemilatticeProduct (x1 , y1) (x2 , y2) = (x1 <>1 x2 , y1 <>2 y2)
    
    open RawSemilattice rawSemilatticeProduct

    semilatticeProduct : Semilattice (L1 -x- L2)
    Semilattice.rawSemilattice semilatticeProduct = rawSemilatticeProduct
    IsSemilattice.associative (Semilattice.isSemilattice semilatticeProduct) 
        {x = (x1 , x2)} {y = (y1 , y2)} {z = (z1 , z2)} = 
            (x1 , x2) <> (y1 , y2) <> (z1 , z2)       =<>
            (x1 <>1 y1 <>1 z1 , x2 <>2 y2 <>2 z2)     =< associative1 || _, x2 <>2 y2 <>2 z2 >
            ((x1 <>1 y1) <>1 z1 , x2 <>2 y2 <>2 z2)   =< associative2 || (x1 <>1 y1) <>1 z1 ,_ >
            ((x1 <>1 y1) <>1 z1 , (x2 <>2 y2) <>2 z2) =<>
            ((x1 , x2) <> (y1 , y2)) <> (z1 , z2)     qed
    IsSemilattice.commutative (Semilattice.isSemilattice semilatticeProduct) 
        {x = (x1 , x2)} {y = (y1 , y2)} = 
            (x1 , x2) <> (y1 , y2)  =<>
            (x1 <>1 y1 , x2 <>2 y2) =< commutative1 || _, x2 <>2 y2 >
            (y1 <>1 x1 , x2 <>2 y2) =< commutative2 || y1 <>1 x1 ,_ >
            (y1 <>1 x1 , y2 <>2 x2) =<>
            (y1 , y2) <> (x1 , x2)  qed
    IsSemilattice.idempotent (Semilattice.isSemilattice semilatticeProduct) 
        {x = (x1 , x2)} = 
            (x1 , x2) <> (x1 , x2)  =<>
            (x1 <>1 x1 , x2 <>2 x2) =< idempotent1 || _, x2 <>2 x2 >
            (x1 , x2 <>2 x2)        =< idempotent2 || x1 ,_ >
            (x1 , x2)               qed

    _-xSLx-_ = semilatticeProduct

module ProductSemilatticeProperties (sl1 : Semilattice L1) (sl2 : Semilattice L2) where

    open Semilattice (sl1 -xSLx- sl2)
    open Semilattice sl1 using () renaming (_P_ to _P1_)
    open Semilattice sl2 using () renaming (_P_ to _P2_)

    relatesProductFst : (x1 , x2) P (y1 , y2) -> x1 P1 y1
    relatesProductFst {x1} {x2} {y1} {y2} xPy = xPy || fst

    relatesProductSnd : (x1 , x2) P (y1 , y2) -> x2 P2 y2
    relatesProductSnd {x1} {x2} {y1} {y2} xPy = xPy || snd

module _ (bsl1 : BoundedSemilattice L1) (bsl2 : BoundedSemilattice L2) where
    open BoundedSemilattice bsl1 renaming
        ( e to e1
        ; semilattice to semilattice1
        ; identity-left  to identity-left1
        ; _<>_ to _<>1_)
    open BoundedSemilattice bsl2 renaming
        ( e to e2
        ; semilattice to semilattice2
        ; identity-left  to identity-left2
        ; _<>_ to _<>2_)
    open Semilattice (semilatticeProduct semilattice1 semilattice2)

    boundedSemilatticeProduct : BoundedSemilattice (L1 -x- L2)
    BoundedSemilattice.e boundedSemilatticeProduct = e1 , e2
    BoundedSemilattice.semilattice boundedSemilatticeProduct = semilatticeProduct semilattice1 semilattice2
    BoundedSemilattice.identity-left boundedSemilatticeProduct {x = (x1 , x2)} = 
        (e1 , e2) <> (x1 , x2)  =<>
        (e1 <>1 x1 , e2 <>2 x2) =< identity-left1 || _, e2 <>2 x2 >
        (x1 , e2 <>2 x2)        =< identity-left2 || x1 ,_ >
        (x1 , x2)               qed

    infixr 10 _-xBSLx-_
    _-xBSLx-_ = boundedSemilatticeProduct

boundedSemilatticeNProduct : (n : Nat) -> BoundedSemilattice L -> BoundedSemilattice (NTup L n)
boundedSemilatticeNProduct 0 bsl = UnitBoundedSemilattice
boundedSemilatticeNProduct 1 bsl = bsl
boundedSemilatticeNProduct (1+ 1+ n) bsl = bsl -xBSLx- boundedSemilatticeNProduct (1+ n) bsl

_BSL^_ : BoundedSemilattice L -> (n : Nat) -> BoundedSemilattice (NTup L n)
_BSL^_ = flip boundedSemilatticeNProduct


module _ 
    {bslX : BoundedSemilattice X}
    {bslY : BoundedSemilattice Y}  where
    open BoundedSemilattice using (semilattice ; idempotent)
    open BoundedSemilattice bslX using () renaming (e to e`$\subX$` ; _P_ to _P`$\subX$`_ ; _<>_ to _<>`$\subX$`_)
    open BoundedSemilattice bslY using () renaming (e to e`$\subY$` ; _P_ to _P`$\subY$`_ ; _<>_ to _<>`$\subY$`_)

    semilatticeProductSndInjection : BoundedSemilatticeInjection bslY (bslX -xBSLx- bslY)
    Injection.inf (SemilatticeInjection.injection (BoundedSemilatticeInjection.semilattice-injection semilatticeProductSndInjection)) = e`$\subX$` ,_
    Injection.outf (SemilatticeInjection.injection (BoundedSemilatticeInjection.semilattice-injection semilatticeProductSndInjection)) = snd
    Injection.outfoinf-id (SemilatticeInjection.injection (BoundedSemilatticeInjection.semilattice-injection semilatticeProductSndInjection)) = refl
    SemilatticeInjection.pres-inf (BoundedSemilatticeInjection.semilattice-injection semilatticeProductSndInjection) = sym (idempotent bslX) || _, _
    SemilatticeInjection.pres-outf (BoundedSemilatticeInjection.semilattice-injection semilatticeProductSndInjection) = refl
    BoundedSemilatticeInjection.pres-inf-e semilatticeProductSndInjection = refl

    semilatticeProductFstInjection : BoundedSemilatticeInjection bslX (bslX -xBSLx- bslY)
    Injection.inf (SemilatticeInjection.injection (BoundedSemilatticeInjection.semilattice-injection semilatticeProductFstInjection)) = _, e`$\subY$`
    Injection.outf (SemilatticeInjection.injection (BoundedSemilatticeInjection.semilattice-injection semilatticeProductFstInjection)) = fst
    Injection.outfoinf-id (SemilatticeInjection.injection (BoundedSemilatticeInjection.semilattice-injection semilatticeProductFstInjection)) = refl
    SemilatticeInjection.pres-inf (BoundedSemilatticeInjection.semilattice-injection semilatticeProductFstInjection) = sym (idempotent bslY) || _ ,_
    SemilatticeInjection.pres-outf (BoundedSemilatticeInjection.semilattice-injection semilatticeProductFstInjection) = refl
    BoundedSemilatticeInjection.pres-inf-e semilatticeProductFstInjection = refl

module _ where
    open NatOp
    stdNatSemilattice : Semilattice Nat
    RawSemilattice._<>_ (Semilattice.rawSemilattice stdNatSemilattice) = max
    IsSemilattice.associative (Semilattice.isSemilattice stdNatSemilattice) {x} {y} {z} = assoc-max {x} {y} {z}
    IsSemilattice.commutative (Semilattice.isSemilattice stdNatSemilattice) {x} {y} = comm-max {x} {y}
    IsSemilattice.idempotent (Semilattice.isSemilattice stdNatSemilattice) = idem-max