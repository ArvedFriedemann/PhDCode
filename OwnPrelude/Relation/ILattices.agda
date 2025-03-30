{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Relation.ILattices where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.IPreOrders
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Categorical.IMonoids
open import OwnPrelude.Data.NTuples
open import OwnPrelude.Relation.Lattices

open ExistsSyntax

private
    variable
        h i j k k' l i' j' u : Level
        n n' : Nat
        A B C X Y Z L L1 L2 S S1 S2 : Set i
        F G M : Set i -> Set j
        a b c x y z m x1 x2 y1 y2 z1 z2 Qx Qy sl bsl Q : A
        f g : A -> B

module _ {L : Set i} (rsl : RawSemilattice L) where
    open RawSemilattice rsl using () renaming (_<>_ to _<>'_ ; _P_ to _P'_)
    record RawISemilattice (Q : L -> Set j) : Set (i ~U~ j) where
        infixr 20 _<>_
        field
            _<>_ : {a : L} -> Q a -> {b : L} -> Q b -> Q (a <>' b)

        _P_ : Q a -> Q b -> Set (i ~U~ j)
        _P_ {a} {b} x y = exists[ aPb of (a P' b) ] (x <> y =< aPb || Q >= y)

module _ {L : Set i} (sl : Semilattice L) where
    private module L = Semilattice sl
    open L using () renaming (_<>_ to _<>'_)
    
    record IsISemilattice 
        {Q : L -> Set j}
        (rawISemilattice : RawISemilattice (Semilattice.rawSemilattice sl) Q) : Set (i ~U~ j) where
        open RawISemilattice rawISemilattice
        field
            associative : {Qx : Q x} {Qy : Q y} {Qz : Q z} -> Qx <> (Qy <> Qz) =< L.associative || Q >= (Qx <> Qy) <> Qz
            commutative : {Qx : Q x} {Qy : Q y} -> Qx <> Qy =< L.commutative || Q >= Qy <> Qx
            idempotent  : {Qx : Q x} -> Qx <> Qx =< L.idempotent || Q >= Qx
        
        isIPreOrder : IsIPreOrder {A = Q} (\a b -> _P_ {a} {b})
        IsIPreOrder.reflexive isIPreOrder = L.idempotent , idempotent
        IsIPreOrder.transitive isIPreOrder {i = a} {j = b} {k = c} {a = Qa} {b = Qb} {c = Qc} (ab=b , QaQb=Qb) (bc=c , QbQc=Qc) = 
            (
                a <>' c          =< (sym bc=c || a <>'_) > 
                (a <>' b <>' c)  =< L.associative >
                (a <>' b) <>' c  =< ab=b || _<>' c >
                b <>' c          =< bc=c > 
                c                qed
            ) , (
                Qa <> Qc         =<Sig[ Q ] (sym' QbQc=Qc) ||P (Qa <>_) >
                (Qa <> Qb <> Qc) =<Sig[ Q ] associative > 
                (Qa <> Qb) <> Qc =<Sig[ Q ] QaQb=Qb ||P (_<> Qc) >  
                Qb <> Qc         =<Sig[ Q ] QbQc=Qc > 
                Qc               qed
            )

        open IsIPreOrder isIPreOrder public hiding (_P_)

        directional : {Qx : Q x} {Qy : Q y} -> Qx P (Qx <> Qy)
        directional {x} {y} {Qx} {Qy} = 
            (
                x <>' (x <>' y) =< L.associative >
                (x <>' x) <>' y =< L.idempotent || _<>' y >
                x <>' y        qed
            ) , (
                Qx <> (Qx <> Qy) =<Sig[ Q ] associative > 
                (Qx <> Qx) <> Qy =<Sig[ Q ] idempotent ||P (_<> Qy) > 
                Qx <> Qy qed
            )

        directional' : Qx P (Qy <> Qx)
        directional' {Qx} {Qy} = coerce (commutative ||P (Qx P_)) directional

    -- postulate isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid isPreOrder)

    record ISemilattice (Q : L -> Set j) : Set (i ~U~ j) where
        field
            rawISemilattice : RawISemilattice (Semilattice.rawSemilattice sl) Q
            isISemilattice  : IsISemilattice rawISemilattice
        open RawISemilattice rawISemilattice public
        open IsISemilattice  isISemilattice  public

module _ {L : Set i} (bsl : BoundedSemilattice L) where
    private module L = BoundedSemilattice bsl
    open L using () renaming (_<>_ to _<>'_)

    record BoundedISemilattice (Q : L -> Set j) : Set (i ~U~ j) where
        field
            e : Q L.e
            isemilattice : ISemilattice (BoundedSemilattice.semilattice bsl) Q
        open ISemilattice isemilattice public
        field
            identity-left : {Qx : Q x} -> e <> Qx =< L.identity-left || Q >= Qx

        identity-right : {Qx : Q x} -> Qx <> e =< L.identity-right || Q >= Qx
        identity-right {x} {Qx} = 
            Qx <> e =<Sig[ Q ] commutative >
            e <> Qx =<Sig[ Q ] identity-left >
            Qx qed

        -- unique-e : {e' : L} -> (forall x -> e' <> x === x) -> e' === e
        -- unique-e {e'} e-id = 
        --     e'      =< sym identity-right > 
        --     e' <> e =< e-id e >
        --     e       qed

MeetISemilattice = ISemilattice

module MeetISemilattice (isemilattice : ISemilattice sl Q) where
    open ISemilattice isemilattice public 
        renaming 
            ( _<>_ to _/\_
            ; _P_ to _leq_
            ; associative    to associative-/\
            ; commutative    to commutative-/\
            ; idempotent     to idempotent-/\
            ; isIPreOrder to isIPreOrder-/\
            -- ; isIMonoid      to isIMonoid-/\
            ; directional    to increase
            ; directional'   to increase' 
            ; rawIMonoid     to rawIMonoid-/\)

BoundedMeetISemilattice = BoundedISemilattice

module BoundedMeetISemilattice (boundedISemilattice : BoundedISemilattice bsl Q) where
    open BoundedISemilattice boundedISemilattice   
    open MeetISemilattice isemilattice public
    open BoundedISemilattice boundedISemilattice public
        using () renaming 
            ( e to top
            ; identity-left  to identity-left-/\
            ; identity-right to identity-right-/\ )

JoinISemilattice = ISemilattice

module JoinISemilattice (isemilattice : ISemilattice sl Q) where
    open ISemilattice isemilattice public 
        renaming 
            ( _<>_ to _\/_
            ; _P_ to _geq_
            ; associative    to associative-\/
            ; commutative    to commutative-\/
            ; idempotent     to idempotent-\/
            ; isIPreOrder to isIPreOrder-\/
            -- ; isIMonoid      to isIMonoid-\/
            ; directional    to decrease
            ; directional'   to decrease' 
            ; rawIMonoid     to rawIMonoid-\/)

BoundedJoinISemilattice = BoundedISemilattice

module BoundedJoinISemilattice (boundedISemilattice : BoundedISemilattice bsl Q) where
    open BoundedISemilattice boundedISemilattice 
    open JoinISemilattice isemilattice public
    open BoundedISemilattice boundedISemilattice public
        using () renaming
            ( e to bot
            ; identity-left  to identity-left-\/
            ; identity-right to identity-right-\/ )

module _ {L : Set i} (lat : Lattice L) where
    private module L = Lattice lat
    record ILattice (Q : L -> Set j) : Set (i ~U~ j) where
        field
            boundedMeetISemilattice : BoundedMeetISemilattice (Lattice.boundedMeetSemilattice lat) Q
            boundedJoinISemilattice : BoundedJoinISemilattice (Lattice.boundedJoinSemilattice lat) Q
        open BoundedMeetISemilattice boundedMeetISemilattice public
            renaming
                ( _/\_ to infixr 10 _/\_ )
        open BoundedJoinISemilattice boundedJoinISemilattice public
            renaming 
                ( _\/_ to infixr 9 _\/_ )
        field        
            absorb-/\ : {Qx : Q x} {Qy : Q y} -> Qx /\ (Qx \/ Qy) =< L.absorb-/\ || Q >= Qx
            absorb-\/ : {Qx : Q x} {Qy : Q y} -> Qx \/ (Qx /\ Qy) =< L.absorb-\/ || Q >= Qx



-- record SemilatticeInjection {X : Set i} {Y : Set j} 
--         (bslX : Semilattice X)
--         (bslY : Semilattice Y) : Set (i ~U~ j) where
--         field
--             injection : Injection X Y
--         open Injection injection public
--         open Semilattice bslX renaming (_P_ to _P`$\subX$`_ ; _<>_ to _<>`$\subX$`_)
--         open Semilattice bslY renaming (_P_ to _P`$\subY$`_ ; _<>_ to _<>`$\subY$`_)
--         field
--             pres-inf  : inf  (a <>`$\subX$` b) === (inf  a <>`$\subY$` inf  b)
--             pres-outf : outf (a <>`$\subY$` b) === (outf a <>`$\subX$` outf b)

--         pres-inf-rel  : a P`$\subX$` b -> (inf a) P`$\subY$` (inf b)
--         pres-inf-rel {a} {b} aPb = 
--             (inf a) <>`$\subY$` (inf b) =< sym pres-inf >
--             inf (a <>`$\subX$` b)       =< aPb || inf >
--             inf b                       qed

--         pres-outf-rel : a P`$\subY$` b -> (outf a) P`$\subX$` (outf b)
--         pres-outf-rel {a} {b} aPb =
--             (outf a) <>`$\subX$` (outf b) =< sym pres-outf >
--             outf (a <>`$\subY$` b)        =< aPb || outf >
--             outf b                        qed

-- module _ {bsl : Semilattice X} where
--     semilattice-injection-reflexive : SemilatticeInjection bsl bsl
--     SemilatticeInjection.injection semilattice-injection-reflexive = injection-refl
--     SemilatticeInjection.pres-inf  semilattice-injection-reflexive = refl
--     SemilatticeInjection.pres-outf semilattice-injection-reflexive = refl

-- module _ {bslX : Semilattice X} {bslY : Semilattice Y} {bslZ : Semilattice Z} where
--     open SemilatticeInjection
--     open Semilattice bslX using () renaming (_<>_ to _<>`$\subX$`_)
--     open Semilattice bslY using () renaming (_<>_ to _<>`$\subY$`_)
--     open Semilattice bslZ using () renaming (_<>_ to _<>`$\subZ$`_)
--     semilattice-injection-transitive : 
--         SemilatticeInjection bslX bslY ->
--         SemilatticeInjection bslY bslZ -> 
--         SemilatticeInjection bslX bslZ
--     injection (semilattice-injection-transitive siXY siYZ) = injection-trans (injection siXY) (injection siYZ)
--     pres-inf  (semilattice-injection-transitive siXY siYZ) {a} {b} =
--         inf siYZ (inf siXY (a <>`$\subX$` b))                     =< pres-inf siXY || inf siYZ >
--         inf siYZ (inf siXY a <>`$\subY$` inf siXY b)              =< pres-inf siYZ >
--         (inf siYZ (inf siXY a) <>`$\subZ$` inf siYZ (inf siXY b)) qed
--     pres-outf (semilattice-injection-transitive siXY siYZ) {a} {b} = 
--         outf siXY (outf siYZ (a <>`$\subZ$` b))                       =< pres-outf siYZ || outf siXY >
--         outf siXY (outf siYZ a <>`$\subY$` outf siYZ b)               =< pres-outf siXY >
--         (outf siXY (outf siYZ a) <>`$\subX$` outf siXY (outf siYZ b)) qed

-- module _ {X : Set i} {Y : Set j} where
--     open BoundedSemilattice using (semilattice ; idempotent ; unique-e)
--     record BoundedSemilatticeInjection (b1 : BoundedSemilattice X) (b2 : BoundedSemilattice Y) : Set (i ~U~ j) where
--         field
--             semilattice-injection : SemilatticeInjection (semilattice b1) (semilattice b2)
--         open SemilatticeInjection semilattice-injection public
--         open BoundedSemilattice b1 using () renaming (e to e`$\subX$` ; _<>_ to _<>`$\subX$`_)
--         open BoundedSemilattice b2 using () renaming (e to e`$\subY$` ; _<>_ to _<>`$\subY$`_)
--         field
--             pres-inf-e : inf (e`$\subX$`) === e`$\subY$`

--         pres-outf-e : outf (e`$\subY$`) === e`$\subX$`
--         pres-outf-e = 
--             outf (e`$\subY$`)     =< sym pres-inf-e || outf >
--             outf (inf e`$\subX$`) =< outfoinf-id || (_$ e`$\subX$`) >
--             e`$\subX$`            qed

-- module _ {bsl : BoundedSemilattice X} where
--     bounded-semilattice-injection-reflexive : BoundedSemilatticeInjection bsl bsl
--     BoundedSemilatticeInjection.semilattice-injection bounded-semilattice-injection-reflexive = semilattice-injection-reflexive
--     BoundedSemilatticeInjection.pres-inf-e bounded-semilattice-injection-reflexive = refl

-- module _ {bslX : BoundedSemilattice X} {bslY : BoundedSemilattice Y} {bslZ : BoundedSemilattice Z} where
--     open BoundedSemilatticeInjection
--     bounded-semilattice-injection-transitive : 
--         BoundedSemilatticeInjection bslX bslY ->
--         BoundedSemilatticeInjection bslY bslZ -> 
--         BoundedSemilatticeInjection bslX bslZ
--     semilattice-injection (bounded-semilattice-injection-transitive sirXY sirYZ) = semilattice-injection-transitive (semilattice-injection sirXY) (semilattice-injection sirYZ)
--     pres-inf-e (bounded-semilattice-injection-transitive sirXY sirYZ) = trans (pres-inf-e sirXY || inf sirYZ) (pres-inf-e sirYZ)