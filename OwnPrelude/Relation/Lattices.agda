{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-} 
module OwnPrelude.Relation.Lattices where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Categorical.IMonoids
open import OwnPrelude.Data.NTuples

open ExistsSyntax

private
    variable
        h i j k k' l i' j' u : Level
        n n' : Nat
        A B C X Y Z L L1 L2 S S1 S2 : Set i
        F G M : Set i -> Set j
        a b c x x' y y' z m x1 x2 y1 y2 z1 z2 : A
        f g : A -> B

record RawSemilattice (L : Set i) : Set i where
    infixr 20 _<>_
    field
        _<>_ : L -> L -> L

    _P_ : L -> L -> Set i
    x P y = x <> y === y

record IsSemilattice 
    {L : Set i} 
    (rawSemilattice : RawSemilattice L) : Set i where
    open RawSemilattice rawSemilattice
    field
        associative : x <> (y <> z) === (x <> y) <> z
        commutative : x <> y === y <> x
        idempotent  : x <> x === x
    
    isPreOrder : IsPreOrder _P_
    IsPreOrder.reflexive isPreOrder = idempotent
    IsPreOrder.transitive isPreOrder {a} {b} {c} ab=b bc=c = 
        a <> c        =< sym bc=c || a <>_ >
        a <> b <> c   =< associative >
        (a <> b) <> c =< ab=b || _<> c >
        b <> c        =< bc=c >
        c             qed

    open IsPreOrder isPreOrder public

    switch-op : x <> y <> z === y <> x <> z
    switch-op {x} {y} {z} =
        x <> y <> z   =< associative >
        (x <> y) <> z =< commutative || _<> z >
        (y <> x) <> z =< sym associative >
        y <> x <> z   qed

    symmetric-eq : x P y -> y P x -> x === y
    symmetric-eq {x} {y} xPy yPx = 
        x        =< sym yPx > 
        (y <> x) =< commutative > 
        (x <> y) =< xPy > 
        y        qed

    -- \tagcode{DIRECTIONAL}

    directional : x P (x <> y)
    directional {x} {y} = 
        x <> (x <> y) =< associative >
        (x <> x) <> y =< idempotent || _<> y >
        x <> y        qed

    directional' : x P (y <> x)
    directional' {x} {y} = coerce (commutative || x P_) directional

    mergeP : x P y -> x' P y' -> (x <> x') P (y <> y')
    mergeP {x} {y} {x'} {y'} xPy x'Py' = 
        (x <> x') <> y <> y' =< commutative || (\h -> h <> y <> y') >
        (x' <> x) <> y <> y' =< associative >
        ((x' <> x) <> y) <> y' =< sym associative || _<> y' >
        (x' <> (x <> y)) <> y' =< xPy || (\h -> (x' <> h) <> y') >
        (x' <> y) <> y' =< commutative || _<> y' >
        (y <> x') <> y' =< sym associative >
        y <> (x' <> y') =< x'Py' || y <>_ >
        y <> y' qed

    mergeP' : x P y -> x P y' -> x P (y <> y')
    mergeP' {x} {y} {y'} xPy xPy' = 
        x <> y <> y' =< sym idempotent || (\h -> h <> y <> y') >
        (x <> x) <> y <> y' =< mergeP xPy xPy' >
        y <> y' qed
    
    addP : (z : L) -> x P y -> (x <> z) P (y <> z)
    addP z xPy = mergeP xPy reflexive

    -- postulate isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid isPreOrder)
    POMonoidType = IsIMonoid (IsPreOrder.rawIMonoid isPreOrder)

record Semilattice (L : Set i) : Set i where
    field
        rawSemilattice : RawSemilattice L
        isSemilattice  : IsSemilattice rawSemilattice
    open RawSemilattice rawSemilattice public
    open IsSemilattice  isSemilattice  public

record BoundedSemilattice (L : Set i) : Set i where
    field
        e : L
        semilattice : Semilattice L
    open Semilattice semilattice public
    field
        identity-left : e <> x === x

    identity-right : x <> e === x
    identity-right {x} = 
        x <> e =< commutative > 
        e <> x =< identity-left >
        x        qed

    unique-e : {e' : L} -> (forall x -> e' <> x === x) -> e' === e
    unique-e {e'} e-id = 
        e'      =< sym identity-right > 
        e' <> e =< e-id e >
        e       qed

MeetSemilattice = Semilattice

module MeetSemilattice (semilattice : Semilattice L) where
    open Semilattice semilattice public 
        renaming 
            ( _<>_ to _/\_
            ; _P_ to _leq_
            ; associative    to associative-/\
            ; commutative    to commutative-/\
            ; idempotent     to idempotent-/\
            ; switch-op      to switch-op-/\
            ; isPreOrder to isPreOrder-/\
            -- ; isIMonoid      to isIMonoid-/\
            ; POMonoidType   to POMonoidType-/\
            ; symmetric-eq   to symmetric-eq-/\
            ; directional    to increase
            ; directional'   to increase' 
            ; mergeP         to merge-/\
            ; mergeP'        to merge-/\'
            ; addP           to add-/\
            ; rawIMonoid     to rawIMonoid-/\)

BoundedMeetSemilattice = BoundedSemilattice

module BoundedMeetSemilattice (boundedSemilattice : BoundedSemilattice L) where
    open BoundedSemilattice boundedSemilattice   
    open MeetSemilattice semilattice public
    open BoundedSemilattice boundedSemilattice public
        using () renaming 
            ( e to top
            ; identity-left  to identity-left-/\
            ; identity-right to identity-right-/\ )

JoinSemilattice = Semilattice

module JoinSemilattice (semilattice : Semilattice L) where
    open Semilattice semilattice public 
        renaming 
            ( _<>_ to _\/_
            ; _P_ to _geq_
            ; _P-<=_ to _P->=_
            ; associative    to associative-\/
            ; commutative    to commutative-\/
            ; idempotent     to idempotent-\/
            ; switch-op      to switch-op-\/
            ; isPreOrder to isPreOrder-\/
            -- ; isIMonoid      to isIMonoid-\/
            ; POMonoidType   to POMonoidType-\/
            ; symmetric-eq   to symmetric-eq-\/
            ; directional    to decrease
            ; directional'   to decrease'
            ; mergeP         to merge-\/
            ; mergeP'        to merge-\/'
            ; addP           to add-\/
            ; rawIMonoid     to rawIMonoid-\/)

BoundedJoinSemilattice = BoundedSemilattice

module BoundedJoinSemilattice (boundedSemilattice : BoundedSemilattice L) where
    open BoundedSemilattice boundedSemilattice 
    open JoinSemilattice semilattice public
    open BoundedSemilattice boundedSemilattice public
        using () renaming
            ( e to bot
            ; identity-left  to identity-left-\/
            ; identity-right to identity-right-\/ )

record Lattice (L : Set i) : Set i where
    field
        boundedMeetSemilattice : BoundedMeetSemilattice L
        boundedJoinSemilattice : BoundedJoinSemilattice L
    open BoundedMeetSemilattice boundedMeetSemilattice public
        renaming
            ( _/\_ to infixr 10 _/\_ )
    open BoundedJoinSemilattice boundedJoinSemilattice public
        renaming 
            ( _\/_ to infixr 9 _\/_ )
    field        
        absorb-/\ : a /\ (a \/ b) === a
        absorb-\/ : a \/ (a /\ b) === a

    meetSemilattice = BoundedSemilattice.semilattice boundedMeetSemilattice
    joinSemilattice = BoundedSemilattice.semilattice boundedJoinSemilattice

    leq-join : forall {a b} -> (a \/ b) leq a
    leq-join {a} {b} = 
        (a \/ b) /\ a =< commutative-/\ >
        a /\ (a \/ b) =< absorb-/\ >
        a qed

record DistributiveLattice (L : Set i) : Set i where
    field
        lattice : Lattice L
    open Lattice lattice public
    field
        distributive-/\ : a /\ (b \/ c) === (a /\ b) \/ (a /\ c)
        distributive-\/ : a \/ (b /\ c) === (a \/ b) /\ (a \/ c)

    sub-\/ : (z : L) -> x leq y -> (x \/ z) leq (y \/ z)
    sub-\/ {x} {y} z xleqy = 
        (x \/ z) /\ (y \/ z) =<( \i -> commutative-\/ {x = x} {y = z} i /\ commutative-\/ {x = y} {y = z} i) >
        (z \/ x) /\ (z \/ y) =< sym distributive-\/ >
        z \/ (x /\ y) =< commutative-\/ >
        (x /\ y) \/ z =< xleqy || _\/ z >
        y \/ z qed
        


-- \tagcode{SemilatticeInjection}

record SemilatticeInjection {X : Set i} {Y : Set j} 
        (bslX : Semilattice X)
        (bslY : Semilattice Y) : Set (i ~U~ j) where
        field
            injection : Injection X Y
        open Injection injection public
        open Semilattice bslX renaming (_P_ to _P`$\subX$`_ ; _<>_ to _<>`$\subX$`_)
        open Semilattice bslY renaming (_P_ to _P`$\subY$`_ ; _<>_ to _<>`$\subY$`_)
        field
            pres-inf  : inf  (a <>`$\subX$` b) === (inf  a <>`$\subY$` inf  b)
            pres-outf : outf (a <>`$\subY$` b) === (outf a <>`$\subX$` outf b)

        pres-inf-rel  : a P`$\subX$` b -> (inf a) P`$\subY$` (inf b)
        pres-inf-rel {a} {b} aPb = 
            (inf a) <>`$\subY$` (inf b) =< sym pres-inf >
            inf (a <>`$\subX$` b)       =< aPb || inf >
            inf b                       qed

        pres-outf-rel : a P`$\subY$` b -> (outf a) P`$\subX$` (outf b)
        pres-outf-rel {a} {b} aPb =
            (outf a) <>`$\subX$` (outf b) =< sym pres-outf >
            outf (a <>`$\subY$` b)        =< aPb || outf >
            outf b                        qed

module _ {bsl : Semilattice X} where
    semilattice-injection-reflexive : SemilatticeInjection bsl bsl
    SemilatticeInjection.injection semilattice-injection-reflexive = injection-refl
    SemilatticeInjection.pres-inf  semilattice-injection-reflexive = refl
    SemilatticeInjection.pres-outf semilattice-injection-reflexive = refl

module _ {bslX : Semilattice X} {bslY : Semilattice Y} {bslZ : Semilattice Z} where
    open SemilatticeInjection
    open Semilattice bslX using () renaming (_<>_ to _<>`$\subX$`_)
    open Semilattice bslY using () renaming (_<>_ to _<>`$\subY$`_)
    open Semilattice bslZ using () renaming (_<>_ to _<>`$\subZ$`_)
    semilattice-injection-transitive : 
        SemilatticeInjection bslX bslY ->
        SemilatticeInjection bslY bslZ -> 
        SemilatticeInjection bslX bslZ
    injection (semilattice-injection-transitive siXY siYZ) = injection-trans (injection siXY) (injection siYZ)
    pres-inf  (semilattice-injection-transitive siXY siYZ) {a} {b} =
        inf siYZ (inf siXY (a <>`$\subX$` b))                     =< pres-inf siXY || inf siYZ >
        inf siYZ (inf siXY a <>`$\subY$` inf siXY b)              =< pres-inf siYZ >
        (inf siYZ (inf siXY a) <>`$\subZ$` inf siYZ (inf siXY b)) qed
    pres-outf (semilattice-injection-transitive siXY siYZ) {a} {b} = 
        outf siXY (outf siYZ (a <>`$\subZ$` b))                       =< pres-outf siYZ || outf siXY >
        outf siXY (outf siYZ a <>`$\subY$` outf siYZ b)               =< pres-outf siXY >
        (outf siXY (outf siYZ a) <>`$\subX$` outf siXY (outf siYZ b)) qed

module _ {X : Set i} {Y : Set j} where
    open BoundedSemilattice using (semilattice ; idempotent ; unique-e)
    record BoundedSemilatticeInjection (b1 : BoundedSemilattice X) (b2 : BoundedSemilattice Y) : Set (i ~U~ j) where
        field
            semilattice-injection : SemilatticeInjection (semilattice b1) (semilattice b2)
        open SemilatticeInjection semilattice-injection public
        open BoundedSemilattice b1 using () renaming (e to e`$\subX$` ; _<>_ to _<>`$\subX$`_)
        open BoundedSemilattice b2 using () renaming (e to e`$\subY$` ; _<>_ to _<>`$\subY$`_)
        field
            pres-inf-e : inf (e`$\subX$`) === e`$\subY$`

        pres-outf-e : outf (e`$\subY$`) === e`$\subX$`
        pres-outf-e = 
            outf (e`$\subY$`)     =< sym pres-inf-e || outf >
            outf (inf e`$\subX$`) =< outfoinf-id || (_$ e`$\subX$`) >
            e`$\subX$`            qed

module _ {bsl : BoundedSemilattice X} where
    bounded-semilattice-injection-reflexive : BoundedSemilatticeInjection bsl bsl
    BoundedSemilatticeInjection.semilattice-injection bounded-semilattice-injection-reflexive = semilattice-injection-reflexive
    BoundedSemilatticeInjection.pres-inf-e bounded-semilattice-injection-reflexive = refl

module _ {bslX : BoundedSemilattice X} {bslY : BoundedSemilattice Y} {bslZ : BoundedSemilattice Z} where
    open BoundedSemilatticeInjection
    bounded-semilattice-injection-transitive : 
        BoundedSemilatticeInjection bslX bslY ->
        BoundedSemilatticeInjection bslY bslZ -> 
        BoundedSemilatticeInjection bslX bslZ 
    semilattice-injection (bounded-semilattice-injection-transitive sirXY sirYZ) = semilattice-injection-transitive (semilattice-injection sirXY) (semilattice-injection sirYZ)
    pres-inf-e (bounded-semilattice-injection-transitive sirXY sirYZ) = trans (pres-inf-e sirXY || inf sirYZ) (pres-inf-e sirYZ)