{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.BiThresholdsAndContainersPartII where

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d e f g h i j k l m n p p1 p2 p3 p' q r s s' s1 s2 s3 t u v w x y z fm i' j' k' l' A B C X Y K M F alg px py pz pm x=y y=z x=z mon Qx Qy Qz : ST

-- \tagcode{BiThresholdsAndContainersPtII}

module InitialExample where
    open import OwnPrelude.Relation.Lattices
    
    data List (A : Set) : Set where
        [] : List A
        _::_ : A -> List A -> List A

    data LatList (A : Set) : Set where
        topList : LatList A
        botList : LatList A
        [] : LatList A
        _::_ : A -> LatList A -> LatList A

    module _ {A : Set} {latA : Semilattice A} where
        open Semilattice latA renaming (_<>_ to _/\`$\subA$`_)

        _/\_ : LatList A -> LatList A -> LatList A
        topList /\ b           = b
        botList /\ b           = botList
        a /\ topList           = a
        a /\ botList           = botList
        [] /\ []               = []
        (x :: xs) /\ (y :: ys) = (x /\`$\subA$` y) :: (xs /\ ys)
        _ /\ _                 = botList

        
open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open PropositionalEq using () renaming (_===_ to _=P=_ ; _=/=_ to _=/P/=_ ; refl to reflP)
module PEq = PropositionalEq
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.VarAsms renaming (module MonadNames to VarAsmsMonadNames)
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.TrivialLattices
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.ILattices
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Data.Containers

{-# DISPLAY LiftL j Zero = PolyZero.Zero #-}

open ExistsSyntax


module FreeLattice {A : Set i} (lat : Lattice A) where
    open Lattice lat

    data FreeLattice : Set i where
        latVal : A -> FreeLattice
        _/\F_ : FreeLattice -> FreeLattice -> FreeLattice
        _\/F_ : FreeLattice -> FreeLattice -> FreeLattice
        associative-/\F    : a /\F (b /\F c) ===  (a /\F b) /\F c
        commutative-/\F    : a /\F b ===  b /\F a
        idempotent-/\F     : a /\F a === a
        identity-left-/\F  : latVal top /\F a === a

        associative-\/F    : a \/F (b \/F c) ===  (a \/F b) \/F c
        commutative-\/F    : a \/F b ===  b \/F a
        idempotent-\/F     : a \/F a === a
        identity-left-\/F  : latVal bot \/F a === a

        absorb-/\F : a /\F (a \/F b) === a
        absorb-\/F : a \/F (a /\F b) === a

    -- unfreeLat : FreeLattice -> A
    -- unfreeLat = {!!}
            
    freeLattice : Lattice FreeLattice
    freeLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.e = latVal top
    freeLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.rawSemilattice .RawSemilattice._<>_ = _/\F_
    freeLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative = associative-/\F
    freeLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative = commutative-/\F
    freeLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent = idempotent-/\F
    freeLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.identity-left = identity-left-/\F
    freeLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.e = latVal bot
    freeLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.rawSemilattice .RawSemilattice._<>_ = _\/F_
    freeLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative = associative-\/F
    freeLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative = commutative-\/F
    freeLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent = idempotent-\/F
    freeLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.identity-left = identity-left-\/F
    freeLattice .Lattice.absorb-/\ = absorb-/\F
    freeLattice .Lattice.absorb-\/ = absorb-\/F

module SigmaLattices {A : Set i} (LatA : Lattice A) {B : A -> Set j} (LatB : ILattice LatA B) where
    module LatA = Lattice LatA
    module LatB = ILattice LatB
    
    latticeSig : Lattice (Sigma A B)
    latticeSig .Lattice.boundedMeetSemilattice .BoundedSemilattice.e = LatA.top , LatB.top
    latticeSig .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.rawSemilattice .RawSemilattice._<>_ (s1 , p1) (s2 , p2) = (s1 LatA./\ s2) , (p1 LatB./\ p2)
    latticeSig .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {x = x , px} {y = y , py} {z = z , pz} i = LatA.associative-/\ {x} {y} {z} i , LatB.associative-/\ {Qx = px} {Qy = py} {Qz = pz} i
    latticeSig .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {x = x , px} {y = y , py} i = LatA.commutative-/\ {x} {y} i , LatB.commutative-/\ {Qx = px} {Qy = py} i 
    latticeSig .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent  {x = x , px} i = LatA.idempotent-/\ {x} i , LatB.idempotent-/\ {Qx = px} i
    latticeSig .Lattice.boundedMeetSemilattice .BoundedSemilattice.identity-left {x = x , px} i = LatA.identity-left-/\ {x} i , LatB.identity-left-/\ {Qx = px} i
    latticeSig .Lattice.boundedJoinSemilattice .BoundedSemilattice.e = LatA.bot , LatB.bot
    latticeSig .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.rawSemilattice .RawSemilattice._<>_ (s1 , p1) (s2 , p2) = (s1 LatA.\/ s2) , (p1 LatB.\/ p2)
    latticeSig .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {x = x , px} {y = y , py} {z = z , pz} i = LatA.associative-\/ {x} {y} {z} i , LatB.associative-\/ {Qx = px} {Qy = py} {Qz = pz} i
    latticeSig .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {x = x , px} {y = y , py} i = LatA.commutative-\/ {x} {y} i , LatB.commutative-\/ {Qx = px} {Qy = py} i 
    latticeSig .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent  {x = x , px} i = LatA.idempotent-\/ {x} i , LatB.idempotent-\/ {Qx = px} i
    latticeSig .Lattice.boundedJoinSemilattice .BoundedSemilattice.identity-left {x = x , px} i = LatA.identity-left-\/ {x} i , LatB.identity-left-\/ {Qx = px} i
    latticeSig .Lattice.absorb-/\ {a = a , pa} {b = b , pb} i = LatA.absorb-/\ {a} {b} i , LatB.absorb-/\ {Qx = pa} {Qy = pb} i
    latticeSig .Lattice.absorb-\/ {a = a , pa} {b = b , pb} i = LatA.absorb-\/ {a} {b} i , LatB.absorb-\/ {Qx = pa} {Qy = pb} i

module ContainerVariables {C : Container i j} (LatS : Lattice (Container.S C)) {A : Set j} (LatP : ILattice LatS (\s -> Container.P C s -> A)) where
    open Container C hiding ([[_]])
    open Container using ([[_]])
    module LatS = Lattice LatS
    module LatP = ILattice LatP
    open SigmaLattices

    latticeLC : Lattice ([[ C ]] A)
    latticeLC = latticeSig LatS LatP

    
module TrivialContainerLattice {C : Container i j} (decEq : DecEq (Container.S C)) {A : Set k} (LatA : Lattice A) where
    open TrivialLattice decEq 
    open Container C hiding ([[_]])
    open Container using ([[_]])
    open DecEq decEq
    LatS = trivialLattice
    module LatS = Lattice LatS

    meet = LatS._/\_
    join = LatS._\/_

    -- \tagcode{latticedContainer}
    
    latticedContainer : Container i j
    latticedContainer = (S tb) |> (top: Zero bot: Zero val: P)

    P``tb = top: Zero bot: Zero val: P

    module LatA = Lattice LatA

    _/\P_ : {a : S tb} -> (P``tb a -> A) -> {b : S tb} -> (P``tb b -> A) -> (P``tb (a LatS./\ b) -> A)
    _/\P_ {(topTB)} pa {(b)} pb pm = pb pm
    _/\P_ {valTB x} pa {(topTB)} pb pm = pa pm
    _/\P_ {valTB x} pa {valTB y} pb pm = 
        ifDec x == y 
        then (\  x=y -> pa (coerce (meetVal x=y || P``tb) pm) LatA./\ pb (coerce ((x=y || valTB) || P``tb) (coerce (meetVal x=y || P``tb)  pm))) 
        else (\ ¬x=y -> absurd (coerce (meetBot ¬x=y || P``tb) pm))

    []/\P[] : (a b : S tb) -> (P``tb a -> A) -> (P``tb b -> A) -> (P``tb (a LatS./\ b) -> A)
    []/\P[] a b px py = _/\P_ {a = a} px {b = b} py

    syntax []/\P[] a b px py = px [ a ]/\P[ b ] py 

    _\/P_ : {a : S tb} -> (P``tb a -> A) -> {b : S tb} -> (P``tb b -> A) -> (P``tb (a LatS.\/ b) -> A)
    _\/P_ {(botTB)} pa {(b)} pb pm = pb pm
    _\/P_ {valTB x} pa {(botTB)} pb pm = pa pm
    _\/P_ {valTB x} pa {valTB y} pb pm = 
        ifDec x == y 
        then (\  x=y -> pa (coerce (joinVal x=y || P``tb) pm) LatA.\/ pb (coerce ((x=y || valTB) || P``tb) (coerce (joinVal x=y || P``tb)  pm))) 
        else (\ ¬x=y -> absurd (coerce (joinTop ¬x=y || P``tb) pm))

    []\/P[] : (a b : S tb) -> (P``tb a -> A) -> (P``tb b -> A) -> (P``tb (a LatS.\/ b) -> A)
    []\/P[] a b px py = _\/P_ {a = a} px {b = b} py

    syntax []\/P[] a b px py = px [ a ]\/P[ b ] py 

    PF : S tb -> Set (j ~U~ k)
    PF s = P``tb s -> A

    module LatticeProof where
        
        meetAssoc1 : forall {x y z Qx Qy Qz y=z} -> 
            (y == z === yes y=z) -> 
            Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =< (meetVal y=z || (valTB x) LatS./\_) || PF >=  Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm))
        meetAssoc1 {x} {y} {z} {Qx} {Qy} {Qz} {y=z} y=z===yes i = Qx [ valTB x ]/\P[ meetVal y=z i ] \pm -> 
            ifDec y=z===yes i
            then (\ y=z -> Qy (coercei1 (meetVal y=z || P``tb) {i} pm) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coercei1 (meetVal y=z || P``tb) {i} pm)))
            else \ ¬y=z -> absurd (coerce (meetBot ¬y=z || P``tb) (coercei0 (meetVal y=z || P``tb) {i} pm))

        meetAssoc2' : {Qy : PF (valTB y)} {Qz : PF (valTB z)} -> 
            (y == z === yes y=z) -> (x == y === yes x=y) -> 
            Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< meetVal x=y || PF >= (\pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) )
        meetAssoc2' {y} {z} {y=z} {x} {x=y} {Qx} {Qy} {Qz} y==z=yes x==y=yes i pm = 
            ifDec (x==y=yes i)
            then (\ x=y -> Qx (coercei1 (meetVal x=y || P``tb) {i} pm) LatA./\ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (meetVal x=y || P``tb) {i} pm)) LatA./\ Qz (coerce (y=z || valTB || P``tb) (coerce ((x=y || valTB) || P``tb) (coercei1 (meetVal x=y || P``tb) {i} pm))) )
            else (\ ¬x=y -> absurd (coerce (meetBot ¬x=y || P``tb) (coercei0 (meetVal x=y || P``tb) {i} pm)))

        meetAssoc2 : {Qy : PF (valTB y)} {Qz : PF (valTB z)} -> 
            (y == z === yes y=z) -> (x == y === yes x=y) -> 
            Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< meetVal x=y || PF >= (\pm -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) )
        meetAssoc2 {y} {z} {y=z} {x} {x=y} {Qx} {Qy} {Qz} y==z=yes x==y=yes = refl =<P meetAssoc2' {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes x==y=yes >= extens \pm -> LatA.associative-/\

        meetAssoc3' : 
            {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} ->
            (x == y === yes x=y) ->
            (y == z === yes y=z) ->
            (x == z === yes x=z) ->
            (pm : P``tb (valTB x)) ->
            (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) === 
            (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce (x=z || valTB || P``tb) (coerce (meetVal x=z || P``tb) (coerce (sym (meetVal x=z) || P``tb) pm)))
        meetAssoc3' {x=y} {y=z} {x=z} {Qx} {Qy} {Qz} x==y=yes y==z=yes x==z=yes pm = 
            (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) =< coerce-trans-subst (P``tb o valTB) x=y y=z || (\h -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (h pm)) >
            (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce (((trans x=y y=z) || valTB) || P``tb) pm) =< sym (encodeDec' (trans (sym' x==z=yes) (decEq-trans x==y=yes y==z=yes))) || (\h -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((h || valTB) || P``tb) pm)) >
            (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((x=z || valTB) || P``tb) pm) =< (sym (coerce-sym-subst P``tb (meetVal x=z)) || (\h -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((x=z || valTB) || P``tb) (h pm)))) >
            (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce (x=z || valTB || P``tb) (coerce (meetVal x=z || P``tb) (coerce (sym (meetVal x=z) || P``tb) pm))) qed

        meetAssoc3'' : 
            {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} -> 
            (x == z === yes x=z) -> 
            (\pm -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce (x=z || valTB || P``tb) (coerce (meetVal x=z || P``tb) (coerce (sym (meetVal x=z) || P``tb) pm))) ) =< sym (meetVal x=z) || PF >= (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz
        meetAssoc3'' {x} {y} {z} {x=z} {x=y} {Qx} {Qy} {Qz} x==z=yes i pm = 
            ifDec x==z=yes (~ i) 
            then (\  x=z -> (Qx (coercei1 (meetVal x=z || P``tb) {~ i} pm) LatA./\ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (meetVal x=z || P``tb) {~ i} pm))) LatA./\ Qz (coerce ((x=z || valTB) || P``tb) (coerce (meetVal x=z || P``tb) (coercei1 (sym (meetVal x=z) || P``tb) {i} pm)))  )
            else (\ ¬x=z -> absurd (coerce (meetBot ¬x=z || P``tb) (coercei0 (meetVal x=z || P``tb) {~ i} pm)))

        meetAssoc3 :
            {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} ->
            (x == y === yes x=y) ->
            (y == z === yes y=z) ->
            (x == z === yes x=z) ->
            (\pm -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) ) =< sym (meetVal x=z) || PF >= (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz
        meetAssoc3 {Qx} {Qy} {Qz} x==y=yes y==z=yes x==z=yes = extens (meetAssoc3' {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes y==z=yes x==z=yes) =<P meetAssoc3'' {Qx = Qx} {Qy = Qy} {Qz = Qz} x==z=yes >= refl
            
        meetAssoc4 : forall {x y z Qx Qy Qz x=y} ->
            (x == y === yes x=y) ->
            (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz =< sym (meetVal x=y) || LatS._/\ (valTB z) || PF >= (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz
        meetAssoc4 {x} {y} {z} {Qx} {Qy} {Qz} {x=y} x==y=yes i = (\pm -> 
            ifDec (x==y=yes (~ i)) 
            then (\  x=y -> Qx (coercei1 (meetVal x=y || P``tb) {~ i} pm) LatA./\ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (meetVal x=y || P``tb) {~ i} pm))) 
            else (\ ¬x=y -> absurd (coerce (meetBot ¬x=y || P``tb) (coercei0 (meetVal x=y || P``tb) {~ i} pm)))) 
            [ meetVal x=y (~ i) ]/\P[ valTB z ] Qz


        meetAssoc21' : forall {x y z Qx Qy Qz ¬y=z} -> 
            (y == z === no ¬y=z) -> 
            Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =< (meetBot ¬y=z || (valTB x) LatS./\_) || PF >=  Qx [ valTB x ]/\P[ botTB ] (\())
        meetAssoc21' {x} {y} {z} {Qx} {Qy} {Qz} {¬y=z} y=z===no i = Qx [ valTB x ]/\P[ meetBot ¬y=z i ] \pm -> 
            ifDec y=z===no i
            then (\  y=z -> Qy (coerce (meetVal y=z || P``tb) (coerce~i0 (meetBot ¬y=z || P``tb) {i} pm)) LatA./\ Qz (coerce (y=z || valTB || P``tb) (coerce (meetVal y=z || P``tb) (coerce~i0 (meetBot ¬y=z || P``tb) {i} pm)))) -- (\ y=z -> Qy (coercei1 (meetVal y=z || P``tb) {i} pm) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coercei1 (meetVal y=z || P``tb) {i} pm)))
            else (\ ¬y=z -> (absurdEq i) (coercei1 (meetBot ¬y=z || P``tb) {i} pm) )

        meetAssoc21'' : forall {x Qx} ->
            Qx [ valTB x ]/\P[ botTB ] (\()) === (\())
        meetAssoc21'' {x} {Qx} i ()

        meetAssoc21 : forall {x y z Qx Qy Qz ¬y=z} -> 
            (y == z === no ¬y=z) -> 
            Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =< (meetBot ¬y=z || (valTB x) LatS./\_) || PF >= (\())
        meetAssoc21 {Qx} {Qy} {Qz} y=z===no = refl =<P meetAssoc21' {Qx = Qx} {Qy = Qy} {Qz = Qz} y=z===no >= meetAssoc21'' 

        meetAssoc22 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {¬x=z x=y} ->
            (x == z === no ¬x=z) -> 
            (\()) =< sym (meetBot {x = x} {y = z} ¬x=z) || PF >= (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz
        meetAssoc22 {x} {y} {z} {Qx} {Qy} {Qz} {¬x=z} {x=y} x==z=no i pm =
            ifDec x==z=no (~ i)
            then (\ x=z -> (Qx (coerce (meetVal x=z || P``tb) (coerce~i0 (meetBot ¬x=z || P``tb) {~ i} pm)) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coerce (meetVal x=z || P``tb) (coerce~i0 (meetBot ¬x=z || P``tb) {~ i} pm)))) LatA./\ Qz (coerce (x=z || valTB || P``tb) (coerce (meetVal x=z || P``tb) (coerce~i0 (meetBot ¬x=z || P``tb) {~ i} pm)))) --  -- (\ x=z -> Qx (coerce (meetVal x=z || P``tb) (coerce~i0 (meetBot ¬x=z || P``tb) {~ i} pm)) LatA./\ Qz (coerce (x=z || valTB || P``tb) (coerce (meetVal x=z || P``tb) (coerce~i0 (meetBot ¬x=z || P``tb) {~ i} pm))))
            else \ ¬x=z -> (absurdEq {P = \i -> A} (~ i)) (coerce~i1 (meetBot ¬x=z || P``tb) {~ i} pm)

        meetAssoc23 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {x=y} -> 
            (x == y === yes x=y) ->
            (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz =< sym (meetVal x=y) || LatS._/\ (valTB z) || PF >= (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz
        meetAssoc23 {Qx} {Qy} {Qz} = meetAssoc4 {Qx = Qx} {Qy = Qy} {Qz = Qz}

        meetAssoc31 : forall {x y z Qx Qy Qz y=z} -> 
            (y == z === yes y=z) -> 
            Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =< (meetVal y=z || (valTB x) LatS./\_) || PF >=  Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm))
        meetAssoc31 {Qx} {Qy} {Qz} = meetAssoc1 {Qx = Qx} {Qy = Qy} {Qz = Qz}

        meetAssoc32' : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {y=z ¬x=y} -> 
            (x == y === no ¬x=y) -> 
            Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< meetBot ¬x=y || PF >= (\())
        meetAssoc32' {Qx} {Qy} {Qz} {y=z} {¬x=y} x==y=no i pm = 
            ifDec x==y=no i
            then (\  x=y -> Qx (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm)) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm))) LatA./\ Qz (coerce (y=z || valTB || P``tb) (coerce (x=y || valTB || P``tb) (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm)))))
            else (\ ¬x=y -> (absurdEq {P = \i -> A} i) (coerce~i1 (meetBot ¬x=y || P``tb) {i} pm))

        meetAssoc32'' : forall {z Qz} ->
            (\()) === (\()) [ botTB ]/\P[ valTB z ] Qz
        meetAssoc32'' i ()

        meetAssoc32 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {y=z ¬x=y} -> 
            (x == y === no ¬x=y) -> 
            Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< meetBot ¬x=y || PF >= (\()) [ botTB ]/\P[ valTB z ] Qz
        meetAssoc32 {Qx} {Qy} {Qz} x==y=no = refl =<P meetAssoc32' {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no >= meetAssoc32''

        meetAssoc33 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {¬x=y} -> 
            (x == y === no ¬x=y) ->
            (\()) [ botTB ]/\P[ valTB z ] Qz =< sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) || PF >= (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz
        meetAssoc33 {z} {Qx} {Qy} {Qz} {¬x=y} x==y=no i = 
            (\pm -> ifDec x==y=no (~ i)
                    then (\  x=y -> Qx (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {~ i} pm)) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {~ i} pm))))
                    else (\ ¬x=y -> (absurdEq {P = \i -> A} (~ i)) (coerce~i1 (meetBot ¬x=y || P``tb) {~ i} pm)) )
            [ meetBot ¬x=y (~ i) ]/\P[ valTB z ] Qz

        meetAssoc41 : forall {x y z Qx Qy Qz ¬y=z} -> 
            (y == z === no ¬y=z) -> 
            Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =< (meetBot ¬y=z || (valTB x) LatS./\_) || PF >= (\()) [ botTB ]/\P[ valTB z ] Qz
        meetAssoc41 {Qx} {Qy} {Qz} y==z=no = refl =<P meetAssoc21 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=no >= meetAssoc32''

        meetAssoc42 = meetAssoc33

        meetCommut1 : forall {x y} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {x=y} -> 
            (x == y === yes x=y) -> 
            Qx [ valTB x ]/\P[ valTB y ] Qy =< meetVal x=y || PF >= (\pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm))
        meetCommut1 {Qx} {Qy} {x=y} x==y=yes i pm =
            ifDec x==y=yes i 
            then (\  x=y -> Qx (coercei1 (meetVal x=y || P``tb) {i} pm) LatA./\ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (meetVal x=y || P``tb) {i} pm))) 
            else (\ ¬x=y -> absurd (coerce (meetBot ¬x=y || P``tb) (coercei0 (meetVal x=y || P``tb) {i} pm)))

        meetCommut2' : forall {x y} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {x=y} -> 
            (\pm -> Qy (coerce ((x=y || valTB) || P``tb) pm) LatA./\ Qx pm) =< (x=y || valTB) || PF >= (\pm -> Qy pm LatA./\ Qx (coerce ((sym x=y) || valTB || P``tb) pm))
        meetCommut2' {Qx} {Qy} {x=y} i pm = Qy (coercei1 (x=y || valTB || P``tb) {i} pm) LatA./\ Qx (coerce~i0 (x=y || valTB || P``tb) {i} pm)

        meetCommut2 : forall {x y} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {x=y} -> 
            (\pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) =< (x=y || valTB) || PF >= (\pm -> Qy pm LatA./\ Qx (coerce ((sym x=y) || valTB || P``tb) pm))
        meetCommut2 {Qx} {Qy} {x=y} = (extens \pm -> LatA.commutative-/\ {x = Qx pm} {y = Qy (coerce (x=y || valTB || P``tb) pm)}) =<P meetCommut2' >= refl

        meetCommut3 : forall {x y Qx Qy x=y} -> 
            (x == y === yes x=y) ->
            (\pm -> Qy pm LatA./\ Qx (coerce ((sym x=y) || valTB || P``tb) pm)) =< sym (meetVal (sym x=y)) || PF >= Qy [ valTB y ]/\P[ valTB x ] Qx
        meetCommut3 {Qx} {Qy} {x=y} x==y=yes i pm = 
            ifDec (decEq-sym x==y=yes) (~ i) 
            then (\ y=x -> Qy (coercei1 (meetVal y=x || P``tb) {~ i} pm) LatA./\ Qx (coerce (y=x || valTB || P``tb) (coercei1 (meetVal y=x || P``tb) {~ i} pm))) 
            else \ ¬y=x -> absurd (coerce (meetBot ¬y=x || P``tb) (coercei0 (meetVal (sym x=y) || P``tb) {~ i} pm))





        joinAssoc1 : forall {x y z Qx Qy Qz y=z} -> 
            (y == z === yes y=z) -> 
            Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =< (joinVal y=z || (valTB x) LatS.\/_) || PF >=  Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm))
        joinAssoc1 {x} {y} {z} {Qx} {Qy} {Qz} {y=z} y=z===yes i = Qx [ valTB x ]\/P[ joinVal y=z i ] \pm -> 
            ifDec y=z===yes i
            then (\ y=z -> Qy (coercei1 (joinVal y=z || P``tb) {i} pm) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coercei1 (joinVal y=z || P``tb) {i} pm)))
            else \ ¬y=z -> absurd (coerce (joinTop ¬y=z || P``tb) (coercei0 (joinVal y=z || P``tb) {i} pm))

        joinAssoc2' : {Qy : PF (valTB y)} {Qz : PF (valTB z)} -> 
            (y == z === yes y=z) -> (x == y === yes x=y) -> 
            Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< joinVal x=y || PF >= (\pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) )
        joinAssoc2' {y} {z} {y=z} {x} {x=y} {Qx} {Qy} {Qz} y==z=yes x==y=yes i pm = 
            ifDec (x==y=yes i)
            then (\ x=y -> Qx (coercei1 (joinVal x=y || P``tb) {i} pm) LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (joinVal x=y || P``tb) {i} pm)) LatA.\/ Qz (coerce (y=z || valTB || P``tb) (coerce ((x=y || valTB) || P``tb) (coercei1 (joinVal x=y || P``tb) {i} pm))) )
            else (\ ¬x=y -> absurd (coerce (joinTop ¬x=y || P``tb) (coercei0 (joinVal x=y || P``tb) {i} pm)))

        joinAssoc2 : {Qy : PF (valTB y)} {Qz : PF (valTB z)} -> 
            (y == z === yes y=z) -> (x == y === yes x=y) -> 
            Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< joinVal x=y || PF >= (\pm -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) )
        joinAssoc2 {y} {z} {y=z} {x} {x=y} {Qx} {Qy} {Qz} y==z=yes x==y=yes = refl =<P joinAssoc2' {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes x==y=yes >= extens \pm -> LatA.associative-\/

        joinAssoc3' : 
            {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} ->
            (x == y === yes x=y) ->
            (y == z === yes y=z) ->
            (x == z === yes x=z) ->
            (pm : P``tb (valTB x)) ->
            (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) === (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce (x=z || valTB || P``tb) (coerce (joinVal x=z || P``tb) (coerce (sym (joinVal x=z) || P``tb) pm)))
        joinAssoc3' {x=y} {y=z} {x=z} {Qx} {Qy} {Qz} x==y=yes y==z=yes x==z=yes pm = 
            (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) =< coerce-trans-subst (P``tb o valTB) x=y y=z || (\h -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (h pm)) >
            (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce (((trans x=y y=z) || valTB) || P``tb) pm) =< sym (encodeDec' (trans (sym' x==z=yes) (decEq-trans x==y=yes y==z=yes))) || (\h -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((h || valTB) || P``tb) pm)) >
            (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((x=z || valTB) || P``tb) pm) =< (sym (coerce-sym-subst P``tb (joinVal x=z)) || (\h -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((x=z || valTB) || P``tb) (h pm)))) >
            (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce (x=z || valTB || P``tb) (coerce (joinVal x=z || P``tb) (coerce (sym (joinVal x=z) || P``tb) pm))) qed

        joinAssoc3'' : 
            {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} -> 
            (x == z === yes x=z) -> 
            (\pm -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce (x=z || valTB || P``tb) (coerce (joinVal x=z || P``tb) (coerce (sym (joinVal x=z) || P``tb) pm))) ) =< sym (joinVal x=z) || PF >= (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz
        joinAssoc3'' {x} {y} {z} {x=z} {x=y} {Qx} {Qy} {Qz} x==z=yes i pm = 
            ifDec x==z=yes (~ i) 
            then (\  x=z -> (Qx (coercei1 (joinVal x=z || P``tb) {~ i} pm) LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (joinVal x=z || P``tb) {~ i} pm))) LatA.\/ Qz (coerce ((x=z || valTB) || P``tb) (coerce (joinVal x=z || P``tb) (coercei1 (sym (joinVal x=z) || P``tb) {i} pm)))  )
            else (\ ¬x=z -> absurd (coerce (joinTop ¬x=z || P``tb) (coercei0 (joinVal x=z || P``tb) {~ i} pm)))

        joinAssoc3 :
            {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} ->
            (x == y === yes x=y) ->
            (y == z === yes y=z) ->
            (x == z === yes x=z) ->
            (\pm -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) ) =< sym (joinVal x=z) || PF >= (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz
        joinAssoc3 {Qx} {Qy} {Qz} x==y=yes y==z=yes x==z=yes = extens (joinAssoc3' {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes y==z=yes x==z=yes) =<P joinAssoc3'' {Qx = Qx} {Qy = Qy} {Qz = Qz} x==z=yes >= refl
            
        joinAssoc4 : forall {x y z Qx Qy Qz x=y} ->
            (x == y === yes x=y) ->
            (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz =< sym (joinVal x=y) || LatS._\/ (valTB z) || PF >= (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz
        joinAssoc4 {x} {y} {z} {Qx} {Qy} {Qz} {x=y} x==y=yes i = (\pm -> 
            ifDec (x==y=yes (~ i)) 
            then (\  x=y -> Qx (coercei1 (joinVal x=y || P``tb) {~ i} pm) LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (joinVal x=y || P``tb) {~ i} pm))) 
            else (\ ¬x=y -> absurd (coerce (joinTop ¬x=y || P``tb) (coercei0 (joinVal x=y || P``tb) {~ i} pm)))) 
            [ joinVal x=y (~ i) ]\/P[ valTB z ] Qz


        joinAssoc21' : forall {x y z Qx Qy Qz ¬y=z} -> 
            (y == z === no ¬y=z) -> 
            Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =< (joinTop ¬y=z || (valTB x) LatS.\/_) || PF >=  Qx [ valTB x ]\/P[ topTB ] (\())
        joinAssoc21' {x} {y} {z} {Qx} {Qy} {Qz} {¬y=z} y=z===no i = Qx [ valTB x ]\/P[ joinTop ¬y=z i ] \pm -> 
            ifDec y=z===no i
            then (\  y=z -> Qy (coerce (joinVal y=z || P``tb) (coerce~i0 (joinTop ¬y=z || P``tb) {i} pm)) LatA.\/ Qz (coerce (y=z || valTB || P``tb) (coerce (joinVal y=z || P``tb) (coerce~i0 (joinTop ¬y=z || P``tb) {i} pm)))) -- (\ y=z -> Qy (coercei1 (joinVal y=z || P``tb) {i} pm) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coercei1 (joinVal y=z || P``tb) {i} pm)))
            else (\ ¬y=z -> (absurdEq i) (coercei1 (joinTop ¬y=z || P``tb) {i} pm) )

        joinAssoc21'' : forall {x Qx} ->
            Qx [ valTB x ]\/P[ topTB ] (\()) === (\())
        joinAssoc21'' {x} {Qx} i ()

        joinAssoc21 : forall {x y z Qx Qy Qz ¬y=z} -> 
            (y == z === no ¬y=z) -> 
            Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =< (joinTop ¬y=z || (valTB x) LatS.\/_) || PF >= (\())
        joinAssoc21 {Qx} {Qy} {Qz} y=z===no = refl =<P joinAssoc21' {Qx = Qx} {Qy = Qy} {Qz = Qz} y=z===no >= joinAssoc21'' 

        joinAssoc22 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {¬x=z x=y} ->
            (x == z === no ¬x=z) -> 
            (\()) =< sym (joinTop {x = x} {y = z} ¬x=z) || PF >= (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz
        joinAssoc22 {x} {y} {z} {Qx} {Qy} {Qz} {¬x=z} {x=y} x==z=no i pm =
            ifDec x==z=no (~ i)
            then (\ x=z -> (Qx (coerce (joinVal x=z || P``tb) (coerce~i0 (joinTop ¬x=z || P``tb) {~ i} pm)) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coerce (joinVal x=z || P``tb) (coerce~i0 (joinTop ¬x=z || P``tb) {~ i} pm)))) LatA.\/ Qz (coerce (x=z || valTB || P``tb) (coerce (joinVal x=z || P``tb) (coerce~i0 (joinTop ¬x=z || P``tb) {~ i} pm)))) --  -- (\ x=z -> Qx (coerce (joinVal x=z || P``tb) (coerce~i0 (joinTop ¬x=z || P``tb) {~ i} pm)) LatA.\/ Qz (coerce (x=z || valTB || P``tb) (coerce (joinVal x=z || P``tb) (coerce~i0 (joinTop ¬x=z || P``tb) {~ i} pm))))
            else \ ¬x=z -> (absurdEq {P = \i -> A} (~ i)) (coerce~i1 (joinTop ¬x=z || P``tb) {~ i} pm)

        joinAssoc23 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {x=y} -> 
            (x == y === yes x=y) ->
            (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz =< sym (joinVal x=y) || LatS._\/ (valTB z) || PF >= (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz
        joinAssoc23 {Qx} {Qy} {Qz} = joinAssoc4 {Qx = Qx} {Qy = Qy} {Qz = Qz}

        joinAssoc31 : forall {x y z Qx Qy Qz y=z} -> 
            (y == z === yes y=z) -> 
            Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =< (joinVal y=z || (valTB x) LatS.\/_) || PF >=  Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm))
        joinAssoc31 {Qx} {Qy} {Qz} = joinAssoc1 {Qx = Qx} {Qy = Qy} {Qz = Qz}

        joinAssoc32' : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {y=z ¬x=y} -> 
            (x == y === no ¬x=y) -> 
            Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< joinTop ¬x=y || PF >= (\())
        joinAssoc32' {Qx} {Qy} {Qz} {y=z} {¬x=y} x==y=no i pm = 
            ifDec x==y=no i
            then (\  x=y -> Qx (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm)) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm))) LatA.\/ Qz (coerce (y=z || valTB || P``tb) (coerce (x=y || valTB || P``tb) (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm)))))
            else (\ ¬x=y -> (absurdEq {P = \i -> A} i) (coerce~i1 (joinTop ¬x=y || P``tb) {i} pm))

        joinAssoc32'' : forall {z Qz} ->
            (\()) === (\()) [ topTB ]\/P[ valTB z ] Qz
        joinAssoc32'' i ()

        joinAssoc32 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {y=z ¬x=y} -> 
            (x == y === no ¬x=y) -> 
            Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm)) =< joinTop ¬x=y || PF >= (\()) [ topTB ]\/P[ valTB z ] Qz
        joinAssoc32 {Qx} {Qy} {Qz} x==y=no = refl =<P joinAssoc32' {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no >= joinAssoc32''

        joinAssoc33 : forall {x y z} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {Qz : PF (valTB z)} {¬x=y} -> 
            (x == y === no ¬x=y) ->
            (\()) [ topTB ]\/P[ valTB z ] Qz =< sym (joinTop ¬x=y) || (\h -> join h (valTB z)) || PF >= (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz
        joinAssoc33 {z} {Qx} {Qy} {Qz} {¬x=y} x==y=no i = 
            (\pm -> ifDec x==y=no (~ i)
                    then (\  x=y -> Qx (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {~ i} pm)) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {~ i} pm))))
                    else (\ ¬x=y -> (absurdEq {P = \i -> A} (~ i)) (coerce~i1 (joinTop ¬x=y || P``tb) {~ i} pm)) )
            [ joinTop ¬x=y (~ i) ]\/P[ valTB z ] Qz

        joinAssoc41 : forall {x y z Qx Qy Qz ¬y=z} -> 
            (y == z === no ¬y=z) -> 
            Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =< (joinTop ¬y=z || (valTB x) LatS.\/_) || PF >= (\()) [ topTB ]\/P[ valTB z ] Qz
        joinAssoc41 {Qx} {Qy} {Qz} y==z=no = refl =<P joinAssoc21 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=no >= joinAssoc32''

        joinAssoc42 = joinAssoc33

        joinCommut1 : forall {x y} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {x=y} -> 
            (x == y === yes x=y) -> 
            Qx [ valTB x ]\/P[ valTB y ] Qy =< joinVal x=y || PF >= (\pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm))
        joinCommut1 {Qx} {Qy} {x=y} x==y=yes i pm =
            ifDec x==y=yes i 
            then (\  x=y -> Qx (coercei1 (joinVal x=y || P``tb) {i} pm) LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) (coercei1 (joinVal x=y || P``tb) {i} pm))) 
            else (\ ¬x=y -> absurd (coerce (joinTop ¬x=y || P``tb) (coercei0 (joinVal x=y || P``tb) {i} pm)))

        joinCommut2' : forall {x y} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {x=y} -> 
            (\pm -> Qy (coerce ((x=y || valTB) || P``tb) pm) LatA.\/ Qx pm) =< (x=y || valTB) || PF >= (\pm -> Qy pm LatA.\/ Qx (coerce ((sym x=y) || valTB || P``tb) pm))
        joinCommut2' {Qx} {Qy} {x=y} i pm = Qy (coercei1 (x=y || valTB || P``tb) {i} pm) LatA.\/ Qx (coerce~i0 (x=y || valTB || P``tb) {i} pm)

        joinCommut2 : forall {x y} {Qx : PF (valTB x)} {Qy : PF (valTB y)} {x=y} -> 
            (\pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) =< (x=y || valTB) || PF >= (\pm -> Qy pm LatA.\/ Qx (coerce ((sym x=y) || valTB || P``tb) pm))
        joinCommut2 {Qx} {Qy} {x=y} = (extens \pm -> LatA.commutative-\/ {x = Qx pm} {y = Qy (coerce (x=y || valTB || P``tb) pm)}) =<P joinCommut2' >= refl

        joinCommut3 : forall {x y Qx Qy x=y} -> 
            (x == y === yes x=y) ->
            (\pm -> Qy pm LatA.\/ Qx (coerce ((sym x=y) || valTB || P``tb) pm)) =< sym (joinVal (sym x=y)) || PF >= Qy [ valTB y ]\/P[ valTB x ] Qx
        joinCommut3 {Qx} {Qy} {x=y} x==y=yes i pm = 
            ifDec (decEq-sym x==y=yes) (~ i) 
            then (\ y=x -> Qy (coercei1 (joinVal y=x || P``tb) {~ i} pm) LatA.\/ Qx (coerce (y=x || valTB || P``tb) (coercei1 (joinVal y=x || P``tb) {~ i} pm))) 
            else \ ¬y=x -> absurd (coerce (joinTop ¬y=x || P``tb) (coercei0 (joinVal (sym x=y) || P``tb) {~ i} pm))







        -- \tagcode{positionLattice}

        positionLattice : ILattice trivialLattice PF
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.e = (\())
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.rawISemilattice .RawISemilattice._<>_ {a} Qx {b} Qy = Qx [ a ]/\P[ b ] Qy
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {(topTB)} {(y)} {(z)} = refl
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {(botTB)} {(y)} {(z)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {(topTB)} {(z)} = refl
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {(botTB)} {(z)} i () 
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {valTB y} {(topTB)} with x == y 
        ... | yes x=y = refl
        ... | no  _   = \{ i ()}
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {valTB y} {(botTB)} with x == y 
        ... | yes x=y = \{ i ()}
        ... | no  _   = \{ i ()}
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {valTB y} {valTB z} {Qx} {Qy} {Qz} = 
            [ (\p -> Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =< p || PF >= (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz) , (\ x==y y==z x==z ->

                ifDec x==y
                then ifDec y==z
                    then ifDec x==z
                        then (\ x=z y=z x=y ->
                            meet (valTB x) (meet (valTB y) (valTB z)) =< meetVal y=z || meet (valTB x) > 
                            meet (valTB x) (valTB y)                  =< meetVal x=y > 
                            (valTB x)                                 =< sym (meetVal x=z) > 
                            meet (valTB x) (valTB z)                  =< sym (meetVal x=y) || (\h -> meet h (valTB z)) > 
                            meet (meet (valTB x) (valTB y)) (valTB z) qed )
                        else (\ ¬x=z y=z x=y -> absurd (¬x=z (trans x=y y=z)) )
                    else ifDec x==z
                        then (\ x=z ¬y=z x=y -> absurd (¬y=z (trans (sym x=y) x=z)))
                        else (\ ¬x=z ¬y=z x=y -> 
                            meet (valTB x) (meet (valTB y) (valTB z)) =< meetBot ¬y=z || meet (valTB x) > 
                            botTB                                     =< sym (meetBot ¬x=z) > 
                            meet (valTB x) (valTB z)                  =< sym (meetVal x=y) || (\h -> meet h (valTB z)) > 
                            meet (meet (valTB x) (valTB y)) (valTB z) qed)
                else ifDec y==z
                    then (\ y=z ¬x=y -> 
                        meet (valTB x) (meet (valTB y) (valTB z)) =< meetVal y=z || meet (valTB x) > 
                        meet (valTB x) (valTB y)                  =< meetBot ¬x=y > 
                        meet botTB (valTB z)                      =< sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) > 
                        meet (meet (valTB x) (valTB y)) (valTB z) qed)
                    else (\ ¬y=z ¬x=y -> 
                        meet (valTB x) (meet (valTB y) (valTB z)) =< meetBot ¬y=z || meet (valTB x) > 
                        meet (valTB x) botTB                      =< sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) > 
                        meet (meet (valTB x) (valTB y)) (valTB z) qed)
            )

            ]ifDecPiCase3: x == z , y == z , x == y makes:
                \{ (yes x=y) x==y=yes (yes y=z) y==z=yes (yes x=z) x==z=yes -> 
                        Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz)                                                                         =<Sig[ PF ][ meetVal y=z || meet (valTB x) ]                 meetAssoc1 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes > 
                        Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm))                                                           =<Sig[ PF ][ meetVal x=y ]                                   meetAssoc2 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes x==y=yes > 
                        (\pm -> (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA./\ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) ) =<Sig[ PF ][ sym (meetVal x=z) ]                             meetAssoc3 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes y==z=yes x==z=yes > 
                        (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz                                                          =<Sig[ PF ][ sym (meetVal x=y) || (\h -> meet h (valTB z)) ] meetAssoc4 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes >
                        (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz                                                                         qed 
                 ; (yes x=y) x==y=yes (yes y=z) y==z=yes (no ¬x=z) x==z=no  -> absurd (¬x=z (trans x=y y=z))
                 ; (yes x=y) x==y=yes (no ¬y=z) y==z=no (yes x=z) x==z=yes -> absurd (¬y=z (trans (sym x=y) x=z))
                 ; (yes x=y) x==y=yes (no ¬y=z) y==z=no (no ¬x=z) x==z=no -> 
                        Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz)                =<Sig[ PF ][ meetBot ¬y=z || meet (valTB x) ]                meetAssoc21 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=no >
                        (\())                                                                                         =<Sig[ PF ][ sym (meetBot ¬x=z) ]                            meetAssoc22 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==z=no >
                        (\ pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]/\P[ valTB z ] Qz =<Sig[ PF ][ sym (meetVal x=y) || (\h -> meet h (valTB z)) ] meetAssoc23 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes >
                        (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz                 qed
                 ; (no ¬x=y) x==y=no (yes y=z) y==z=yes r3 x==z= -> 
                        Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz)               =<Sig[ PF ][ meetVal y=z || meet (valTB x) ]                  meetAssoc31 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes > 
                        Qx [ valTB x ]/\P[ valTB y ] (\pm -> Qy pm LatA./\ Qz (coerce ((y=z || valTB) || P``tb) pm)) =<Sig[ PF ][ meetBot ¬x=y ]                                   meetAssoc32 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no > 
                        (\()) [ botTB ]/\P[ valTB z ] Qz                                                             =<Sig[ PF ][ sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) ] meetAssoc33 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no > 
                        (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz               qed
                 ; (no ¬x=y) x==y=no (no ¬y=z) y==z=no  r3 x==z= -> 
                        Qx [ valTB x ]/\P[ valTB y LatS./\ valTB z ] (Qy [ valTB y ]/\P[ valTB z ] Qz) =<Sig[ PF ][ meetBot ¬y=z || meet (valTB x) ]                 meetAssoc41 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=no > 
                        (\()) [ botTB ]/\P[ valTB z ] Qz                                               =<Sig[ PF ][ sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) ] meetAssoc42 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no > 
                        (Qx [ valTB x ]/\P[ valTB y ] Qy) [ valTB x LatS./\ valTB y ]/\P[ valTB z ] Qz qed }

        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = topTB} {y = topTB} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = topTB} {y = botTB} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = topTB} {y = valTB y} {(Qx)} {(Qy)} = refl
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = botTB} {y = topTB} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = botTB} {y = botTB} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = botTB} {y = valTB y} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = valTB x} {y = topTB} {(Qx)} {(Qy)} = refl
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = valTB x} {y = botTB} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {x = valTB x} {y = valTB y} {(Qx)} {(Qy)} = 
            [ (\p -> Qx [ valTB x ]/\P[ valTB y ] Qy =< p || PF >= Qy [ valTB y ]/\P[ valTB x ] Qx) , (\ x==y ->
            
                ifDec x==y
                then (\  x=y -> 
                    meet (valTB x) (valTB y) =< meetVal x=y > 
                    valTB x                  =< x=y || valTB > 
                    valTB y                  =< sym (meetVal (sym x=y)) >
                    meet (valTB y) (valTB x) qed)
                else \ ¬x=y -> 
                    meet (valTB x) (valTB y) =< meetBot ¬x=y > 
                    botTB                    =< sym (meetBot (¬x=y o sym)) > 
                    meet (valTB y) (valTB x) qed
            )

            ]ifDecPiCase: x == y makes:
                \{ (yes x=y) x==y=yes -> 
                          transSubst' {B = PF} {p = meetVal x=y}             {q = trans (x=y || valTB) (trans (sym (meetVal (sym x=y))) refl)} (meetCommut1 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes)  
                        ((transSubst' {B = PF} {p = x=y || valTB}            {q = trans (sym (meetVal (sym x=y))) refl}                        (meetCommut2 {x = x} {y = y} {Qx = Qx} {Qy = Qy} {x=y}) 
                        ( transSubst' {B = PF} {p = sym (meetVal (sym x=y))} {q = refl}                                                        (meetCommut3 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes) refl) ))
                        -- ^- no idea why the above is necessary...

                        -- Qx [ valTB x ]/\P[ valTB y ] Qy                                   =<Sig[ PF ][ meetVal x=y ]             meetCommut1 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes > 
                        -- (\pm -> Qx pm LatA./\ Qy (coerce (x=y || valTB || P``tb) pm))     =<Sig[ PF ][ x=y || valTB ]            meetCommut2 {x = x} {y = y} {Qx = Qx} {Qy = Qy} {x=y} > 
                        -- (\pm -> Qy pm LatA./\ Qx (coerce (sym x=y || valTB || P``tb) pm)) =<Sig[ PF ][ sym (meetVal (sym x=y)) ] meetCommut3 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes > 
                        -- Qy [ valTB y ]/\P[ valTB x ] Qx                                   qedSig[ PF ]
                ;  (no ¬x=y) x==y=no  -> 
                    Qx [ valTB x ]/\P[ valTB y ] Qy =<Sig[ PF ][ meetBot ¬x=y ] (\i pm -> ifDec x==y=no i
                                                                                            then (\ x=y -> Qx (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm)) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm)))) 
                                                                                            else \ ¬x=y -> (absurdEq i) (coercei1 (meetBot ¬x=y || P``tb) {i} pm) ) >
                    (\()) =<Sig[ PF ][ sym (meetBot (¬x=y o sym)) ] (\i pm -> ifDec decEq-sym-no x==y=no (~ i) 
                                                                                then (\ y=x -> Qy (coerce (meetVal y=x || P``tb) (coerce~i0 (meetBot (¬x=y o sym) || P``tb) {~ i} pm)) LatA./\ Qx (coerce (y=x || valTB || P``tb) (coerce (meetVal y=x || P``tb) (coerce~i0 (meetBot (¬x=y o sym) || P``tb) {~ i} pm)))) 
                                                                                else (\ ¬y=x -> (absurdEq {P = (\_ -> A)} (~ i)) (coercei1 (meetBot (¬x=y o sym) || P``tb) {~ i} pm) )) >
                    Qy [ valTB y ]/\P[ valTB x ] Qx qed }

        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.idempotent {(topTB)} {(Qx)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.idempotent {(botTB)} {(Qx)} i ()
        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.idempotent {valTB x} {(Qx)} =
            [ (\p -> Qx [ valTB x ]/\P[ valTB x ] Qx =< p || PF >= Qx) , (\ x==x ->
            
                ifDec x==x
                then (\ x=x -> meetVal x=x)
                else (\ ¬x=x -> absurd (¬x=x refl))
            )

            ]ifDecPiCase: x == x makes:
                \{ (yes x=x') x==x=yes' i pm -> 
                        ifDec' (decEq-refl {a = x} i)
                        then (\x=x x==x=yes -> 
                            (Qx (coercei1 (meetVal x=x || P``tb) {i} pm) LatA./\ Qx (coerce (x=x || valTB || P``tb) (coercei1 (meetVal x=x || P``tb) {i} pm)) =< (\c -> coerce-refl-DecEq {P = P} (coercei0 (\j -> decEq-refl j === yes x=x) {i} x==x=yes) || (_$ c)) |f (\h -> (Qx (coercei1 (meetVal x=x || P``tb) {i} pm) LatA./\ Qx (h (coercei1 (meetVal x=x || P``tb) {i} pm)))) > 
                            (Qx (coercei1 (meetVal x=x || P``tb) {i} pm) LatA./\ Qx (coercei1 (meetVal x=x || P``tb) {i} pm)) =< LatA.idempotent-/\ {x = Qx (coercei1 (meetVal x=x || P``tb) {i} pm)} > 
                            Qx (coercei1 (meetVal x=x || P``tb) {i} pm) qed) i) 
                        else (\ ¬x=x _ -> absurd (coerce (meetBot ¬x=x || P``tb) (coercei0 (meetVal x=x' || P``tb) {i} pm)))
                 ; (no ¬x=x) x==x=no i pm -> absurd {A = Qx [ valTB x ]/\P[ valTB x ] Qx =< absurd (¬x=x refl) || PF >= Qx} (¬x=x refl) i pm                 
                  }

        positionLattice .ILattice.boundedMeetISemilattice .BoundedISemilattice.identity-left = refl

        
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.e = (\())
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.rawISemilattice .RawISemilattice._<>_ {a} Qx {b} Qy = Qx [ a ]\/P[ b ] Qy
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {(topTB)} {(y)} {(z)} {(Qx)} {(Qy)} {(Qz)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {(botTB)} {(y)} {(z)} {(Qx)} {(Qy)} {(Qz)} = refl
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {(topTB)} {(z)} {(Qx)} {(Qy)} {(Qz)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {(botTB)} {(z)} {(Qx)} {(Qy)} {(Qz)} = refl
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {valTB y} {(topTB)} {(Qx)} {(Qy)} {(Qz)} with x == y
        ... | yes a = \{ i () }
        ... | no ¬a = \{ i () }
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {valTB y} {(botTB)} {(Qx)} {(Qy)} {(Qz)} with x == y 
        ... | yes a = refl
        ... | no ¬a = \{ i () }
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.associative {valTB x} {valTB y} {valTB z} {(Qx)} {(Qy)} {(Qz)} =
            [ (\p -> Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =< p || PF >= (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz) , (\ x==y y==z x==z ->

                ifDec x==y
                then ifDec y==z
                    then ifDec x==z
                        then (\ x=z y=z x=y ->
                            join (valTB x) (join (valTB y) (valTB z)) =< joinVal y=z || join (valTB x) > 
                            join (valTB x) (valTB y)                  =< joinVal x=y > 
                            (valTB x)                                 =< sym (joinVal x=z) > 
                            join (valTB x) (valTB z)                  =< sym (joinVal x=y) || (\h -> join h (valTB z)) > 
                            join (join (valTB x) (valTB y)) (valTB z) qed )
                        else (\ ¬x=z y=z x=y -> absurd (¬x=z (trans x=y y=z)) )
                    else ifDec x==z
                        then (\ x=z ¬y=z x=y -> absurd (¬y=z (trans (sym x=y) x=z)))
                        else (\ ¬x=z ¬y=z x=y -> 
                            join (valTB x) (join (valTB y) (valTB z)) =< joinTop ¬y=z || join (valTB x) > 
                            topTB                                     =< sym (joinTop ¬x=z) > 
                            join (valTB x) (valTB z)                  =< sym (joinVal x=y) || (\h -> join h (valTB z)) > 
                            join (join (valTB x) (valTB y)) (valTB z) qed)
                else ifDec y==z
                    then (\ y=z ¬x=y -> 
                        join (valTB x) (join (valTB y) (valTB z)) =< joinVal y=z || join (valTB x) > 
                        join (valTB x) (valTB y)                  =< joinTop ¬x=y > 
                        join topTB (valTB z)                      =< sym (joinTop ¬x=y) || (\h -> join h (valTB z)) > 
                        join (join (valTB x) (valTB y)) (valTB z) qed)
                    else (\ ¬y=z ¬x=y -> 
                        join (valTB x) (join (valTB y) (valTB z)) =< joinTop ¬y=z || join (valTB x) > 
                        join (valTB x) topTB                      =< sym (joinTop ¬x=y) || (\h -> join h (valTB z)) > 
                        join (join (valTB x) (valTB y)) (valTB z) qed)
            )

            ]ifDecPiCase3: x == z , y == z , x == y makes:
                \{ (yes x=y) x==y=yes (yes y=z) y==z=yes (yes x=z) x==z=yes -> 
                        Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz)                                                                         =<Sig[ PF ][ joinVal y=z || join (valTB x) ]                 joinAssoc1 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes > 
                        Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm))                                                           =<Sig[ PF ][ joinVal x=y ]                                   joinAssoc2 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes x==y=yes > 
                        (\pm -> (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) (coerce ((x=y || valTB) || P``tb) pm)) ) =<Sig[ PF ][ sym (joinVal x=z) ]                             joinAssoc3 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes y==z=yes x==z=yes > 
                        (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz                                                          =<Sig[ PF ][ sym (joinVal x=y) || (\h -> join h (valTB z)) ] joinAssoc4 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes >
                        (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz                                                                         qed 
                 ; (yes x=y) x==y=yes (yes y=z) y==z=yes (no ¬x=z) x==z=no  -> absurd (¬x=z (trans x=y y=z))
                 ; (yes x=y) x==y=yes (no ¬y=z) y==z=no (yes x=z) x==z=yes -> absurd (¬y=z (trans (sym x=y) x=z))
                 ; (yes x=y) x==y=yes (no ¬y=z) y==z=no (no ¬x=z) x==z=no -> 
                        Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz)                =<Sig[ PF ][ joinTop ¬y=z || join (valTB x) ]                joinAssoc21 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=no >
                        (\())                                                                                         =<Sig[ PF ][ sym (joinTop ¬x=z) ]                            joinAssoc22 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==z=no >
                        (\ pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) [ valTB x ]\/P[ valTB z ] Qz =<Sig[ PF ][ sym (joinVal x=y) || (\h -> join h (valTB z)) ] joinAssoc23 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=yes >
                        (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz                 qed
                 ; (no ¬x=y) x==y=no (yes y=z) y==z=yes r3 x==z= -> 
                        Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz)               =<Sig[ PF ][ joinVal y=z || join (valTB x) ]                  joinAssoc31 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=yes > 
                        Qx [ valTB x ]\/P[ valTB y ] (\pm -> Qy pm LatA.\/ Qz (coerce ((y=z || valTB) || P``tb) pm)) =<Sig[ PF ][ joinTop ¬x=y ]                                   joinAssoc32 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no > 
                        (\()) [ topTB ]\/P[ valTB z ] Qz                                                             =<Sig[ PF ][ sym (joinTop ¬x=y) || (\h -> join h (valTB z)) ] joinAssoc33 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no > 
                        (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz               qed
                 ; (no ¬x=y) x==y=no (no ¬y=z) y==z=no  r3 x==z= -> 
                        Qx [ valTB x ]\/P[ valTB y LatS.\/ valTB z ] (Qy [ valTB y ]\/P[ valTB z ] Qz) =<Sig[ PF ][ joinTop ¬y=z || join (valTB x) ]                 joinAssoc41 {Qx = Qx} {Qy = Qy} {Qz = Qz} y==z=no > 
                        (\()) [ topTB ]\/P[ valTB z ] Qz                                               =<Sig[ PF ][ sym (joinTop ¬x=y) || (\h -> join h (valTB z)) ] joinAssoc42 {Qx = Qx} {Qy = Qy} {Qz = Qz} x==y=no > 
                        (Qx [ valTB x ]\/P[ valTB y ] Qy) [ valTB x LatS.\/ valTB y ]\/P[ valTB z ] Qz qed }

        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {(topTB)} {(topTB)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {(topTB)} {(botTB)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {(topTB)} {valTB x} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {(botTB)} {(topTB)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {(botTB)} {(botTB)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {(botTB)} {valTB x} {(Qx)} {(Qy)} = refl
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {valTB x} {(topTB)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {valTB x} {(botTB)} {(Qx)} {(Qy)} = refl
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.commutative {valTB x} {valTB y} {(Qx)} {(Qy)} =
            [ (\p -> Qx [ valTB x ]\/P[ valTB y ] Qy =< p || PF >= Qy [ valTB y ]\/P[ valTB x ] Qx) , (\ x==y ->
            
                ifDec x==y
                then (\  x=y -> 
                    join (valTB x) (valTB y) =< joinVal x=y > 
                    valTB x                  =< x=y || valTB > 
                    valTB y                  =< sym (joinVal (sym x=y)) >
                    join (valTB y) (valTB x) qed)
                else \ ¬x=y -> 
                    join (valTB x) (valTB y) =< joinTop ¬x=y > 
                    topTB                    =< sym (joinTop (¬x=y o sym)) > 
                    join (valTB y) (valTB x) qed
            )

            ]ifDecPiCase: x == y makes:
                \{ (yes x=y) x==y=yes -> 
                          transSubst' {B = PF} {p = joinVal x=y}             {q = trans (x=y || valTB) (trans (sym (joinVal (sym x=y))) refl)} (joinCommut1 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes)  
                        ((transSubst' {B = PF} {p = x=y || valTB}            {q = trans (sym (joinVal (sym x=y))) refl}                        (joinCommut2 {x = x} {y = y} {Qx = Qx} {Qy = Qy} {x=y}) 
                        ( transSubst' {B = PF} {p = sym (joinVal (sym x=y))} {q = refl}                                                        (joinCommut3 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes) refl) ))
                        -- ^- no idea why the above is necessary...

                        -- Qx [ valTB x ]\/P[ valTB y ] Qy                                   =<Sig[ PF ][ joinVal x=y ]             joinCommut1 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes > 
                        -- (\pm -> Qx pm LatA.\/ Qy (coerce (x=y || valTB || P``tb) pm))     =<Sig[ PF ][ x=y || valTB ]            joinCommut2 {x = x} {y = y} {Qx = Qx} {Qy = Qy} {x=y} > 
                        -- (\pm -> Qy pm LatA.\/ Qx (coerce (sym x=y || valTB || P``tb) pm)) =<Sig[ PF ][ sym (joinVal (sym x=y)) ] joinCommut3 {x = x} {y = y} {Qx = Qx} {Qy = Qy} x==y=yes > 
                        -- Qy [ valTB y ]\/P[ valTB x ] Qx                                   qedSig[ PF ]
                ;  (no ¬x=y) x==y=no  -> 
                    Qx [ valTB x ]\/P[ valTB y ] Qy =<Sig[ PF ][ joinTop ¬x=y ] (\i pm -> ifDec x==y=no i
                                                                                            then (\ x=y -> Qx (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm)) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm)))) 
                                                                                            else \ ¬x=y -> (absurdEq i) (coercei1 (joinTop ¬x=y || P``tb) {i} pm) ) >
                    (\()) =<Sig[ PF ][ sym (joinTop (¬x=y o sym)) ] (\i pm -> ifDec decEq-sym-no x==y=no (~ i) 
                                                                                then (\ y=x -> Qy (coerce (joinVal y=x || P``tb) (coerce~i0 (joinTop (¬x=y o sym) || P``tb) {~ i} pm)) LatA.\/ Qx (coerce (y=x || valTB || P``tb) (coerce (joinVal y=x || P``tb) (coerce~i0 (joinTop (¬x=y o sym) || P``tb) {~ i} pm)))) 
                                                                                else (\ ¬y=x -> (absurdEq {P = (\_ -> A)} (~ i)) (coercei1 (joinTop (¬x=y o sym) || P``tb) {~ i} pm) )) >
                    Qy [ valTB y ]\/P[ valTB x ] Qx qed }
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.idempotent {(topTB)} {(Qx)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.idempotent {(botTB)} {(Qx)} i ()
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.isemilattice .ISemilattice.isISemilattice .IsISemilattice.idempotent {valTB x} {(Qx)} =
            [ (\p -> Qx [ valTB x ]\/P[ valTB x ] Qx =< p || PF >= Qx) , (\ x==x ->
            
                ifDec x==x
                then (\ x=x -> joinVal x=x)
                else (\ ¬x=x -> absurd (¬x=x refl))
            )

            ]ifDecPiCase: x == x makes:
                \{ (yes x=x') x==x=yes' i pm -> 
                        ifDec' (decEq-refl {a = x} i)
                        then (\x=x x==x=yes -> 
                            (Qx (coercei1 (joinVal x=x || P``tb) {i} pm) LatA.\/ Qx (coerce (x=x || valTB || P``tb) (coercei1 (joinVal x=x || P``tb) {i} pm)) =< (\c -> coerce-refl-DecEq {P = P} (coercei0 (\j -> decEq-refl j === yes x=x) {i} x==x=yes) || (_$ c)) |f (\h -> (Qx (coercei1 (joinVal x=x || P``tb) {i} pm) LatA.\/ Qx (h (coercei1 (joinVal x=x || P``tb) {i} pm)))) > 
                            (Qx (coercei1 (joinVal x=x || P``tb) {i} pm) LatA.\/ Qx (coercei1 (joinVal x=x || P``tb) {i} pm)) =< LatA.idempotent-\/ {x = Qx (coercei1 (joinVal x=x || P``tb) {i} pm)} > 
                            Qx (coercei1 (joinVal x=x || P``tb) {i} pm) qed) i) 
                        else (\ ¬x=x _ -> absurd (coerce (joinTop ¬x=x || P``tb) (coercei0 (joinVal x=x' || P``tb) {i} pm)))
                 ; (no ¬x=x) x==x=no i pm -> absurd {A = Qx [ valTB x ]\/P[ valTB x ] Qx =< absurd (¬x=x refl) || PF >= Qx} (¬x=x refl) i pm                 
                  }
                    
        positionLattice .ILattice.boundedJoinISemilattice .BoundedISemilattice.identity-left = refl
        positionLattice .ILattice.absorb-/\ {(topTB)} {(y)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.absorb-/\ {(botTB)} {(y)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.absorb-/\ {valTB x} {(topTB)} {(Qx)} {(Qy)} = refl
        positionLattice .ILattice.absorb-/\ {valTB x} {(botTB)} {(Qx)} {(Qy)} with x == x in x==x-eq
        ... | yes x=x = \i pm -> 
            (Qx (coerce refl pm) LatA./\ Qx (coerce (x=x || P) (coerce refl pm)) =< coerce-refl-DecEq {P = P} (propToPath x==x-eq) || (\h -> (Qx (coerce refl pm) LatA./\ Qx (h (coerce refl pm)))) > 
            Qx (coerce refl pm) LatA./\ Qx (coerce refl pm) =< LatA.idempotent-/\ {x = Qx (coerce refl pm)} >
            Qx (coerce refl pm) =< coerce-refl || Qx >
            Qx pm qed) i
        ... | no ¬x=x = absurd (¬x=x refl) 
        positionLattice .ILattice.absorb-/\ {valTB x} {valTB y} {(Qx)} {(Qy)} =
            [ (\p -> Qx [ valTB x ]/\P[ valTB x LatS.\/ valTB y ] (Qx [ valTB x ]\/P[ valTB y ] Qy) =< p || PF >= Qx) , (\ x==y ->
                ifDec x==y
                then (\ x=y -> 
                    meet (valTB x) (join (valTB x) (valTB y)) =< joinVal x=y || meet (valTB x) > 
                    meet (valTB x) (valTB x) =< meetVal refl >
                    valTB x qed)
                else \ ¬x=y -> 
                    meet (valTB x) (join (valTB x) (valTB y)) =< joinTop ¬x=y || meet (valTB x) > 
                    valTB x qed
            )

            ]ifDecPiCase: x == y makes:
                \{(yes x=y) x==y=yes -> 
                    Qx [ valTB x ]/\P[ valTB x LatS.\/ valTB y ] (Qx [ valTB x ]\/P[ valTB y ] Qy) =<Sig[ PF ][ joinVal x=y || meet (valTB x) ] (\i -> 
                                                                                                    Qx [ valTB x ]/\P[ joinVal x=y i ] \pm -> 
                                                                                                        ifDec (x==y=yes i) 
                                                                                                        then (\ x=y -> Qx (coercei1 (joinVal x=y || P``tb) {i} pm) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coercei1 (joinVal x=y || P``tb) {i} pm))) 
                                                                                                        else \ ¬x=y -> absurd (coerce (joinTop ¬x=y || P``tb) (coercei0 (joinVal x=y || P``tb) {i} pm))) > 
                    Qx [ valTB x ]/\P[ valTB x ] (\pm -> Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm)) =<Sig[ PF ][ meetVal refl ] (\i pm -> 
                                                                                                                    ifDec (decEq-refl {a = x} i)
                                                                                                                    then (\  x=x -> Qx (coercei1 (meetVal x=x || P``tb) {i} pm) LatA./\ (Qx (coerce (x=x || valTB || P``tb) (coercei1 (meetVal x=x || P``tb) {i} pm)) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coerce (x=x || valTB || P``tb) (coercei1 (meetVal x=x || P``tb) {i} pm))))) 
                                                                                                                    else (\ ¬x=x -> absurd (coerce (meetBot ¬x=x || P``tb) (coercei0 (meetVal refl || P``tb) {i} pm)))) > 
                    (\pm -> Qx pm LatA./\ ((Qx (coerce refl pm)) LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) (coerce refl pm)))) =< (\i pm -> Qx pm LatA./\ ((Qx (coerce-refl {x = pm} i)) LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) (coerce-refl {x = pm} i)))) >P
                    (\pm -> Qx pm LatA./\ (Qx pm LatA.\/ Qy (coerce ((x=y || valTB) || P``tb) pm))) =< (extens \_ -> LatA.absorb-/\) >P
                    Qx qed
                ; (no ¬x=y) x==y=no  -> 
                    Qx [ valTB x ]/\P[ valTB x LatS.\/ valTB y ] (Qx [ valTB x ]\/P[ valTB y ] Qy) =<Sig[ PF ][ joinTop ¬x=y || meet (valTB x) ] (\i -> Qx [ valTB x ]/\P[ joinTop ¬x=y i ] \pm -> 
                                                                                                        ifDec x==y=no i 
                                                                                                        then (\ x=y -> Qx (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm)) LatA.\/ Qy (coerce (x=y || valTB || P``tb) (coerce (joinVal x=y || P``tb) (coerce~i0 (joinTop ¬x=y || P``tb) {i} pm))))
                                                                                                        else \ ¬x=y -> absurd (coercei1 (joinTop ¬x=y || P``tb) {i} pm)) > 
                    Qx [ valTB x ]/\P[ topTB ] (\()) =<>
                    Qx qed }
        
        positionLattice .ILattice.absorb-\/ {(topTB)} {(y)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.absorb-\/ {(botTB)} {(y)} {(Qx)} {(Qy)} i ()
        positionLattice .ILattice.absorb-\/ {valTB x} {(topTB)} {(Qx)} {(Qy)} with x == x in x==x-eq
        ... | yes x=x = \i pm -> 
            (Qx (coerce refl pm) LatA.\/ Qx (coerce (x=x || P) (coerce refl pm)) =< coerce-refl-DecEq {P = P} (propToPath x==x-eq) || (\h -> (Qx (coerce refl pm) LatA.\/ Qx (h (coerce refl pm)))) > 
            Qx (coerce refl pm) LatA.\/ Qx (coerce refl pm) =< LatA.idempotent-\/ {x = Qx (coerce refl pm)} >
            Qx (coerce refl pm) =< coerce-refl || Qx >
            Qx pm qed) i
        ... | no ¬x=x = absurd (¬x=x refl)
        positionLattice .ILattice.absorb-\/ {valTB x} {(botTB)} {(Qx)} {(Qy)} = refl
        positionLattice .ILattice.absorb-\/ {valTB x} {valTB y} {(Qx)} {(Qy)} =
            [ (\p -> Qx [ valTB x ]\/P[ valTB x LatS./\ valTB y ] (Qx [ valTB x ]/\P[ valTB y ] Qy) =< p || PF >= Qx) , (\ x==y ->
                ifDec x==y
                then (\ x=y -> 
                    join (valTB x) (meet (valTB x) (valTB y)) =< meetVal x=y || join (valTB x) > 
                    join (valTB x) (valTB x) =< joinVal refl >
                    valTB x qed)
                else \ ¬x=y -> 
                    join (valTB x) (meet (valTB x) (valTB y)) =< meetBot ¬x=y || join (valTB x) > 
                    valTB x qed
            )

            ]ifDecPiCase: x == y makes:
                \{(yes x=y) x==y=yes -> 
                    Qx [ valTB x ]\/P[ valTB x LatS./\ valTB y ] (Qx [ valTB x ]/\P[ valTB y ] Qy) =<Sig[ PF ][ meetVal x=y || join (valTB x) ] (\i -> 
                                                                                                    Qx [ valTB x ]\/P[ meetVal x=y i ] \pm -> 
                                                                                                        ifDec (x==y=yes i) 
                                                                                                        then (\ x=y -> Qx (coercei1 (meetVal x=y || P``tb) {i} pm) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coercei1 (meetVal x=y || P``tb) {i} pm))) 
                                                                                                        else \ ¬x=y -> absurd (coerce (meetBot ¬x=y || P``tb) (coercei0 (meetVal x=y || P``tb) {i} pm))) > 
                    Qx [ valTB x ]\/P[ valTB x ] (\pm -> Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm)) =<Sig[ PF ][ joinVal refl ] (\i pm -> 
                                                                                                                    ifDec (decEq-refl {a = x} i)
                                                                                                                    then (\  x=x -> Qx (coercei1 (joinVal x=x || P``tb) {i} pm) LatA.\/ (Qx (coerce (x=x || valTB || P``tb) (coercei1 (joinVal x=x || P``tb) {i} pm)) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coerce (x=x || valTB || P``tb) (coercei1 (joinVal x=x || P``tb) {i} pm))))) 
                                                                                                                    else (\ ¬x=x -> absurd (coerce (joinTop ¬x=x || P``tb) (coercei0 (joinVal refl || P``tb) {i} pm)))) > 
                    (\pm -> Qx pm LatA.\/ ((Qx (coerce refl pm)) LatA./\ Qy (coerce ((x=y || valTB) || P``tb) (coerce refl pm)))) =< (\i pm -> Qx pm LatA.\/ ((Qx (coerce-refl {x = pm} i)) LatA./\ Qy (coerce ((x=y || valTB) || P``tb) (coerce-refl {x = pm} i)))) >P
                    (\pm -> Qx pm LatA.\/ (Qx pm LatA./\ Qy (coerce ((x=y || valTB) || P``tb) pm))) =< (extens \_ -> LatA.absorb-\/) >P
                    Qx qed
                ; (no ¬x=y) x==y=no  -> 
                    Qx [ valTB x ]\/P[ valTB x LatS./\ valTB y ] (Qx [ valTB x ]/\P[ valTB y ] Qy) =<Sig[ PF ][ meetBot ¬x=y || join (valTB x) ] (\i -> Qx [ valTB x ]\/P[ meetBot ¬x=y i ] \pm -> 
                                                                                                        ifDec x==y=no i 
                                                                                                        then (\ x=y -> Qx (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm)) LatA./\ Qy (coerce (x=y || valTB || P``tb) (coerce (meetVal x=y || P``tb) (coerce~i0 (meetBot ¬x=y || P``tb) {i} pm))))
                                                                                                        else \ ¬x=y -> absurd (coercei1 (meetBot ¬x=y || P``tb) {i} pm)) > 
                    Qx [ valTB x ]\/P[ botTB ] (\()) =<>
                    Qx qed }
        
    open SigmaLattices LatS LatticeProof.positionLattice

    latticedContainerLattice : Lattice ([[ latticedContainer ]] A)
    latticedContainerLattice = latticeSig