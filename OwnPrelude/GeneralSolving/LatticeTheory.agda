{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-postfix #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.LatticeTheory where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open NatOp hiding (_leq_; _^_)
open ListOp hiding (and; or)
open import OwnPrelude.Equality
open import Level.Literals


open import ASCIIPrelude.ASCIIProofPrelude 
open NatProp using (right-step-+)
open import OwnPrelude.ASCIIPreludeProofs using (module CoverSumSameLevel; encodeMaybe)
open CoverSumSameLevel

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Relation.Functions
open RepeatSyntax
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.BiThresholdVariables
open BiThresholds
open IncreaseAssignmentProperty

open ExistsSyntax

-- \tagcode{LatticeTheory}

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d f g h i j k l m n n' p q r s s' st t u v w x x' y z fm i' j' k' l' A B C D E F G H K L M N O Q R S T V W X Y Z alg Ctx  : ST


record IsOrderPreservingIncrease {S : Set i} (sl : Semilattice S) (delta : S -> S) : Set i where
    open Semilattice sl
    field
        delta-dir : forall {s} -> s P delta s
        delta-pres-P : forall {s} {s'} -> s P s' -> delta s P delta s'

record OPIFunc (S : Set i) (sl : Semilattice S) : Set i where
    field
        delta : S -> S
        isOrderPreservingIncrease : IsOrderPreservingIncrease sl delta
    open IsOrderPreservingIncrease isOrderPreservingIncrease public

module _ {S : Set i} {sl : Semilattice S} where
    open OPIFunc
    open Semilattice sl
    
    mergeOPI : OPIFunc S sl -> OPIFunc S sl -> OPIFunc S sl
    OPIFunc.delta (mergeOPI p1 p2) s = delta p1 s <> delta p2 s
    IsOrderPreservingIncrease.delta-dir (isOrderPreservingIncrease (mergeOPI p1 p2)) = mergeP' (delta-dir p1) (delta-dir p2)
    IsOrderPreservingIncrease.delta-pres-P (isOrderPreservingIncrease (mergeOPI p1 p2)) {s} {s'} sPs' = 
        ((delta p1 s <> delta p2 s) <> delta p1 s' <> delta p2 s') =< associative >
        ((delta p1 s <> delta p2 s) <> delta p1 s') <> delta p2 s' =< sym associative || _<> delta p2 s' >
        (delta p1 s <> delta p2 s <> delta p1 s') <> delta p2 s' =< commutative || (\h -> (delta p1 s <> h) <> delta p2 s') > 
        ((delta p1 s <> (delta p1 s' <> delta p2 s)) <> delta p2 s') =< associative || _<> delta p2 s' >
        ((delta p1 s <> delta p1 s') <> delta p2 s) <> delta p2 s' =< sym associative >
        (delta p1 s <> delta p1 s') <> (delta p2 s <> delta p2 s') =< (\i -> delta-pres-P p1 sPs' i <> delta-pres-P p2 sPs' i) >
        (delta p1 s' <> delta p2 s') qed

module _ {S : Set i} where


    module Branches (sl : Semilattice S) (opif : OPIFunc S sl) where
        open Semilattice sl
        open OPIFunc opif

        -- \tagcode{Branches}

        record Branch : Set i where
            field
                seminjection : SemilatticeInjection sl sl
            open SemilatticeInjection seminjection renaming (outf to unshrink ; inf to shrink ; outfoinf-id to inject-prop ; pres-inf to shrink-pres ; pres-outf to unshrink-pres) public
            field
                shrink-unshrink-revdir : shrink (unshrink s) P s -- size of unshrink itself unknown. Could be anything as arbitrary state is retrieved
                delta-similar : shrink o delta o unshrink === delta o shrink o unshrink
                --^ above might only be a property to identify branches. Might only be needed for branching operators...
                -- would be used to show correctness of branches actually creating information for the general search
                -- property could be used to show that also subbranches may communicate with parent branches. 

            delta-similar' : delta === unshrink o delta o shrink
            delta-similar' = 
                delta                                         =< sym inject-prop || delta o_ >
                delta o unshrink o shrink                     =< sym inject-prop || _o delta o unshrink o shrink >
                unshrink o shrink o delta o unshrink o shrink =< delta-similar || (\h -> unshrink o h o shrink) >
                unshrink o delta o shrink o unshrink o shrink =< inject-prop ||  (\h -> unshrink o delta o shrink o h) >
                unshrink o delta o shrink                     qed

            shrink-pres-P : s P s' -> shrink s P shrink s'
            shrink-pres-P {s} {s'} sPs' = 
                shrink s <> shrink s' =< sym shrink-pres >
                shrink (s <> s')      =< sPs' || shrink >
                shrink s'             qed

            unshrink-pres-P : s P s' -> unshrink s P unshrink s'
            unshrink-pres-P {s} {s'} sPs' = 
                unshrink s <> unshrink s' =< sym unshrink-pres >
                unshrink (s <> s')        =< sPs' || unshrink >
                unshrink s'               qed

            subdelta : S -> S
            subdelta s = s <> (shrink o delta o unshrink) s           

            subdelta-OPIFunc : IsOrderPreservingIncrease sl subdelta
            IsOrderPreservingIncrease.delta-dir subdelta-OPIFunc {s} = 
                s <> s <> shrink (delta (unshrink s))   =< associative >
                (s <> s) <> shrink (delta (unshrink s)) =< idempotent || _<> _ > 
                s <> shrink (delta (unshrink s))        qed
            IsOrderPreservingIncrease.delta-pres-P subdelta-OPIFunc {s} {s'} sPs' = 
                coerce (\i -> (s <> delta-similar (~ i) s) <> (s' <> (delta-similar (~ i) s')) === (s' <> (delta-similar (~ i) s'))) 
                (mergeP sPs' (delta-pres-P (shrink-pres-P (unshrink-pres-P sPs'))))

            -- this shows that during state transition, branches continue to be transitioned
            delta-contained : subdelta s P delta s
            delta-contained {s} =
                (s <> shrink (delta (unshrink s))) <> delta s =< (delta-similar || (_$ s)) || (\h -> (s <> h) <> delta s) >
                (s <> delta (shrink (unshrink s))) <> delta s =< commutative || _<> delta s >
                (delta (shrink (unshrink s)) <> s) <> delta s =< sym associative >
                delta (shrink (unshrink s)) <> s <> delta s   =< delta-dir {s = s} || _ <>_ >
                delta (shrink (unshrink s)) <> delta s        =< delta-pres-P (shrink-unshrink-revdir {s = s}) >
                delta s                                       qed

    module Clauses (sl : Semilattice S) where
        open Semilattice sl

        _reaches-threshold_from_at_ : OPIFunc S sl -> S -> S -> Nat -> Set i
        opi reaches-threshold st from s at 0 = st P s
        opi reaches-threshold st from s at (1+ n) = opi reaches-threshold st from (OPIFunc.delta opi s) at n

        module _ (_hasReached?_ : forall s st -> Dec (st P s)) where
            module _ where
                open OPIFunc
                clause : S -> S -> OPIFunc S sl
                delta (clause prem post) s with s hasReached? prem
                ... | yes sPprem = s <> post
                ... | no ¬sPprem = s
                IsOrderPreservingIncrease.delta-dir (isOrderPreservingIncrease (clause prem post)) {s} with s hasReached? prem
                ... | yes sPprem = directional
                ... | no ¬sPprem = idempotent
                IsOrderPreservingIncrease.delta-pres-P (isOrderPreservingIncrease (clause prem post)) {s} {s'} sPs' with s hasReached? prem | s' hasReached? prem
                ... | yes sPprem | yes s'Pprem = addP post sPs'
                ... | yes sPprem | no ¬s'Pprem = absurd (¬s'Pprem (transitive sPprem sPs'))
                ... | no ¬sPprem | yes s'Pprem = transitive sPs' directional
                ... | no ¬sPprem | no ¬s'Pprem = sPs'

            module _ {opi : OPIFunc S sl} where
                open OPIFunc opi
                
                reaches-threshold-succ : opi reaches-threshold st from (delta s) at n -> opi reaches-threshold st from s at (1+ n)
                reaches-threshold-succ {n = zero} rt = rt
                reaches-threshold-succ {n = 1+_ n} rt = reaches-threshold-succ {n = n} rt

                reaches-next-threshold : opi reaches-threshold st from s at n -> opi reaches-threshold (delta st) from s at (1+ n)
                reaches-next-threshold {n = zero} rt = delta-pres-P rt
                reaches-next-threshold {n = 1+_ n} rt = reaches-next-threshold {n = n} rt

                -- problem: while the statement is true, it does not give a tight bound. Reason: when we reach a certain threshold, 
                -- we might aquire more information on the way there speeding up the successive computation
                reaches-transitivity : forall {s s' st n n'} -> 
                    opi reaches-threshold st from s at n -> 
                    opi reaches-threshold s from s' at n' -> 
                    opi reaches-threshold st from s' at (n + n')
                reaches-transitivity {n = zero} {(zero)} rtst rts = transitive rtst rts
                reaches-transitivity {n = 1+ n} {(zero)} rtst rts = reaches-transitivity {n = n} {n' = 0} rtst (delta-pres-P rts)
                reaches-transitivity {n = zero} {(1+ n')} rtst rts = reaches-transitivity {n = 0} {n' = n'} rtst rts
                reaches-transitivity {s} {s'} {st} {n = 1+ n} {n' = 1+ n'} rtst rts = coerce (sym (right-step-+ {x = n} {y = n'}) || opi reaches-threshold st from delta s' at_) 
                    (reaches-transitivity {st = st} {n = n} {n' = n'} rtst (reaches-next-threshold {st = s} {s = delta s'} {n = n'} rts))


                reaches-higher-threshold : s P s' -> opi reaches-threshold st from s at n -> opi reaches-threshold st from s' at n
                reaches-higher-threshold {n = zero} sPs' rt = transitive rt sPs'
                reaches-higher-threshold {s} {s'} {st} {n = 1+_ n} sPs' rt = reaches-higher-threshold {n = n} (delta-pres-P sPs') rt

            module _ {opi : OPIFunc S sl} where
                open OPIFunc opi

                --TODO: small argument for how to create smaller clauses (without doing the proofs, put it to future research)

                -- \tagcode{AddClauseProp}

                -- problem with exact hit: with the learned clause, the goal might have been reaached much sooner. 
                -- therefore: just use an eventually hit and argue that if the initial bounds were tight, then transitivity could not be improved upon, but the clause learning could
                add-clause-prop : forall {s s' st n} -> 
                    opi reaches-threshold s from s' at n -> 
                    (mergeOPI opi (clause s st)) reaches-threshold st from s' at (1+ n)
                add-clause-prop {(s)} {(s')} {(st)} {(zero)} sPs' with s' hasReached? s
                ... | yes _ = 
                    st <> delta s' <> s' <> st   =< associative > 
                    (st <> delta s') <> s' <> st =< commutative || _<> (s' <> st) > 
                    (delta s' <> st) <> s' <> st =< sym associative > 
                    delta s' <> st <> s' <> st   =< associative || delta s' <>_ >
                    delta s' <> (st <> s') <> st =< commutative || (\h -> delta s' <> h <> st) >
                    delta s' <> (s' <> st) <> st =< sym associative || delta s' <>_ >
                    delta s' <> s' <> st <> st   =< idempotent || (\h -> delta s' <> s' <> h) >
                    delta s' <> s' <> st         qed
                ... | no ¬sPs' = absurd (¬sPs' sPs')
                add-clause-prop {(s)} {(s')} {(st)} {1+_ n} rtss'n with s' hasReached? s 
                ... | yes sPs' = reaches-higher-threshold {opi = mergeOPI opi (clause s st)} {n = n} ineq (add-clause-prop {st = st} {n = n} rtss'n) -- (add-clause-prop {st = st} {n = n} {n = n} rtss'n)
                    where
                        eq1 : (delta (delta s') <> delta s' <> st) <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st === delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st
                        eq1 = 
                            (delta (delta s') <> delta s' <> st) <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st     =< sym associative >
                            delta (delta s') <> (delta s' <> st) <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st     =< sym associative || delta (delta s') <>_ >
                            delta (delta s') <> delta s' <> st <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st       =< switch-op || (\h -> delta (delta s') <> delta s' <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> st <> (delta s' <> s' <> st) <> st       =< switch-op || (\h -> delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> (st <> st)     =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s' <> st) <> delta s' <> (delta s' <> s' <> st) <> (st <> st)     =< associative || (\h -> delta (delta s') <> delta (delta s' <> s' <> st) <> h) >
                            delta (delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> (delta s' <> s' <> st)) <> (st <> st)   =< associative >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> (delta s' <> s' <> st)) <> (st <> st) =< idempotent || (\h -> (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> (delta s' <> s' <> st)) <> h) >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> (delta s' <> s' <> st)) <> st         =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s' <> st)) <> h <> st) >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> s' <> st) <> st                       =< delta-pres-P directional || (\h -> h <> (delta s' <> s' <> st) <> st) >
                            delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st                                             qed

                        eq2 : (delta (delta s') <> delta s' <> st) <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) === delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)
                        eq2 = 
                            (delta (delta s') <> delta s' <> st) <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) =< sym associative >
                            delta (delta s') <> (delta s' <> st) <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) =< sym associative || delta (delta s') <>_ >
                            delta (delta s') <> delta s' <> st <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)   =< switch-op || (\h -> delta (delta s') <> delta s' <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> st <> (delta s' <> s' <> st)   =< switch-op || (\h -> delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> (delta s' <> st <> s' <> st)   =< switch-op || (\h -> delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> delta s' <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st <> st)   =< idempotent || (\h -> delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> delta s' <> s' <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)         =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> (delta s' <> s' <> st))       =< associative >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> (delta s' <> s' <> st))     =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s' <> st)) <> h) >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> s' <> st)                   =< delta-pres-P directional || (\h -> h <> (delta s' <> s' <> st)) >
                            delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)                                         qed

                        eq3 : (delta (delta s') <> delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st === delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st
                        eq3 = 
                            (delta (delta s') <> delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st   =< sym associative >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st     =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s' <> st) <> delta s' <> (delta s' <> s' <> st) <> st     =< associative || (\h -> delta (delta s') <> delta (delta s' <> s' <> st) <> h) >
                            delta (delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> (delta s' <> s' <> st)) <> st   =< associative >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> (delta s' <> s' <> st)) <> st =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s' <> st)) <> h <> st) >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> s' <> st) <> st               =< delta-pres-P directional || (\h -> h <> (delta s' <> s' <> st) <> st) >
                            delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) <> st                                     qed
                        
                        eq4 : (delta (delta s') <> delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st) === delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)
                        eq4 = 
                            (delta (delta s') <> delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)   =< sym associative >
                            delta (delta s') <> delta s' <> delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)     =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s' <> st) <> (delta s' <> (delta s' <> s' <> st))   =< associative >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> (delta s' <> s' <> st)) =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s' <> st)) <> h) >
                            (delta (delta s') <> delta (delta s' <> s' <> st)) <> (delta s' <> s' <> st)               =< delta-pres-P directional || (\h -> h <> (delta s' <> s' <> st)) >
                            delta (delta s' <> s' <> st) <> (delta s' <> s' <> st)                                     qed
                                
                        ineq : (delta (delta s') <> (OPIFunc.delta (clause s st) (delta s'))) P 
                                (delta (delta s' <> s' <> st) <> (OPIFunc.delta (clause s st) (delta s' <> s' <> st)))
                        ineq with delta s' hasReached? s | (delta s' <> s' <> st) hasReached? s
                        ... | yes sPds' | yes sPds's'st = eq1                            
                        ... | yes sPds' | no ¬sPds's'st = eq2
                        ... | no ¬sPds' | yes sPds's'st = eq3
                        ... | no ¬sPds' | no ¬sPds's'st = eq4
                                
                                     
                ... | no ¬sPs' = reaches-higher-threshold {opi = mergeOPI opi (clause s st)} {n = n} ineq (add-clause-prop {st = st} {n = n} rtss'n)
                    where
                        eq1 : (delta (delta s') <> delta s' <> st) <> delta (delta s' <> s') <> (delta s' <> s') <> st === delta (delta s' <> s') <> (delta s' <> s') <> st
                        eq1 = 
                            (delta (delta s') <> delta s' <> st) <> delta (delta s' <> s') <> (delta s' <> s') <> st     =< sym associative >
                            delta (delta s') <> (delta s' <> st) <> delta (delta s' <> s') <> (delta s' <> s') <> st     =< sym associative || delta (delta s') <>_ >
                            delta (delta s') <> delta s' <> st <> delta (delta s' <> s') <> (delta s' <> s') <> st       =< switch-op || (\h -> delta (delta s') <> delta s' <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s') <> st <> (delta s' <> s') <> st       =< switch-op || (\h -> delta (delta s') <> delta s' <> delta (delta s' <> s') <> h) >
                            delta (delta s') <> delta s' <> delta (delta s' <> s') <> (delta s' <> s') <> (st <> st)     =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s') <> delta s' <> (delta s' <> s') <> (st <> st)     =< associative || (\h -> delta (delta s') <> delta (delta s' <> s') <> h) >
                            delta (delta s') <> delta (delta s' <> s') <> (delta s' <> (delta s' <> s')) <> (st <> st)   =< associative >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> (delta s' <> s')) <> (st <> st) =< idempotent || (\h -> (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> (delta s' <> s')) <> h) >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> (delta s' <> s')) <> st         =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s')) <> h <> st) >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> s') <> st                       =< delta-pres-P directional || (\h -> h <> (delta s' <> s') <> st) >
                            delta (delta s' <> s') <> (delta s' <> s') <> st                                             qed

                        eq3 : (delta (delta s') <> delta s') <> delta (delta s' <> s') <> (delta s' <> s') <> st === delta (delta s' <> s') <> (delta s' <> s') <> st
                        eq3 = 
                            (delta (delta s') <> delta s') <> delta (delta s' <> s') <> (delta s' <> s') <> st   =< sym associative >
                            delta (delta s') <> delta s' <> delta (delta s' <> s') <> (delta s' <> s') <> st     =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s') <> delta s' <> (delta s' <> s') <> st     =< associative || (\h -> delta (delta s') <> delta (delta s' <> s') <> h) >
                            delta (delta s') <> delta (delta s' <> s') <> (delta s' <> (delta s' <> s')) <> st   =< associative >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> (delta s' <> s')) <> st =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s')) <> h <> st) >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> s') <> st               =< delta-pres-P directional || (\h -> h <> (delta s' <> s') <> st) >
                            delta (delta s' <> s') <> (delta s' <> s') <> st                                     qed

                        eq4 : (delta (delta s') <> delta s') <> delta (delta s' <> s') <> (delta s' <> s') === delta (delta s' <> s') <> (delta s' <> s')
                        eq4 = 
                            (delta (delta s') <> delta s') <> delta (delta s' <> s') <> (delta s' <> s')   =< sym associative >
                            delta (delta s') <> delta s' <> delta (delta s' <> s') <> (delta s' <> s')     =< switch-op || (\h -> delta (delta s') <> h) >
                            delta (delta s') <> delta (delta s' <> s') <> (delta s' <> (delta s' <> s'))   =< associative >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> (delta s' <> s')) =< directional || (\h -> (delta (delta s') <> delta (delta s' <> s')) <> h) >
                            (delta (delta s') <> delta (delta s' <> s')) <> (delta s' <> s')               =< delta-pres-P directional || (\h -> h <> (delta s' <> s')) >
                            delta (delta s' <> s') <> (delta s' <> s')                                     qed

                        ineq : (delta (delta s') <> (OPIFunc.delta (clause s st) (delta s'))) P 
                                (delta (delta s' <> s') <> (OPIFunc.delta (clause s st) (delta s' <> s')))
                        ineq with delta s' hasReached? s | (delta s' <> s') hasReached? s
                        ... | yes sPds' | yes sPds's' = eq1                           
                        ... | yes sPds' | no ¬sPds's' = absurd (¬sPds's' (trans associative (sPds' || _<> s'))) 
                        ... | no ¬sPds' | yes sPds's' = eq3  
                        ... | no ¬sPds' | no ¬sPds's' = eq4  
        module _ (opi : OPIFunc S sl) where
            open OPIFunc opi

            -- \tagcode{SmallerDelta}
            
            module SmallerDelta (delta-low : forall (st s : S) -> st P delta s ->  exists[ s' of S ] ((s' P s) and (st P delta s'))) where

                delta^n-pres-P : forall{n s s'} -> s P s' -> ((delta ^ n) s) P ((delta ^ n) s')
                delta^n-pres-P {n = 0}    sPs' = sPs'
                delta^n-pres-P {n = 1+ n} {s} {s'} sPs' = coerce (\i -> fof^n=f^1+n {f = delta} {n = n} i s P  fof^n=f^1+n {f = delta} {n = n} i s') 
                    (delta-pres-P {s = (delta ^ n) s} {s' = (delta ^ n) s'} (delta^n-pres-P {n = n} sPs'))

                --ideally, s' is smallest input that gives the desired output threshold
                delta-low-rec : forall {n} -> (st s : S) -> st P ((delta ^ n) s) -> exists[ s' of S ] ((s' P s) and (st P (delta ^ n) s'))
                delta-low-rec {(zero)} st s dPst = s , reflexive , dPst
                delta-low-rec {1+_ n} st s dPst = 
                    let 
                        (s' ,  s'Pds , stPdns') = delta-low-rec {n = n} st (delta s) dPst
                        (s'' , s''Ps , s'Pds'') = delta-low s' s s'Pds
                    in s''  , s''Ps , transitive stPdns' (delta^n-pres-P {n = n} s'Pds'')
            
            -- module SmallerDelta (delta-low : forall (s : S) -> exists[ s' of S ] (delta s' P s)) where
            --     --ideally, s' is smallest input that gives the desired output threshold
            --     delta-low-rec : forall {n} -> (s : S) -> exists[ s' of S ] ((delta ^ (1+ n)) s' P s)
            --     delta-low-rec {(zero)} s = delta-low s
            --     delta-low-rec {1+_ n} s = let 
            --         (s' , ds'Ps) = delta-low s -- ds'Ps : delta s' P s
            --         (s'' , d1+nPs') = delta-low-rec {n = n} s' -- 1+nPs' : (delta ^ (1+ n)) s'' P s'
            --         in s'' , coerce (fof^n=f^1+n {f = delta} {n = 1+ n} || (_$ s'') || _P s) (transitive (delta-pres-P d1+nPs') ds'Ps)
 
         