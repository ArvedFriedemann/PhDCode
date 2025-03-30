{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.TypeOfTypeTheoryInterpretation where

open import ASCIIPrelude.ASCIIPrelude 
open NatOp
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import Level.Literals
open import OwnPrelude.GeneralSolving.TypeOfTypeTheory

private
    variable
        i j k l : Level
        n n' n'' n1 n2 n3 : Nat
        -- A B C : Set i

private
        variable
            ctx ctx' Gamma Gamma' Delta Delta' : Ctx n
            A B : Tp Gamma n
            a b : Tm Gamma A
            tms tms' : Tms Gamma Delta

module _ where
    module P = PropositionalEq
    
    lmaxEq : # (max n n') P.=== (# n) ~U~ (# n') 
    lmaxEq {n = zero} {n'} = P.refl
    lmaxEq {n = 1+ n} {n' = zero}  = P.refl
    lmaxEq {n = 1+ n} {n' = 1+ n'} = P.cong lsuc (lmaxEq {n} {n'})

    liftSetMax : Set ((# n) ~U~ (# n')) -> Set (# (max n n'))
    liftSetMax {n} {n'} A with # (max n n') | (lmaxEq {n} {n'})
    ...| mnn | P.refl = A

    liftSetMaxTrm : {A : Set ((# n) ~U~ (# n'))} -> A -> liftSetMax {n = n} {n' = n'} A
    liftSetMaxTrm {n} {n'} a with # (max n n') | (lmaxEq {n} {n'})
    ...| mnn | P.refl = a

    unliftSetMaxTrm : {A : Set ((# n) ~U~ (# n'))} -> liftSetMax {n = n} {n' = n'} A -> A
    unliftSetMaxTrm {n} {n'} a with # (max n n') | (lmaxEq {n} {n'})
    ...| mnn | P.refl = a

max3 : (n1 n2 n3 : Nat) -> Nat
max3 n1 n2 n3 = max n1 (max n2 n3)

{- Does not work in the current implementation but used to work in an older one

mutual
    [_]ctx : Ctx n -> Set (# n)
    [ []ctx' ]ctx = Unit
    [ _::ctx'_ {n} {n'} ctx A ]ctx = liftSetMax {n = n} {n' = n'} (Sigma [ ctx ]ctx [ A ]tp)   

    [_]tp : Tp Gamma n -> [ Gamma ]ctx -> Set (# n)
    [ t [ tms ]TpTms' ]tp ctx = [ t ]tp ([ tms ]tms ctx)
    [ SetS' n ]tp     ctx = Set (# n)
    [ toTp' t ]tp     ctx = [ t ]tm ctx
    [ ZERO' ]tp       ctx = Zero
    [ UNIT' ]tp       ctx = Unit
    [ _:+:'_ {n} {n'} A B ]tp ctx = liftSetMax {n = n} {n' = n'} ([ A ]tp ctx -+- [ B ]tp ctx)
    [ Pi' {n} {n'} A B ]tp    ctx = liftSetMax {n = n} {n' = n'} ((a : [ A ]tp ctx) -> [ B ]tp (liftSetMaxTrm (ctx , a)))
    [ Sig' {n} {n'} A B ]tp   ctx = liftSetMax {n = n} {n' = n'} (Sigma ([ A ]tp ctx) (\a -> [ B ]tp (liftSetMaxTrm (ctx , a))))
    [ EQ' a b ]tp     ctx = [ a ]tm ctx === [ b ]tm ctx
    [ Tp-eq eq i ]tp  ctx = {!   !} -- TODO: this does not pattern match properly...needs cubical variation of indexed types

    [_]tms : Tms Gamma Delta -> [ Gamma ]ctx -> [ Delta ]ctx
    [ idtms' ]tms         ctx = ctx
    [ v1' {n} {n'} ]tms   ctx = fst (unliftSetMaxTrm {n = n} {n' = n'} ctx)
    [ apply' a ]tms       ctx = liftSetMaxTrm (ctx , [ a ]tm ctx)
    [ bc otms' ab ]tms    ctx = ([ bc ]tms o [ ab ]tms) ctx
    [ tms-eq eq i ]tms    ctx = {!  !}

    [_]tm : Tm Gamma A -> (ctx : [ Gamma ]ctx) -> [ A ]tp ctx
    [ t [ tms ]TmTms' ]tm ctx = [ t ]tm ([ tms ]tms ctx)
    [ toTm' A ]tm         ctx = [ A ]tp ctx
    [ absurdTm' t ]tm     ctx = absurd ([ t ]tm ctx)
    [ unitTm' ]tm         ctx = unit
    [ leftTm' t ]tm       ctx = liftSetMaxTrm (left  ([ t ]tm ctx))
    [ rightTm' t ]tm      ctx = liftSetMaxTrm (right ([ t ]tm ctx))
    [ lam' {n = n} {n' = n'} t ]tm ctx = liftSetMaxTrm {n = n} {n' = n'} (\a -> [ t ]tm (liftSetMaxTrm (ctx , a))) 
    [ sigma' {n = n} {n' = n'} a b ]tm ctx = liftSetMaxTrm {n = n} {n' = n'} ([ a ]tm ctx , [ b ]tm ctx) -- {n = n} {n' = n'}  (liftSetMaxTrm (ctx , [ a ]tm ctx)) 
    [ f <$$>' a ]tm       ctx = [ f ]tm (liftSetMaxTrm (ctx , [ a ]tm ctx))
    [ v0' {n} {n'} ]tm    ctx = snd (unliftSetMaxTrm {n = n} {n' = n'} ctx)
    [ Tm-eq eq i ]tm      ctx = {!   !} 

-}

    -- [ SetS' n ]tp = Set (# n)
    -- [ toTp' x ]tp = {!   !}
    -- [ ZERO' ]tp = {!   !} 
    -- [ UNIT' ]tp = {!   !}
    -- [ _=>'_ {n} {n'} A B ]tp = liftSetMax {n} {n'} ([ A ]tp -> [ B ]tp)
    -- [ t :+:' t1 ]tp = {!   !}
    -- [ Pi' t x ]tp = {!   !}
    -- [ Sig' t x ]tp = {!   !}
    -- [ EQ' a b ]tp = {!   !} 

    -- private
    --     variable
    --         -- B : Tm (A => SetS n)