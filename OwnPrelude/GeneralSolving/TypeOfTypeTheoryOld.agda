{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.TypeOfTypeTheoryOld where

open import ASCIIPrelude.ASCIIPrelude 
open NatOp
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import Level.Literals

private
    variable
        i j k l : Level
        n n' n'' n1 n2 n3 : Nat
        -- A B C : Set i

module Specification where
    record TypeTheorySpec : Setw where
        field
            Tp : (i : Level) -> Set i
            Tm : {i : Level} -> Tp i -> Set i
            [_]tp : Tp i -> Set i
            [_]tm : {A : Tp i} -> Tm A -> [ A ]tp

            SetS : (l : Level) -> Tp (lsuc l)
            toTp : Tm (SetS i) -> Tp i
            toTm : Tp i -> Tm (SetS i)

            ZERO  : Tp i
            UNIT  : Tp i 
            _=>_  : Tp i -> Tp j -> Tp (i ~U~ j)
            _:+:_ : Tp i -> Tp j -> Tp (i ~U~ j) 
            Pi  : (A : Tp i) -> Tm (A => SetS j) -> Tp (i ~U~ j)
            Sig : (A : Tp i) -> Tm (A => SetS j) -> Tp (i ~U~ j)
            EQ  : {A : Tp i} -> (a b : Tm A) -> Tp i 

            --TODO: Recursion principle. Assumption: All strictly positive functors have a fixpoint!

            absurdTm : {A : Tp i} -> Tm {i} ZERO -> Tm A

            unitTm : Tm {i} UNIT

            lam : {A : Tp i}{B : Tp j} -> (Tm A -> Tm B) -> Tm (A => B)
            app : {A : Tp i}{B : Tp j} -> Tm (A => B) -> (Tm A -> Tm B)

            leftTm  : {A : Tp i}{B : Tp j} -> Tm A -> Tm (A :+: B)
            rightTm : {A : Tp i}{B : Tp j} -> Tm B -> Tm (A :+: B)
            either  : {A : Tp i}{B : Tp j} -> Tm (A :+: B) -> Tm A -x- Tm B

        _$tm_ : {A : Tp i}{B : Tp j} -> Tm (A => B) -> Tm A -> Tm B
        f $tm a = (app f) a 

        _$tp_ : {A : Tp i} -> Tm (A => SetS j) -> Tm A -> Tp j
        B $tp a = toTp (B $tm a)

        Prod : (A : Tp i)(B : Tp j) -> Tp (i ~U~ j)
        Prod A B = Sig A (lam \_ -> toTm B) 
        
        field
            lamPi : {A : Tp i}{B : Tm (A => SetS j)} -> ((a : Tm A) -> Tm (B $tp a)) -> Tm (Pi A B)
            appPi : {A : Tp i}{B : Tm (A => SetS j)} -> Tm (Pi A B) -> ((a : Tm A) -> Tm (B $tp a))

        _$pi_ : {A : Tp i}{B : Tm (A => SetS j)} -> Tm (Pi A B) -> (a : Tm A) -> Tm (B $tp a)
        f $pi a = (appPi f) a 

        field
            tuple : {A : Tp i}{B : Tm (A => SetS j)} -> Sigma (Tm A) (Tm o B $tp_) -> Tm (Sig A B) 
            elput : {A : Tp i}{B : Tm (A => SetS j)} -> Tm (Sig A B) -> Sigma (Tm A) (Tm o B $tp_)

        _,,_ : {A : Tp i}{B : Tm (A => SetS j)} -> (a : Tm A) -> (b : Tm (B $tp a)) -> Tm (Sig A B)
        a ,, b = tuple (a , b)
        
        field
            toEq   : {A : Tp i}{a b : Tm A} -> Tm (EQ a b) -> [ a ]tm === [ b ]tm
            fromEq : {A : Tp i}{a b : Tm A} -> [ a ]tm === [ b ]tm -> Tm (EQ a b)

            coerceTm : {A B : Tm (SetS i)} -> Tm (EQ A B) -> Tm (toTp A) -> Tm (toTp B)


            []tp-Set  : [ SetS i ]tp === Set i
            toTm=toTp : toTp (toTm (SetS i)) === SetS i
            []tp-=>   : {A : Tp i} {B : Tp j} -> [ A => B ]tp === ([ A ]tp -> [ B ]tp)
            []tp-Pi   : {A : Tp i} {B : Tm (A => SetS j)} -> [ Pi  A B ]tp === ((a : [ A ]tp) -> (coerce (trans []tp-=> ([]tp-Set || Morphism _)) [ B ]tm) a)
            []tp-Sig  : {A : Tp i} {B : Tm (A => SetS j)} -> [ Sig A B ]tp === (Sigma [ A ]tp (\a -> (coerce (trans []tp-=> ([]tp-Set || Morphism _)) [ B ]tm) a))
            []to-Eq   : {A : Tp i} {a b : Tm A} -> [ EQ a b ]tp === ([ a ]tm === [ b ]tm)

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


module Interpretation where
    mutual
        data Ctx : Nat -> Set
        data Tp : Ctx n' -> Nat -> Set
        data Tm : (Gamma : Ctx n') -> Tp Gamma n -> Set
        data Tms : (Gamma : Ctx n) (Delta : Ctx n') -> Set

        private
            variable
                ctx ctx' Gamma Gamma' Delta Delta' : Ctx n
                A B : Tp Gamma n
                a b : Tm Gamma A
                tms tms' : Tms Gamma Delta

        infix 1 _=Ctx=_
        infix 1 _=Tp=_ 
        infix 1 _=Tm=_ 
        infix 1 _=Tms=_

        data _=Ctx=_ : Ctx n -> Ctx n' -> Set
        data _=Tp=_  : Tp Gamma n -> Tp Delta n' -> Set
        data _=Tm=_  : Tm Gamma A -> Tm Delta B -> Set
        data _=Tms=_ : Tms Gamma Delta -> Tms Gamma' Delta' -> Set

        data Ctx where
            []ctx' : Ctx 0
            _::ctx'_ : (Gamma : Ctx n) -> Tp Gamma n' -> Ctx (max n n')

            -- Ctx-eq : Gamma =Ctx= Delta -> Gamma === Delta -- not necessary...no additional equalities

        data Tp where
            _[_]TpTms' : Tp Gamma n -> Tms Delta Gamma -> Tp Delta n

            toTp' : Tm (Gamma) (SetS n) -> Tp Gamma n

            SetS' : (n : Nat) -> Tp Gamma (1+ n)

            ZERO'  : Tp Gamma n
            UNIT'  : Tp Gamma n 
            _:+:'_ : Tp Gamma n -> Tp Gamma n' -> Tp Gamma (max n n') -- TODO: Are these special Pi types?
            -- TODO: Base types might no longer be necessary when the naturals are used as a primitive
            Pi'  : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
            Sig' : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
            EQ'  : {A : Tp Gamma n} -> (a b : Tm Gamma A) -> Tp Gamma n 

            Tp-eq : A =Tp= B -> A === B

        data Tm where
            _[_]TmTms' : Tm Gamma A -> (tms : Tms Delta Gamma) -> Tm Delta (A [ tms ]TpTms)
            toTm' : (A : Tp Gamma n) -> Tm Gamma (SetS n)

            absurdTm' : Tm Gamma (ZERO {n = n}) -> Tm Gamma A

            unitTm' : Tm Gamma (UNIT {n = n})

            leftTm'  : Tm Gamma A -> Tm Gamma (A :+: B)
            rightTm' : Tm Gamma B -> Tm Gamma (A :+: B)

            lam' : {A : Tp Gamma n}{B : Tp (Gamma ::ctx A) n'} -> 
                Tm (Gamma ::ctx A) B -> Tm Gamma (Pi A B)

            sigma' : {A : Tp Gamma n}{B : Tp (Gamma ::ctx A) n'} -> 
                (a : Tm Gamma A) -> Tm Gamma (B [ apply a ]TpTms) -> Tm Gamma (Sig A B)

            _<$$>'_ : Tm (Gamma ::ctx A) B -> (a : Tm Gamma A) -> Tm Gamma (B [ apply a ]TpTms)
            v0' : {Gamma : Ctx n}{A : Tp Gamma n'} -> Tm (Gamma ::ctx A) (A [ v1 ]TpTms)

            Tm-eq : a =Tm= b -> a === b

        data Tms where
            idtms' : Tms Gamma Gamma
            v1' : {Gamma : Ctx n}{B : Tp Gamma n'} -> Tms (Gamma ::ctx B) Gamma
            apply' : Tm Gamma A -> Tms Gamma (Gamma ::ctx A) 
            _otms'_ : Tms Delta Gamma' -> Tms Gamma Delta -> Tms Gamma Gamma'

            tms-eq : tms =Tms= tms' -> tms === tms'

        data _=Ctx=_ where
            -- pure-Ctx-eq : Gamma === Delta -> Gamma =Ctx= Delta

            -- might not be needed
            -- []ctx-eq : []ctx =Ctx= []ctx
            -- ::ctx-eq : Gamma =Ctx= Delta -> A =Tp= B -> (Gamma ::ctx A) =Ctx= (Delta ::ctx B)
            
        data _=Tp=_   where
            -- pure-Tp-eq : A === B -> A =Tp= B

            TMS-idtsm-eq :             A [ idtms ]TpTms =Tp= A
            TMS-assoc-eq : A [ tms ]TpTms [ tms' ]TpTms =Tp= A [ tms otms tms' ]TpTms 
            toTp-o-toTm-id :              toTp (toTm A) =Tp= A
            
        data _=Tm=_   where
            -- pure-Tm-eq : a === b -> a =Tm= b
            
            tms-idtms-eq :           a [ idtms ]TmTms =Tm= a 
            tms-assoc-eq : a [ tms ]TmTms [ tms' ]TmTms =Tm= a [ tms otms tms' ]TmTms
            v0-apply-eq  :        v0 [ apply a ]TmTms =Tm= a
            toTm-o-toTp-id :          toTm (toTp a) =Tm= a
            
        data _=Tms=_  where
            -- pure-Tms-eq : tms === tms' -> tms =Tms= tms'
            
            v1-o-apply-id : v1 otms (apply a) =Tms= idtms {Gamma = Gamma}
            id-left-id    :   idtms otms tms  =Tms= tms
            id-right-id   :   tms otms idtms  =Tms= tms
        

        []ctx : Ctx 0
        []ctx = []ctx' 
        _::ctx_ : (Gamma : Ctx n) -> Tp Gamma n' -> Ctx (max n n')    
        _::ctx_ = _::ctx'_ 

        idtms : Tms Gamma Gamma
        idtms = idtms'
        v1 : Tms (Gamma ::ctx B) Gamma
        v1 = v1' 
        apply : Tm Gamma A -> Tms Gamma (Gamma ::ctx A) 
        apply = apply'
        _otms_ : Tms Delta Gamma' -> Tms Gamma Delta -> Tms Gamma Gamma'
        _otms_ = _otms'_

        _[_]TpTms : Tp Gamma n -> Tms Delta Gamma -> Tp Delta n
        _[_]TpTms = _[_]TpTms'

        SetS : (n : Nat) -> Tp Gamma (1+ n)
        SetS = SetS' 
        toTp : Tm Gamma (SetS n) -> Tp Gamma n
        toTp = toTp' 

        ZERO  : Tp Gamma n
        ZERO  = ZERO'  
        UNIT  : Tp Gamma n 
        UNIT  = UNIT'  
        _:+:_ : Tp Gamma n -> Tp Gamma n' -> Tp Gamma (max n n')
        _:+:_ = _:+:'_ 
        Pi  : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
        Pi  = Pi'  
        Sig : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
        Sig = Sig' 
        EQ  : {A : Tp Gamma n} -> (a b : Tm Gamma A) -> Tp Gamma n 
        EQ  = EQ'  

        _[_]TmTms : Tm Gamma A -> (tms : Tms Delta Gamma) -> Tm Delta (A [ tms ]TpTms)
        _[_]TmTms = _[_]TmTms'

        toTm : (A : Tp Gamma n) -> Tm Gamma (SetS n)
        toTm = toTm' 

        absurdTm : Tm Gamma (ZERO {n = n}) -> Tm Gamma A
        absurdTm = absurdTm' 

        unitTm : Tm Gamma (UNIT {n = n})
        unitTm = unitTm' 

        leftTm  : Tm Gamma A -> Tm Gamma (A :+: B)
        leftTm  = leftTm'  
        rightTm : Tm Gamma B -> Tm Gamma (A :+: B)
        rightTm = rightTm' 

        lam : Tm (Gamma ::ctx A) B -> Tm Gamma (Pi A B)
        lam = lam' 

        sigma : (a : Tm Gamma A) -> Tm Gamma (B [ apply a ]TpTms) -> Tm Gamma (Sig A B)
        sigma = sigma' 

        _<$$>_ : Tm (Gamma ::ctx A) B -> (a : Tm Gamma A) -> Tm Gamma (B [ apply a ]TpTms)
        _<$$>_ = _<$$>'_ 
        v0 : Tm (Gamma ::ctx A) (A [ v1 ]TpTms)
        v0 = v0' 

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