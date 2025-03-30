{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.TypeOfTypeTheory where

open import ASCIIPrelude.ASCIIPrelude 
open import ASCIIPrelude.ASCIIProofPrelude 
open NatProp
open NatOp
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import Level.Literals

private
    variable
        ST : Set _
        a a' b b' c c' d e f g h i j k l m n n' n'' p p1 p2 p3 p' q r s s' s1 s2 s3 t u v w x y z fm i' j' k' l' A B C D E F G H I K L M N O P Q R S T U V X Y Z A=B B=C : ST

-- \tagcode{TypeOfTypeTheory}

mutual
    data Ctx : Nat -> Set
    data Tp : Ctx n' -> Nat -> Set
    data Tm : (Gamma : Ctx n') -> Tp Gamma n -> Set
    data Tms : (Gamma : Ctx n) (Delta : Ctx n') -> Set

    private
        variable
            ctx ctx' Gamma Gamma' Gamma1 Gamma2 Delta Delta' Delta1 Delta2 : Ctx n
            -- A B : Tp Gamma n
            -- a b : Tm Gamma A
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
        _[_]TpTms' : Tp Delta n -> Tms Gamma Delta -> Tp Gamma n

        toTp' : Tm (Gamma) (SetS n) -> Tp Gamma n

        SetS' : (n : Nat) -> Tp Gamma (1+ n)

        ZERO' : Tp Gamma n
        UNIT' : Tp Gamma n 
        BOOL' : Tp Gamma n -- needed to use Pi types for non-dependent products and Sigma types for nondependent sums
    
        Pi'  : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
        Sig' : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
        EQ'  : {A B : Tp Gamma n} -> (a : Tm Gamma A) -> (b : Tm Gamma B) -> Tp Gamma n

        W' : Tm Gamma (ContainerTp n n') -> Tp Gamma (max (1+ n) (max n (1+ n')))

        -- TODO: container fixpoints (A container itself is just a Sigma-type Sigma Set (\A -> (A -> Set)))

        coerce-Tp' : Gamma =Ctx= Delta -> Tp Gamma n -> Tp Delta n

        -- Tp-eq : A =Tp= B -> A === B

    data Tm where
        _[_]TmTms' : Tm Delta A -> (tms : Tms Gamma Delta) -> Tm Gamma (A [ tms ]TpTms)
        toTm' : (A : Tp Gamma n) -> Tm Gamma (SetS n)

        -- constructors:

        unitTm' : Tm Gamma (UNIT {n = n})

        trueTm'  : Tm Gamma (BOOL {n = n})
        falseTm' : Tm Gamma (BOOL {n = n})

        lam' : Tm (Gamma ::ctx A) B -> Tm Gamma (Pi A B)

        sigma' : (a : Tm Gamma A) -> Tm Gamma (B $Tp a) -> Tm Gamma (Sig A B)

        eqC' : {A B : Tp Gamma n} {a : Tm Gamma A} {b : Tm Gamma B} -> a =Tm= b -> Tm Gamma (EQ a b)

        In' : {C : Tm Gamma (ContainerTp n n')} -> Tm Gamma ([[ C ]] (W C)) -> Tm Gamma (W C)

        -- destructors:

        absurdTm' : Tm Gamma (ZERO {n = n}) -> Tm Gamma A

        ifTm'_then_else_ : Tm Gamma (BOOL {n = n}) -> Tm Gamma A -> Tm Gamma A -> Tm Gamma A
        
        app' : Tm Gamma (Pi A B) -> Tm (Gamma ::ctx A) B

        fstTm' : Tm Gamma (Sig A B) -> Tm Gamma A
        sndTm' : (a : Tm Gamma (Sig A B)) -> Tm Gamma (B $Tp (fstTm a)) 

        foldC' : {A : Tp Gamma n''}{C : Tm Gamma (ContainerTp n n')} -> Tm (Gamma ::ctx [[ C ]] A) (A [ v1 ]TpTms) -> Tm (Gamma ::ctx W C) (A [ v1 ]TpTms)

        -- misc:

        v0' : Tm (Gamma ::ctx A) (A [ v1 ]TpTms)

        coerce-Tm' : A =Tp= B -> Tm Gamma A -> Tm Delta B

        -- Tm-eq : a =Tm= b -> a === b

    data Tms where
        idtms' : Tms Gamma Gamma
        v1' : Tms (Gamma ::ctx B) Gamma
        
        _addTm'_ : (tms : Tms Gamma Delta) -> Tm Gamma (A [ tms ]TpTms) -> Tms Gamma (Delta ::ctx A) 

        _otms'_ : Tms Delta Gamma' -> Tms Gamma Delta -> Tms Gamma Gamma'

        coerce-Tms : Gamma1 =Ctx= Gamma2 -> Delta1 =Ctx= Delta2 -> Tms Gamma1 Delta1 -> Tms Gamma2 Delta2

        -- Tms-eq : tms =Tms= tms' -> tms === tms'

    data _=Ctx=_ where
        -- pure-Ctx-eq : Gamma === Delta -> Gamma =Ctx= Delta

        refl-Ctx  : A =Ctx= A
        sym-Ctx   : A =Ctx= B -> B =Ctx= A
        trans-Ctx : A =Ctx= B -> B =Ctx= C -> A =Ctx= C

        -- TODO: this should be a consequence, not an axiom
        ctx-Eq : A =Tp= B -> Gamma =Ctx= Delta

        []ctx-eq : []ctx =Ctx= []ctx
        ::ctx-eq : Gamma =Ctx= Delta -> A =Tp= B -> (Gamma ::ctx A) =Ctx= (Delta ::ctx B)
        
    data _=Tp=_   where
        -- pure-Tp-eq : A === B -> A =Tp= B

        refl-Tp  : A =Tp= A
        sym-Tp   : A =Tp= B -> B =Tp= A
        trans-Tp : A =Tp= B -> B =Tp= C -> A =Tp= C

        coerce-Tp-coh : coerce-Tp A=B A =Tp= A
        coerce-Tp-cong : A =Tp= C -> coerce-Tp A=B A =Tp= coerce-Tp A=B C

        toTp-cong : A =Tm= B -> toTp A =Tp= toTp B
        tms-cong-Tp  : A =Tp= B -> tms =Tms= tms' -> A [ tms ]TpTms =Tp= B [ tms' ]TpTms

        Pi-cong  : (A=Tp=B : A =Tp= B) -> (C=Tp=D : C =Tp= D) -> Pi  A C =Tp= Pi  B D
        Sig-cong : (A=Tp=B : A =Tp= B) -> (C=Tp=D : C =Tp= D) -> Sig A C =Tp= Sig B D

        tms-idtms-Tp :             A [ idtms ]TpTms =Tp= A 
        tms-assoc-Tp : A [ tms ]TpTms [ tms' ]TpTms =Tp= A [ tms otms tms' ]TpTms 

        toTp-o-toTm-id :              toTp (toTm A) =Tp= A

        tms-SetS : {tms : Tms Gamma Delta} -> SetS {Gamma = Delta} n [ tms ]TpTms  =Tp= SetS {Gamma = Gamma} n
        tms-ZERO : {tms : Tms Gamma Delta} -> ZERO {Gamma = Delta} {n = n} [ tms ]TpTms  =Tp= ZERO {Gamma = Gamma} {n = n}
        tms-UNIT : {tms : Tms Gamma Delta} -> UNIT {Gamma = Delta} {n = n} [ tms ]TpTms  =Tp= UNIT {Gamma = Gamma} {n = n}
        tms-BOOL : {tms : Tms Gamma Delta} -> BOOL {Gamma = Delta} {n = n} [ tms ]TpTms  =Tp= BOOL {Gamma = Gamma} {n = n}

        tms-Pi  : Pi A B  [ tms ]TpTms =Tp= Pi  (A [ tms ]TpTms) (B [ tms transformTp A ]TpTms)
        tms-Sig : Sig A B [ tms ]TpTms =Tp= Sig (A [ tms ]TpTms) (B [ tms transformTp A ]TpTms)
        tms-Eq  : EQ a b [ tms ]TpTms =Tp= EQ (a [ tms ]TmTms) (b [ tms ]TmTms)

        toTp-tms : (toTp a) [ tms ]TpTms =Tp= toTp (coerce-Tm tms-SetS (a [ tms ]TmTms))
        
    infix 3 _qedTp
    _qedTp : (A : Tp Gamma n) -> A =Tp= A
    _qedTp A = refl-Tp

    infixr 2 trans-tp-step
    trans-tp-step : forall (A : Tp Gamma n) -> B =Tp= C -> A =Tp= B -> A =Tp= C
    trans-tp-step _ B=C A=B = trans-Tp A=B B=C

    infixr 2 trans-tp-step'
    trans-tp-step' : forall (A : Tp Gamma n) -> A =Tp= B -> A =Tp= B
    trans-tp-step' _ A=B = A=B

    syntax trans-tp-step A B=C A=B = A =<Tp A=B > B=C
    syntax trans-tp-step' A A=B = A =<Tp> A=B

    data _=Tm=_   where
        -- pure-Tm-eq : a === b -> a =Tm= b

        refl-Tm  : A =Tm= A
        sym-Tm   : A =Tm= B -> B =Tm= A
        trans-Tm : A =Tm= B -> B =Tm= C -> A =Tm= C
        
        coerce-Tm-coh : coerce-Tm A=B A =Tm= A
        coerce-Tm-cong : a =Tm= c -> coerce-Tm A=B a =Tm= coerce-Tm A=B c
        tms-cong-Tm : a =Tm= b -> tms =Tms= tms' -> a [ tms ]TmTms =Tm= b [ tms' ]TmTms
        ite-cong : b =Tm= b' -> a =Tm= a' -> c =Tm= c' -> (ifTm b then a else c) =Tm= (ifTm b' then a' else c')
        toTm-cong : A =Tp= B -> toTm A =Tm= toTm B 

        tms-idtms-Tm     :             a [ idtms ]TmTms =Tm= a 
        tms-assoc-Tm     : a [ tms ]TmTms [ tms' ]TmTms =Tm= a [ tms otms tms' ]TmTms
        tms-v0-addTm-Tm  :      v0 [ tms addTm a ]TmTms =Tm= a
        tms-ite          : (ifTm b then a else c) [ tms ]TmTms =Tm= ifTm (coerce-Tm tms-BOOL (b [ tms ]TmTms)) then (a [ tms ]TmTms) else (c [ tms ]TmTms)
        tms-sigma        : -- {A : Tp Gamma n}{B : Tp (Gamma ::ctx A) n'}{a : Tm Gamma A} {b : Tm Gamma (B $Tp a)}{tms : Tms Delta Gamma} -> 
            (sigma a b) [ tms ]TmTms =Tm= sigma (a [ tms ]TmTms) (coerce-Tm tms-apply-Tp (b [ tms ]TmTms))

        ite-true  : ifTm trueTm  {n = n} then a else b =Tm= a
        ite-false : ifTm falseTm {n = n} then a else b =Tm= b

        fstTm-sigma : fstTm (sigma a b) =Tm= a
        sndTm-sigma : sndTm (sigma a b) =Tm= b

        foldC-In : {C : Tm Gamma (ContainerTp n n')} {CW : Tm Gamma ([[ C ]] (W C))}{alg : Tm (Gamma ::ctx [[ C ]] A) (A [ v1 ]TpTms)}  -> 
            (foldC alg [ apply (In CW) ]TmTms) =Tm= mapC (foldC alg) CW

        toTm-tms : (toTm A) [ tms ]TmTms =Tm= toTm (A [ tms ]TpTms)

        toTm-o-toTp-id :          toTm (toTp a) =Tm= a

        beta : app (lam t) =Tm= t
        eta  : lam (app t) =Tm= t 
    
    infix 3 _qedTm
    _qedTm : (A : Tm Gamma n) -> A =Tm= A
    _qedTm A = refl-Tm

    infixr 2 trans-tm-step
    trans-tm-step : forall (a : Tm Gamma A) -> b =Tm= c -> a =Tm= b -> a =Tm= c
    trans-tm-step _ b=c a=b = trans-Tm a=b b=c

    infixr 2 trans-tm-step'
    trans-tm-step' : forall (a : Tm Gamma A) -> a =Tm= b -> a =Tm= b
    trans-tm-step' _ a=b = a=b

    syntax trans-tm-step A B=C A=B = A =<Tm A=B > B=C
    syntax trans-tm-step' A A=B = A =<Tm> A=B

    data _=Tms=_  where
        -- pure-Tms-eq : tms === tms' -> tms =Tms= tms'

        refl-Tms  : A =Tms= A
        sym-Tms   : A =Tms= B -> B =Tms= A
        trans-Tms : A =Tms= B -> B =Tms= C -> A =Tms= C

        coerce-Tms-coh : coerce-Tms A B tms =Tms= tms

        otms-cong : forall {Gamma Gamma' : Ctx n} {Delta Delta' : Ctx n'} {B B' : Ctx n''}{tms1 : Tms Delta Gamma} {tms1' : Tms Delta' Gamma'} {tms2 : Tms B Delta} {tms2' : Tms B' Delta'} ->
            tms1 =Tms= tms1' -> tms2 =Tms= tms2' -> tms1 otms tms2 =Tms= tms1' otms tms2'
        addTm-cong : tms =Tms= tms' -> a =Tm= b -> (tms addTm a) =Tms= (tms' addTm b)
        
        otms-assoc : (a otms b) otms c =Tms= a otms (b otms c)

        idtms-left-id    :   idtms otms tms  =Tms= tms
        idtms-right-id   :   tms otms idtms  =Tms= tms
        v1-addTm-id :           (v1 {B = B}) addTm v0 =Tms= idtms {Gamma = Gamma ::ctx B}
        v1-otms     : (v1 {B = B}) otms (tms addTm a) =Tms= tms
        otms-addTm  :         (tms addTm a) otms tms' =Tms= ((tms otms tms') addTm (coerce-Tm tms-assoc-Tp (a [ tms' ]TmTms)))

    infix 3 _qedTms
    _qedTms : (A : Tms Gamma n) -> A =Tms= A
    _qedTms A = refl-Tms

    infixr 2 trans-tms-step
    trans-tms-step : forall (a : Tms Gamma A) -> b =Tms= c -> a =Tms= b -> a =Tms= c
    trans-tms-step _ b=c a=b = trans-Tms a=b b=c

    infixr 2 trans-tms-step'
    trans-tms-step' : forall (a : Tms Gamma A) -> a =Tms= b -> a =Tms= b
    trans-tms-step' _ a=b = a=b

    syntax trans-tms-step A B=C A=B = A =<Tms A=B > B=C
    syntax trans-tms-step' A A=B = A =<Tms> A=B

    -- ctx-Eq : {A : Tp Gamma n} {B : Tp Delta n'} -> A =Tp= B -> Gamma =Ctx= Delta
    -- ctx-Eq A=Tp=B = {! A=Tp=B !}

    []ctx : Ctx 0
    []ctx = []ctx' 

    infixl 10 _::ctx_
    _::ctx_ : (Gamma : Ctx n) -> Tp Gamma n' -> Ctx (max n n')    
    _::ctx_ = _::ctx'_ 

    ctx-Tp-eq : A =Tp= B -> (Gamma ::ctx A) =Ctx= (Delta ::ctx B)
    ctx-Tp-eq A=Tp=B = ::ctx-eq (ctx-Eq A=Tp=B) A=Tp=B

    idtms : Tms Gamma Gamma
    idtms = idtms'
    v1 : Tms (Gamma ::ctx B) Gamma
    v1 = v1' 

    infixr 9 _otms_
    _otms_ : Tms Delta Gamma' -> Tms Gamma Delta -> Tms Gamma Gamma'
    _otms_ = _otms'_

    _[_]TpTms : Tp Gamma n -> Tms Delta Gamma -> Tp Delta n
    _[_]TpTms = _[_]TpTms'

    _addTm_ : (tms : Tms Gamma Delta) -> Tm Gamma (A [ tms ]TpTms) -> Tms Gamma (Delta ::ctx A) 
    _addTm_ = _addTm'_

    apply : Tm Gamma A -> Tms Gamma (Gamma ::ctx A) 
    apply a = idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) a

    SetS : (n : Nat) -> Tp Gamma (1+ n)
    SetS = SetS' 

    toTp : Tm Gamma (SetS n) -> Tp Gamma n
    toTp = toTp' 

    coerce-Tp : Gamma =Ctx= Delta -> Tp Gamma n -> Tp Delta n
    coerce-Tp = coerce-Tp'

    coerce-Tm : A =Tp= B -> Tm Gamma A -> Tm Delta B
    coerce-Tm = coerce-Tm'

    toTpTms : Tm Gamma (SetS n [ tms ]TpTms) -> Tp Gamma n
    toTpTms = toTp o coerce-Tm tms-SetS

    toTpTms2 : Tm Gamma ((SetS n [ tms ]TpTms) [ tms' ]TpTms) -> Tp Gamma n
    toTpTms2 = toTpTms o coerce-Tm tms-assoc-Tp

    ZERO  : Tp Gamma n
    ZERO  = ZERO'  
    UNIT  : Tp Gamma n 
    UNIT  = UNIT'  
    BOOL  : Tp Gamma n 
    BOOL  = BOOL'  

    Pi  : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
    Pi  = Pi'  
    Sig : (A : Tp Gamma n) -> Tp (Gamma ::ctx A) n' -> Tp Gamma (max n n')
    Sig = Sig' 
    EQ  : {A B : Tp Gamma n} -> (a : Tm Gamma A) -> (b : Tm Gamma B) -> Tp Gamma n 
    EQ  = EQ'  

    infixr 10 _=>_
    _=>_ : Tp Gamma n -> Tp Gamma n' -> Tp Gamma (max n n')
    A => B = Pi A (B [ v1 ]TpTms)

    _[_]TmTms : Tm Gamma A -> (tms : Tms Delta Gamma) -> Tm Delta (A [ tms ]TpTms)
    _[_]TmTms = _[_]TmTms'

    toTm : (A : Tp Gamma n) -> Tm Gamma (SetS n)
    toTm = toTm' 

    absurdTm : Tm Gamma (ZERO {n = n}) -> Tm Gamma A
    absurdTm = absurdTm' 

    unitTm : Tm Gamma (UNIT {n = n})
    unitTm = unitTm' 

    trueTm  : Tm Gamma (BOOL {n = n})
    trueTm  = trueTm'  
    falseTm : Tm Gamma (BOOL {n = n})
    falseTm = falseTm' 

    lam : Tm (Gamma ::ctx A) B -> Tm Gamma (Pi A B)
    lam = lam' 

    app : {A : Tp Gamma n}{B : Tp (Gamma ::ctx A) n'} -> 
            Tm Gamma (Pi A B) -> Tm (Gamma ::ctx A) B
    app = app'
    
    _$Tp_ : Tp (Gamma ::ctx A) n -> Tm Gamma A -> Tp Gamma n
    _$Tp_ {n} B a = B [ apply a ]TpTms
    
    apply-irr-Tp : (A [ v1 ]TpTms) $Tp a =Tp= A
    apply-irr-Tp {A} {a} =
        (A [ v1 ]TpTms) $Tp a =<Tp tms-assoc-Tp >
        A [ v1 otms apply a ]TpTms =<Tp tms-cong-Tp refl-Tp v1-otms >
        A [ idtms ]TpTms =<Tp tms-idtms-Tp >
        A qedTp

    _$Tm_ : Tm Gamma (Pi A B) -> (a : Tm Gamma A) -> Tm Gamma (B $Tp a)
    _$Tm_ f a = app f [ apply a ]TmTms

    _$Tm'_ : Tm Gamma (A => B) -> (a : Tm Gamma A) -> Tm Gamma B
    _$Tm'_ f a = coerce-Tm apply-irr-Tp (f $Tm a)

    sigma : (a : Tm Gamma A) -> Tm Gamma (B $Tp a) -> Tm Gamma (Sig A B)
    sigma = sigma' 

    ifTm_then_else_ : Tm Gamma (BOOL {n = n}) -> Tm Gamma A -> Tm Gamma A -> Tm Gamma A
    ifTm_then_else_ = ifTm'_then_else_

    fstTm : Tm Gamma (Sig A B) -> Tm Gamma A
    fstTm = fstTm'
    
    sndTm : (a : Tm Gamma (Sig A B)) -> Tm Gamma (B $Tp (fstTm a))
    sndTm = sndTm'

    _:x:_ : Tp Gamma n -> Tp Gamma n' -> Tp Gamma (max n n')
    _:x:_ A B = Sig A (B [ v1 ]TpTms)

    mkTup : Tm Gamma A -> Tm Gamma B -> Tm Gamma (A :x: B)
    mkTup a b = sigma a (coerce-Tm (sym-Tp apply-irr-Tp) b)

    fstTup : Tm Gamma (A :x: B) -> Tm Gamma A
    fstTup axb = fstTm axb

    sndTup : Tm Gamma (A :x: B) -> Tm Gamma B
    sndTup {B} axb = coerce-Tm apply-irr-Tp (sndTm axb)

    liftTpL : (n : Nat) -> Tp Gamma n' -> Tp Gamma (max n n')
    liftTpL n A = UNIT {n = n} :x: A

    liftTpR : (n : Nat) -> Tp Gamma n' -> Tp Gamma (max n' n)
    liftTpR {Gamma} {n'} n A = A :x: UNIT {n = n}

    _:+:_ : Tp Gamma n -> Tp Gamma n' -> Tp Gamma (max n n')
    _:+:_ {Gamma} {n} {n'} A B = (Sig (BOOL {n = 0}) (toTp (ifTm (coerce-Tm (tms-BOOL {n = 0}) v0) 
                                                            then toTm (liftTpR n' (A [ v1 ]TpTms)) 
                                                            else toTm (liftTpL n (B [ v1 ]TpTms)))))

    SetS-Ctx-Eq : Gamma =Ctx= Delta -> SetS {Gamma = Gamma} n =Tp= SetS {Gamma = Delta} n
    SetS-Ctx-Eq {Gamma} {Delta} {n} eq =
        SetS {Gamma = Gamma} n =<Tp sym-Tp tms-SetS >
        SetS {Gamma = Gamma} n [ idtms ]TpTms =<Tp tms-cong-Tp refl-Tp (sym-Tms coerce-Tms-coh) >
        SetS {Gamma = Gamma} n [ coerce-Tms eq refl-Ctx idtms ]TpTms =<Tp tms-SetS >
        SetS {Gamma = Delta} n qedTp

    UNIT-Ctx-Eq : Gamma =Ctx= Delta -> UNIT {Gamma = Gamma} {n = n} =Tp= UNIT {Gamma = Delta} {n = n}
    UNIT-Ctx-Eq {Gamma} {Delta} {n} eq =
        UNIT {Gamma = Gamma} {n = n} =<Tp sym-Tp tms-UNIT >
        UNIT {Gamma = Gamma} {n = n} [ idtms ]TpTms =<Tp tms-cong-Tp refl-Tp (sym-Tms coerce-Tms-coh) >
        UNIT {Gamma = Gamma} {n = n} [ coerce-Tms eq refl-Ctx idtms ]TpTms =<Tp tms-UNIT >
        UNIT {Gamma = Delta} {n = n} qedTp

    leftTm : {A : Tp Gamma n} {B : Tp Gamma n'} -> 
        Tm Gamma A -> Tm Gamma (A :+: B)
    leftTm {n} {n'} {A} {B} a = sigma trueTm (coerce-Tm (sym-Tp eq) (mkTup a unitTm))
        where
            eq : toTp (ifTm coerce-Tm tms-BOOL v0 
                        then toTm (liftTpR n' (A [ v1 ]TpTms)) 
                        else toTm (liftTpL n (B [ v1 ]TpTms))) 
                        $Tp trueTm 
                    =Tp= A :x: (UNIT {n = n'})
            eq = 
                toTp (ifTm coerce-Tm tms-BOOL v0 
                        then toTm (liftTpR n' (A [ v1 ]TpTms)) 
                        else toTm (liftTpL n (B [ v1 ]TpTms))) 
                        $Tp trueTm =<Tp toTp-tms >
                        
                toTp (coerce-Tm tms-SetS ((
                    ifTm coerce-Tm tms-BOOL v0 
                    then toTm (liftTpR n' (A [ v1 ]TpTms)) 
                    else toTm (liftTpL n (B [ v1 ]TpTms))) 
                    [ apply trueTm ]TmTms)) =<Tp toTp-cong (
                        coerce-Tm tms-SetS ((
                            ifTm coerce-Tm tms-BOOL v0 
                            then toTm (liftTpR n' (A [ v1 ]TpTms)) 
                            else toTm (liftTpL n (B [ v1 ]TpTms))) 
                            [ apply trueTm ]TmTms) =<Tm coerce-Tm-coh >

                        (ifTm coerce-Tm tms-BOOL v0 
                        then toTm (liftTpR n' (A [ v1 ]TpTms)) 
                        else toTm (liftTpL n (B [ v1 ]TpTms))) 
                        [ apply trueTm ]TmTms =<Tm tms-ite >

                        ifTm coerce-Tm tms-BOOL (coerce-Tm tms-BOOL v0 [ apply trueTm ]TmTms)
                        then toTm (liftTpR n' (A [ v1 ]TpTms)) [ apply trueTm ]TmTms 
                        else (toTm (liftTpL n (B [ v1 ]TpTms)) [ apply trueTm ]TmTms) =<Tm ite-cong (trans-Tm coerce-Tm-coh (trans-Tm (tms-cong-fst-Tm coerce-Tm-coh) (trans-Tm tms-v0-addTm-Tm coerce-Tm-coh))) refl-Tm refl-Tm >

                        ifTm trueTm
                        then toTm (liftTpR n' (A [ v1 ]TpTms)) [ apply trueTm ]TmTms 
                        else (toTm (liftTpL n (B [ v1 ]TpTms)) [ apply trueTm ]TmTms) =<Tm ite-true >

                        toTm (liftTpR n' (A [ v1 ]TpTms)) [ apply trueTm ]TmTms =<Tm toTm-tms >
                        toTm (liftTpR n' (A [ v1 ]TpTms) [ apply trueTm ]TpTms)  =<Tm toTm-cong tms-Sig >
                        toTm (Sig ((A [ v1 ]TpTms) [ apply trueTm ]TpTms) ((UNIT [ v1 ]TpTms) [ apply trueTm transformTp (A [ v1 ]TpTms) ]TpTms)) =<Tm toTm-cong (Sig-cong 
                            apply-irr-Tp 
                            ((UNIT [ v1 ]TpTms) [ apply trueTm transformTp (A [ v1 ]TpTms) ]TpTms =<Tp tms-assoc-Tp >
                            UNIT [ v1 otms (apply trueTm) transformTp (A [ v1 ]TpTms) ]TpTms =<Tp tms-UNIT >
                            UNIT =<Tp UNIT-Ctx-Eq (::ctx-eq refl-Ctx apply-irr-Tp) >
                            UNIT =<Tp sym-Tp tms-UNIT >
                            UNIT [ v1 ]TpTms qedTp)) >
                        
                        toTm (Sig A (UNIT [ v1 ]TpTms)) =<Tm>
                        
                        toTm (liftTpR n' A) qedTm) >

                toTp (toTm (liftTpR n' A)) =<Tp toTp-o-toTm-id >

                A :x: UNIT qedTp

    v0 : Tm (Gamma ::ctx A) (A [ v1 ]TpTms)
    v0 = v0' 

    v0Tp : Tm (Gamma ::ctx SetS n) (SetS n)
    v0Tp = coerce-Tm tms-SetS v0

    _transformTp_ : (tms : Tms Gamma Delta) -> (A : Tp Delta n) -> Tms (Gamma ::ctx (A [ tms ]TpTms)) (Delta ::ctx A)
    _transformTp_ tms A = (tms otms v1) addTm (coerce-Tm tms-assoc-Tp v0)


    tms-apply-Tp : (B $Tp a) [ tms ]TpTms =Tp= (B [ tms transformTp A ]TpTms) $Tp (a [ tms ]TmTms)
    tms-apply-Tp {A} {B} {a} {tms} = 
        (B $Tp a) [ tms ]TpTms =<Tp tms-assoc-Tp >
        B [ apply a otms tms ]TpTms =<Tp tms-cong-Tp refl-Tp otms-addTm >
        B [ (idtms otms tms) addTm coerce-Tm tms-assoc-Tp (coerce-Tm (sym-Tp tms-idtms-Tp) a [ tms ]TmTms) ]TpTms =<Tp tms-cong-Tp refl-Tp (
            (idtms otms tms) addTm coerce-Tm tms-assoc-Tp (coerce-Tm (sym-Tp tms-idtms-Tp) a [ tms ]TmTms) =<Tms addTm-cong refl-Tms (
                coerce-Tm tms-assoc-Tp (coerce-Tm (sym-Tp tms-idtms-Tp) a [ tms ]TmTms) =<Tm coerce-Tm-coh >
                coerce-Tm (sym-Tp tms-idtms-Tp) a [ tms ]TmTms =<Tm tms-cong-fst-Tm coerce-Tm-coh >
                a [ tms ]TmTms =<Tm tms-cong-Tm refl-Tm (sym-Tms idtms-left-id) >
                a [ idtms otms tms ]TmTms qedTm ) >
            (idtms otms tms) addTm (a [ idtms otms tms ]TmTms) =<Tms addTm-cong idtms-left-id (tms-cong-Tm refl-Tm idtms-left-id) >
            tms addTm (a [ tms ]TmTms) =<Tms addTm-cong 
                -- tms eq
                (tms =<Tms sym-Tms idtms-right-id >
                tms otms idtms =<Tms otms-cong refl-Tms (sym-Tms v1-otms) >
                tms otms (v1 otms (idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms))) =<Tms sym-Tms otms-assoc >
                (tms otms v1) otms (idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms)) qedTms) 
                -- tm eq
                (a [ tms ]TmTms =<Tm sym-Tm coerce-Tm-coh >
                coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms) =<Tm sym-Tm tms-v0-addTm-Tm >
                v0 [ idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms) ]TmTms =<Tm tms-cong-fst-Tm (sym-Tm coerce-Tm-coh) >
                coerce-Tm tms-assoc-Tp v0 [ idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms)]TmTms =<Tm sym-Tm coerce-Tm-coh >
                coerce-Tm tms-assoc-Tp (coerce-Tm tms-assoc-Tp v0 [ idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms)]TmTms) qedTm ) >
            ((tms otms v1) otms (idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms))) addTm (coerce-Tm tms-assoc-Tp (coerce-Tm tms-assoc-Tp v0 [ idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms)]TmTms)) =<Tms sym-Tms otms-addTm >
            ((tms otms v1) addTm coerce-Tm tms-assoc-Tp v0) otms (idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms)) qedTms ) >
        B [ ((tms otms v1) addTm coerce-Tm tms-assoc-Tp v0) otms (idtms addTm coerce-Tm (sym-Tp tms-idtms-Tp) (a [ tms ]TmTms)) ]TpTms =<Tp>
        B [ (tms transformTp A) otms apply (a [ tms ]TmTms) ]TpTms =<Tp sym-Tp tms-assoc-Tp >
        (B [ tms transformTp A ]TpTms) $Tp (a [ tms ]TmTms) qedTp

    -- _transformTm_ : (tms : Tms Gamma Delta) -> (a : Tm Delta A) -> Tms (Gamma ::ctx ) (Delta ::ctx A)
    -- _transformTm_ tms A = (tms otms v1) addTm (coerce-Tm tms-assoc-Tp v0)

    tms-cong-fst-Tm : a =Tm= b -> a [ tms ]TmTms =Tm= b [ tms ]TmTms
    tms-cong-fst-Tm eq = tms-cong-Tm eq refl-Tms

    Pi-cong-fst : (A=Tp=C : A =Tp= C) -> Pi A B =Tp= Pi C (coerce-Tp (ctx-Tp-eq A=Tp=C) B)
    Pi-cong-fst eq = Pi-cong eq (sym-Tp coerce-Tp-coh)
    
    Pi-cong-snd : B =Tp= C -> Pi A B =Tp= Pi A C
    Pi-cong-snd eq = Pi-cong refl-Tp eq

    tms-cong-fst-Tp  : A =Tp= B -> A [ tms ]TpTms =Tp= B [ tms ]TpTms
    tms-cong-fst-Tp eq = tms-cong-Tp eq refl-Tms

    tms-=> : (A => B) [ tms ]TpTms =Tp= (A [ tms ]TpTms) => (B [ tms ]TpTms)
    tms-=> {A} {B} {tms} = 
        Pi A (B [ v1 ]TpTms) [ tms ]TpTms =<Tp tms-Pi >
        Pi (A [ tms ]TpTms) ((B [ v1 ]TpTms) [ tms transformTp A ]TpTms) =<Tp Pi-cong-snd tms-assoc-Tp >
        Pi (A [ tms ]TpTms) (B [ v1 otms tms transformTp A ]TpTms) =<Tp Pi-cong-snd (tms-cong-Tp refl-Tp v1-otms) >
        Pi (A [ tms ]TpTms) (B [ tms otms v1 ]TpTms) =<Tp Pi-cong-snd (sym-Tp tms-assoc-Tp) >
        Pi (A [ tms ]TpTms) ((B [ tms ]TpTms) [ v1 ]TpTms) qedTp

    lift-func : Tm Gamma (A => B) -> Tm (Gamma ::ctx C) (A [ v1 ]TpTms => B [ v1 ]TpTms)
    lift-func f = coerce-Tm tms-=> (f [ v1 ]TmTms)

    _oTm_ : Tm Gamma (B => C) -> Tm Gamma (A => B) -> Tm Gamma (A => C)
    f oTm g = lam ((lift-func f) $Tm' app g)

    _oTm-tms_ : Tm Gamma ((B => C) [ tms ]TpTms) -> Tm Gamma ((A => B) [ tms ]TpTms) -> Tm Gamma ((A => C) [ tms ]TpTms)
    f oTm-tms g = coerce-Tm (sym-Tp tms-=>) (coerce-Tm tms-=> f oTm coerce-Tm tms-=> g)

    ContainerTp : (n n' : Nat) -> Tp Gamma (max (1+ n) (max n (1+ n')))
    ContainerTp n n' = Sig (SetS n) ((toTp v0Tp) => (SetS n'))
    
    W : Tm Gamma (ContainerTp n n') -> Tp Gamma (max (1+ n) (max n (1+ n')))
    W = W'

    [[_]] : Tm Gamma (ContainerTp n n') -> Tp Gamma n'' -> Tp Gamma (max n (max n' n''))
    [[_]] S|>P A = Sig (toTp (fstTm S|>P)) ((coerce-Tp (::ctx-eq refl-Ctx eq) o toTpTms2 o app o coerce-Tm tms-=>) (sndTm S|>P) => A [ v1 ]TpTms)
        where
            eq : (toTp v0Tp [ apply (fstTm S|>P) ]TpTms) =Tp= toTp (fstTm S|>P)
            eq = 
                toTp v0Tp [ apply (fstTm S|>P) ]TpTms =<Tp toTp-tms >
                toTp (coerce-Tm tms-SetS (v0Tp [ apply (fstTm S|>P) ]TmTms)) =<Tp toTp-cong (trans-Tm coerce-Tm-coh (trans-Tm (tms-cong-fst-Tm coerce-Tm-coh) (trans-Tm tms-v0-addTm-Tm coerce-Tm-coh))) >
                toTp (fstTm S|>P) qedTp


    foldC : {A : Tp Gamma n''}{C : Tm Gamma (ContainerTp n n')} -> Tm (Gamma ::ctx [[ C ]] A) (A [ v1 ]TpTms) -> Tm (Gamma ::ctx W C) (A [ v1 ]TpTms)
    foldC = foldC'

    In : {C : Tm Gamma (ContainerTp n n')} -> Tm Gamma ([[ C ]] (W C)) -> Tm Gamma (W C)
    In = In'

    mapC : Tm (Gamma ::ctx A) (B [ v1 ]TpTms) -> Tm Gamma ([[ C ]] A) -> Tm Gamma ([[ C ]] B)
    mapC f s,p = sigma (fstTm s,p) ((lift-func (lam f) [ apply (fstTm s,p) ]TmTms) oTm-tms (sndTm s,p))