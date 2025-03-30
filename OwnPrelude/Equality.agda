{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Equality where

open import ASCIIPrelude.ASCIIPrelude
open PolyZero
open PolyUnit
open import Cubical.Core.Everything

-- \tagcode{CubicalEquality}

open import Cubical.Core.Everything public
    using (~_; i0; i1; hcomp; comp; fill; inS; transp; PathP)
    renaming (
          _∧_ to _/\-path_
        ; _∨_ to _\/-path_
        ; I to Ivl
    )

open import Cubical.Foundations.Prelude public
    using (congP; transport; compPath-unique)
    renaming 
        ( _∙_ to trans ; compPath-filler to transFill ; compPathP to trans' ; compPathP' to transSubst') 

open import Cubical.Foundations.Transport public
    using (substComposite)

private
    variable
        k' i' j' : Level
        n n' : Nat
        ST : Set _
        a b c d e f g h i j k l m p q r s t u v w x y z A B C D E F G H K L M N O P Q R S T U V W X Y Z : ST

infix -1 _===_
_===_ : {A : Set i} -> (a b : A) -> Set i
_===_ {A} a b = Path A a b 

_=/=_ : {A : Set i} -> (a b : A) -> Set i
a =/= b = ¬(a === b)


path-to-eq : (P : I -> A) -> P i0 === P i1
path-to-eq P i = P i

eq-to-path : {a b : A} -> (a=b : a === b) -> ((i : I) -> A)
eq-to-path a=b i = a=b i

PathP' : {A B : Set i} -> (A === B) -> A -> B -> Set i
PathP' A=B a b = PathP (\i -> A=B i) a b
infix -1 PathP'
syntax PathP' p a b = a =< p >= b

propToPath : forall {a b : A} -> a PropositionalEq.=== b -> a === b
propToPath {a} {b} PropositionalEq.refl i = b

refl : {a : A} -> a === a
refl {a} i = a

sym : {a b : A} -> a === b -> b === a
sym a=b i = a=b (~ i)

sym' : {eq : A === B} {a : A} {b : B} -> a =< eq >= b -> b =< sym eq >= a
sym' a=b i = a=b (~ i)

-- imported from prelude now
-- trans : {a b c : A} -> a === b -> b === c -> a === c
-- trans {a} a=b b=c i = hcomp (\j -> \{
--       (i = i0) -> a
--     ; (i = i1) -> b=c j}) (a=b i)

cong : {a b : A} ->
    (f : A -> B) -> a === b ->  f a === f b
cong f a=b i = f (a=b i)
{-# INLINE cong #-}

infixl 1 _||_
_||_ : {a b : A} ->
    a === b -> (f : A -> B) -> f a === f b
_||_ a=b f = cong f a=b


extens : {f g : A -> B} ->
    ((a : A) -> f a === g a) -> f === g
extens ex i a = ex a i

extensPi : {A : Set i} {B : A -> Set j} {f g : (a : A) -> B a} -> 
    ((a : A) -> f a === g a) -> f === g
extensPi ex i a = ex a i


transpFill : (A=B : A === B) -> (p : A) -> p =< A=B >= (transp (\j -> A=B j) i0 p)
transpFill P p i = transp (\j -> P (i /\-path j)) (~ i) p

coerce : A === B -> A -> B
coerce A=B a = transp (\j -> A=B j) i0 a

coercei1 : (A=B : A === B) -> {i : I} -> (a : A=B i) -> A=B i1
coercei1 A=B {i} a = transp (\j -> A=B (i \/-path j)) i a 

coerce~i1 : (A=B : A === B) -> {i : I} -> (a : A=B i) -> A=B i1
coerce~i1 A=B {i} a = transp (\j -> A=B (i \/-path j)) i0 a

coercei0 : (A=B : A === B) -> {i : I} -> (a : A=B i) -> A=B i0
coercei0 A=B {i} a = transp (\j -> A=B (i /\-path ~ j)) i0 a

coerce~i0 : (A=B : A === B) -> {i : I} -> (a : A=B i) -> A=B i0
coerce~i0 A=B {i} a = transp (\j -> A=B (i /\-path ~ j)) (~ i) a

coerceEq : {A=B : A === B} -> {a : (i : I) -> A=B i} -> coerce A=B (a i0) === (a i1)
coerceEq {A=B} {a} i = coercei1 A=B {i} (a i)

coerce-trans-subst : (P : A -> Set i) -> {a b c : A} -> (p : a === b) (q : b === c) -> coerce (q || P) o coerce (p || P) === coerce (trans p q || P)
coerce-trans-subst P p q = extens \x -> sym (substComposite P p q x)

coerce-sym-subst : (P : A -> Set i) {a b : A} (p : a === b) -> coerce (p || P) o coerce (sym p || P) === id
coerce-sym-subst P p i x = transp (\ j -> (p || P) (j \/-path i)) i (transp (\j -> (sym p || P) (j /\-path ~ i)) i x)

absurdCoerc : {A : Set i} -> Unit {i} === Zero {i} -> A
absurdCoerc p = absurd (coerce p unit)

absurdEq : {P : Ivl -> Set i} -> PathP (\i -> Zero {k} -> P i) absurd (\())
absurdEq i ()

coerce-refl : {A : Set i} {x : A} -> coerce (refl {A = Set i}) x === x
coerce-refl {i} {A} {x} k = transp (\j -> refl {A = Set i} {a = A} j) k x

module _ {a b : A} {P : A -> Set i} {p : P a} where
    coerceSig : (eq : a === b) -> (a , p) === (b , coerce (eq || P) p)
    coerceSig eq i = eq i , transp (\j -> P (eq (i /\-path j))) (~ i) p


J : {A : Set i} {x : A} (P : forall y -> x === y -> Set i)
      (d : P x refl) {y : A} (p : x === y)
    -> P y p
J P d p = coerce (\ i -> P (p i) (\ j -> p (i /\-path j))) d

-- JP further down


congP' = congP
congP'' = congP
syntax congP' (\_ -> f) p = p ||P f
syntax congP'' (\i -> f) p = p ||P[ i ] f

JP : {A : Set i} {Q : Set i -> Set j} {x : Q A} 
    (P : forall {B : Set i} {A=B : A === B} y -> x =< A=B || Q >= y -> Set k)
    (d : P {A=B = refl} x refl) {A=B : A === B} {y : Q B} (p : x =< A=B || Q >= y)
    -> P y p
JP P d p = coerce (\i -> P (p i) \j -> p (i /\-path j)) d

-- imported from prelude
-- trans' : {p : A === B} {q : B === C} -> a =< p >= b -> b =< q >= c -> a =< trans p q >= c
-- trans' = Cubical.Foundations.Prelude.compPathP

module _ {P : A -> Set i} where
    subst : a === b -> P a -> P b
    subst eq = coerce (eq || P)

    subst' : {a b : A} -> (eq : a === b) -> P a === P b
    subst' eq = eq || P

module _ {a b : A} {P : A -> Set i} {p : P a} {q : P b} where
    SigEq : (fstEq : a === b) -> (p =< (\i -> P (fstEq i)) >= q) -> (a , p) === (b , q)
    SigEq fstEq pathEq i = fstEq i , pathEq i

congPi : {A : Set i} {B : A -> Set j}{a b : A} ->
    (f : (a : A) -> B a) -> (a=b : a === b) -> (f a) =< a=b || B >= (f b)
congPi {B} f a=b i = f (a=b i)

infixl 1 _|||_
_|||_ : {A : Set i} {B : A -> Set j}{a b : A} ->
    (a=b : a === b) -> (f : (a : A) -> B a) -> (f a) =< a=b || B >= (f b)
_|||_ a=b f = congPi f a=b


infixl 1 _|f_
_|f_ : {a b : C -> A} ->
    ((c : C) -> a c === b c) -> (f : (C -> A) -> B) -> f a === f b
(ac=bc |f f) = cong f (extens \c -> ac=bc c)

infixl 1 _|f2_
_|f2_ : {a b : C -> D -> A} ->
    ((c : C) -> (d : D) -> a c d === b c d) -> (f : (C -> D -> A) -> B) -> f a === f b
(acd=bcd |f2 f) = cong f (extens \c -> extens \d -> acd=bcd c d)

infixl 1 _|f3_
_|f3_ : {a b : C -> D -> E -> A} ->
    ((c : C) -> (d : D) -> (e : E) -> a c d e === b c d e) -> (f : (C -> D -> E -> A) -> B) -> f a === f b
(acd=bcd |f3 f) = cong f (extens \c -> extens \d -> extens \e -> acd=bcd c d e)


infixl 1 _|pi_
_|pi_ : {A : C -> Set i}{a b : (c : C) -> A c} ->
    ((c : C) -> a c === b c) -> (f : ((c : C) -> A c) -> B) -> f a === f b
(ac=bc |pi f) = cong f (extensPi \c -> ac=bc c)

infixl 1 _|pi2_
_|pi2_ : {D : C -> Set j}{A : (c : C) -> D c -> Set i}{a b : (c : C) (d : D c) -> A c d} ->
    ((c : C) (d : D c) -> a c d === b c d) -> (f : ((c : C) (d : D c) -> A c d) -> B) -> f a === f b
(ac=bc |pi2 f) = cong f (extensPi \c -> extensPi \d -> ac=bc c d)

infixl 1 _|pi3_
_|pi3_ : {D : C -> Set j}{E : (c : C) -> D c -> Set k}{A : (c : C) -> (d : D c) -> E c d -> Set i}{a b : (c : C) (d : D c) (e : E c d) -> A c d e} ->
    ((c : C) (d : D c) (e : E c d) -> a c d e === b c d e) -> (f : ((c : C) (d : D c) (e : E c d) -> A c d e) -> B) -> f a === f b
(ac=bc |pi3 f) = cong f (extensPi \c -> extensPi \d -> extensPi \e -> ac=bc c d e) 

infix 3 _qed
_qed : (a : A) -> a === a
_qed a = refl {a = a}

infix 3 qedSig
qedSig : (P : A -> Set i) -> {a : A} (x : P a) ->  x =< refl || P >= x
qedSig _ x = refl {a = x}

syntax qedSig P x = x qedSig[ P ]

infixr 2 step->
step-> : forall {b c} -> (a : A) -> b === c -> a === b -> a === c
step-> _ b=c a=b = trans a=b b=c

infixr 2 step->>
step->> : forall {b} -> (a : A) -> a === b -> a === b
step->> _ a=b = a=b

syntax step-> a b=c a=b = a =< a=b > b=c
syntax step->> a a=b = a =<> a=b 

infixr 2 step->'
step->' : forall {q : B === C} {b : B} {c : C} -> (a : A) -> forall {p : A === B} -> b =< q >= c -> a =< p >= b -> a =< step-> _ q p >= c
step->' _ b=c a=b = trans' a=b b=c

syntax step->' a b=c a=b = a =<' a=b > b=c

infixr 2 step->Sig
step->Sig : forall (P : A -> Set i) {y z} {b : P y} {c : P z} {q : y === z} {x} -> (a : P x) -> forall {p : x === y} -> b =< q || P >= c -> a =< p || P >= b -> a =< trans p q || P >= c
step->Sig {A} P {y} {z} {x} _ b=c a=b = transSubst' {A = A} {x = x} {y = y} {z = z} {B = P} a=b b=c

syntax step->Sig P a b=c a=b = a =<Sig[ P ] a=b > b=c

infixr 2 step->Sig'
step->Sig' : forall {x y z} (P : A -> Set i) {b : P y} {c : P z} (p : x === y) {q : y === z} -> (a : P x) -> b =< q || P >= c -> a =< p || P >= b -> a =< trans p q || P >= c
step->Sig' {A} {x} {y} {z} P p _ b=c a=b = transSubst' {A = A} {x = x} {y = y} {z = z} {B = P} a=b b=c

syntax step->Sig' P p a b=c a=b = a =<Sig[ P ][ p ] a=b > b=c

infixr 2 step->Sig''
step->Sig'' : forall {x y z} (P : A -> Set i) {b : P y} {c : P z} (p : x === y) (q : y === z) -> (a : P x) -> b =< q || P >= c -> a =< p || P >= b -> a =< trans p q || P >= c
step->Sig'' {A} {x} {y} {z} P p q _ b=c a=b = transSubst' {A = A} {x = x} {y = y} {z = z} {B = P} a=b b=c

syntax step->Sig'' P p q a b=c a=b = a =<Sig[ P ][ q ][ p ] a=b > b=c

infixr 2 _=<P_>=_
_=<P_>=_ : {P : A === B} {a b : A} {c d : B} -> a === b -> b =< P >= c -> c === d  -> a =< P >= d
_=<P_>=_ {P} a=b b=c c=d i = comp (\j -> P i) (
    \{ j (i = i0) -> a=b (~ j)
    ;  j (i = i1) -> c=d j }) (b=c i)

infixr 2 step->SigInterm
step->SigInterm : (a : A) -> b =< P >= c -> a === b -> a =< P >= c
step->SigInterm {P} {c} a b=c a=b i = comp (\j -> P i) (
    \{ j (i = i0) -> a=b (~ j)
    ;  j (i = i1) -> c }) (b=c i)

syntax step->SigInterm a b=c a=b = a =< a=b >P b=c


refl-refl : {a : A} -> refl {A = A} {a} === refl {A = A} {a}
refl-refl = refl

refl-sym : {a : A} -> refl {A = A} {a} === sym (refl {A = A} {a})
refl-sym = refl

trans-cong-left : {ab1 ab2 : a === b}(abeq : ab1 === ab2){bc : b === c} -> trans ab1 bc === trans ab2 bc
trans-cong-left abeq {bc} = (abeq || trans) || (_$ bc)


trans-cong : forall {a b c : A} {a=b : a === b} {b=c : b === c} {f : A -> B} -> trans (a=b || f) (b=c || f) === trans a=b b=c || f
trans-cong {a} {b} {c} {a=b} {b=c} {f} = compPath-unique (refl || f) (a=b || f) (b=c || f) 
    (trans (a=b || f) (b=c || f) , transFill (a=b || f) (b=c || f)) 
    ((trans a=b b=c || f) , \i j -> f (transFill a=b b=c i j)) || fst
    

private variable
    li : I -> Level 


trans-refl-right : {a b : A} {ab : a === b} -> trans ab refl === ab
trans-refl-right {A} {a} {b} {ab} i j = hfill (\k -> \{
      (j = i0) -> a
    ; (j = i1) -> b
    }) (inS (ab j)) (~ i)


trans-refl-left : {a b : A}{ab : a === b} -> trans refl ab === ab
trans-refl-left {A} {a} {b} {ab} i j = hcomp (\k -> 
    \{ (i = i1) -> ab (j /\-path k)
     ; (j = i0) -> a
     ; (j = i1) -> ab k
     }) a

trans-refl-refl : trans refl refl === (refl {A = A} {a = a})
trans-refl-refl = trans-refl-left


module _ {a b c d : A} {ab : a === b} {bc : b === c} {cd : c === d} where
    -- trans-trans : trans ab (trans bc cd) === trans (trans ab bc) cd
    -- trans-trans i j = {!!}
        
        -- hfill (\k -> 
        -- \{(j = i0) -> a
        -- ; (j = i1) -> d}) (inS (trans ab (trans bc cd) j)) i
        
        -- hcomp (\k -> 
        -- \{ (i = i0) -> hfill (\l -> 
        --     \{(j = i0) -> a 
        --     ; (j = i1) -> trans bc cd l }) (inS (ab j)) k
        --  ; (i = i1) -> hfill (\l -> 
        --     \{(j = i0) -> a
        --     ; (j = i1) -> cd l}) (inS (trans ab bc j)) k
        --  ; (j = i0) -> a
        --  ; (j = i1) -> hfill (\l -> 
        --     \{(i = i0) -> trans bc cd l 
        --     ; (i = i1) -> cd l}) (inS (bc i)) k
        -- })
        -- (hfill (\k -> \{ (i = i0) -> ab k
        --                ; (i = i1) -> trans ab bc k
        --                }) (inS a) j)




        -- (j = i1) -> hfill (\l -> 
        --     \{(i = i0) -> trans bc cd (~ l) 
        --     ; (i = i1) -> cd (~ l)}) (inS d) (~ k)




--------------------------------------------
-- Univalence
--------------------------------------------
module _ {A : Set i} {B : Set j} where
    record IsIsomorphism (to : A -> B) (from : B -> A) : Set (i ~U~ j) where
        field
            to-o-from=id : to o from === id
            from-o-to=id : from o to === id
            
        to[from[x]]=x : forall {x} -> to (from x) === x
        to[from[x]]=x {x} = to-o-from=id || (_$ x)
        
        from[to[x]]=x : forall {x} -> from (to x) === x
        from[to[x]]=x {x} = from-o-to=id || (_$ x)

record Isomorphism (A : Set i) (B : Set j) : Set (i ~U~ j) where
    field
        to : A -> B
        from : B -> A
        isIsomorphism : IsIsomorphism to from
    open IsIsomorphism isIsomorphism public

isomorphismRefl : Isomorphism A A
isomorphismRefl .Isomorphism.to = id
isomorphismRefl .Isomorphism.from = id
isomorphismRefl .Isomorphism.isIsomorphism .IsIsomorphism.to-o-from=id = refl
isomorphismRefl .Isomorphism.isIsomorphism .IsIsomorphism.from-o-to=id = refl

open import Cubical.Foundations.Isomorphism

module _ (isom : Isomorphism A B) where
    open Isomorphism isom
    Isomorphism->Iso : Iso A B
    Isomorphism->Iso .Iso.fun = to
    Isomorphism->Iso .Iso.inv = from
    Isomorphism->Iso .Iso.rightInv x = to[from[x]]=x {x}
    Isomorphism->Iso .Iso.leftInv x = from[to[x]]=x {x}

module _ {A B : Set i} (iso : Isomorphism A B) where
    open Isomorphism iso
 
    Iso->=== : A === B  
    Iso->=== = isoToPath (Isomorphism->Iso iso)



symEq : (a === b) === (b === a)
symEq = Iso->=== (record { 
    to = sym ; 
    from = sym ; 
    isIsomorphism = record { 
        to-o-from=id = refl ; 
        from-o-to=id = refl } })
