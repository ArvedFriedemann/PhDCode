{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.Decidables where

open import ASCIIPrelude.ASCIIPrelude 
open PolyZero
open PolyUnit
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)

open ExistsSyntax

private
    variable
        h i j k k' l i' j' u : Level
        n n' : Nat
        A B C X Y Z L L1 L2 S S1 S2 : Set _
        F G M : Set i -> Set j
        a b c d r x y z m x1 x2 y1 y2 z1 z2 p a=b b=c a=c ¬a=b ¬b=c ¬a=c R P : A
        f g : A -> B

data Dec (A : Set i) : Set i where
    yes :  (a :   A) -> Dec A
    no  : (¬a : ¬ A) -> Dec A 

module _ {A : Set i} where
    CoverDec : Dec A -> Dec A -> Set i
    CoverDec (yes x) (yes y) = x === y
    CoverDec (no x)  (no y)  = x === y
    CoverDec _ _ = Zero

    CoverDec' : (A === B) -> Dec A -> Dec B -> Set i
    CoverDec' A=B (yes x) (yes y) = x =< A=B >= y
    CoverDec' A=B (no x)  (no y)  = x =< A=B || ¬_ >= y
    CoverDec' A=B _ _ = Zero

    encodeReflDec : CoverDec a a
    encodeReflDec {yes x} = refl
    encodeReflDec {no x}  = refl

    encodeReflDec' : CoverDec' refl a a
    encodeReflDec' {yes x} = refl
    encodeReflDec' {no x}  = refl

    encodeDec : {a b : Dec A} -> a === b -> CoverDec a b
    encodeDec {a} = J (\b _ -> CoverDec a b) encodeReflDec

    encodeDec' : {A=B : A === B} {a : Dec A}{b : Dec B}  -> a =< A=B || Dec >= b -> CoverDec' A=B a b
    encodeDec' {A=B} {a} = JP (\{_} {A=B} b a=b -> CoverDec' A=B a b) encodeReflDec'


_isTrue : {A : Set i} -> Dec A -> Set i
(yes _) isTrue = Unit
_ isTrue = Zero

_isFalse : {A : Set i} -> Dec A -> Set i
(yes _) isFalse = Zero
_ isFalse = Unit

fromTrue : (a : Dec A) -> a isTrue -> A
fromTrue (yes x) t = x

fromFalse : (a : Dec A) -> a isFalse -> ¬ A
fromFalse (no x) t = x

infix 1 ifDec'_then_else_
ifDec'_then_else_ : (d : Dec A) -> ((a : A) -> d === yes a -> B) -> ((a : ¬ A) -> d === no a -> B) -> B
ifDec' yes a then x else y = x  a refl
ifDec' no ¬a then x else y = y ¬a refl

infix 1 ifDec_then_else_
ifDec_then_else_ : Dec A -> (A -> B) -> (¬ A -> B) -> B
ifDec d then y else n = ifDec' d then (\x _ -> y x) else (\x _ -> n x) 

ifDecEqYes : forall {d : Dec R} {a c : R -> A} -> (d=yes : d === yes r) (a=c : a === c) -> ifDec d then (a=c i0) else b === (a=c i1 r)
ifDecEqYes {b} d=yes a=c i = ifDec (d=yes i) then a=c i else b

ifDecEqYesP : forall {d : Dec R} {P : A === B} {a : R -> P i0} {c : R -> P i1} -> (d=yes : d === yes r) (a=c : a =< (\i -> R -> (P i)) >= c) {b : ¬ R -> P i0} -> ifDec d then (a=c i0) else b =< P >= (a=c i1 r)
ifDecEqYesP {r} {P} d=yes a=c {b} i = ifDec (d=yes i) then a=c i else transp (\j -> P (i /\-path j)) (~ i) o b

[_]ifDecPi_then_else_ : (B : Dec A -> Set i) -> (d : Dec A) -> ((a : A) -> B (yes a)) -> ((a : ¬ A) -> B (no a)) -> B d
[ _ ]ifDecPi yes a then x else y = x a
[ _ ]ifDecPi no ¬a then x else y = y ¬a


module _ where
    [_]ifDecPi'_then_else : (B : Dec A -> Set i) -> (d : Dec A) -> ((a : A) -> d === yes a -> B (yes a)) -> ((a : ¬ A) -> d === no a -> B (no a)) -> B d
    [ B ]ifDecPi' yes a then x else y = x a refl
    [ B ]ifDecPi' no ¬a then x else y = y ¬a refl 

    ifDecPiCase_then_else_ : {B : Dec A -> Set i} -> (d : Dec A) -> ((a : A) -> d === yes a -> B (yes a)) -> ((a : ¬ A) -> d === no a -> B (no a)) -> case d of B
    ifDecPiCase yes a then x else y = x a refl
    ifDecPiCase no ¬a then x else y = y ¬a refl

    [_]ifDecPiCase_then_else_ : (B : Dec A -> Set i) -> (d : Dec A) -> ((a : A) -> d === yes a -> B (yes a)) -> ((a : ¬ A) -> d === no a -> B (no a)) -> case d of B
    [_]ifDecPiCase_then_else_ B = ifDecPiCase_then_else_ {B = B}

    [_,_]ifDecPiCase:_makes:_ : (P : X -> Set i) -> (f : (d1 : Dec A) -> X) -> 
        (d1 : Dec A) ->
        (g : (d1' : Dec A) (eq1 : d1 === d1') -> P (f d1')) -> P (f d1)
    [ B , f ]ifDecPiCase: d1 makes: g = g d1 refl 

    [_,_]ifDecPiCase3:_,_,_makes:_ : (P : X -> Set i) -> (f : (d1 : Dec A) (d2 : Dec B) (d3 : Dec C)-> X) -> 
        (d3 : Dec C) -> (d2 : Dec B) -> (d1 : Dec A) ->
        (g : (d1' : Dec A) (eq1 : d1 === d1') (d2' : Dec B) (eq2 : d2 === d2') (d3' : Dec C) (eq3 : d3 === d3') -> P (f d1' d2' d3')) -> P (f d1 d2 d3)
    [ B , f ]ifDecPiCase3: d1 , d2 , d3 makes: g = g d3 refl d2 refl d1 refl 

infix 1 _<?decf>[_][_]
_<?decf>[_][_] = ifDec_then_else_

id-synt = id
syntax id-synt (\x -> X) = x := X

infix 1 _<?dec>[_][_]
_<?dec>[_][_] : Dec A -> B -> B -> B
d <?dec>[ y ][ n ] = d <?decf>[ _ := y ][ _ := n ]


-- _<?dec>[_][_] : Dec A -> B -> B -> B
-- yes x <?dec>[ y ][ n ] = y
-- no x  <?dec>[ y ][ n ] = n


record DecEq (A : Set i) : Set i where
    infix 2 _==_
    field
        _==_ : (a b : A) -> Dec (a === b)
        decEq-refl   : a == a === yes (refl {a = a})
        decEq-sym    : a == b === yes a=b -> b == a === yes (sym a=b)
        decEq-sym-no : a == b === no ¬a=b -> b == a === no (¬a=b o sym)
        decEq-trans  : a == b === yes a=b -> b == c === yes b=c -> a == c === yes (trans a=b b=c)


    coerce-refl-DecEq : forall {P : A -> Set k} {x} {x=x} -> (x == x === yes x=x) -> coerce (x=x || P) === id
    coerce-refl-DecEq {P} {x} {x=x} x==x=yes = 
        coerce (x=x || P) =< encodeDec' (trans (sym x==x=yes) (decEq-refl {a = x})) || (\h -> coerce (h || P)) >
        coerce (refl || P) =< (\i pm -> transp (\j -> (refl {a = x} || P) j) i pm) >
        id qed

    -- decEq-trans b==c=yes (decEq-sym a==c=yes)
    --  trans' (sym (decEq-sym a==b=yes)) (decEq-trans b==c=yes (decEq-sym a==c=yes))
    -- yes (sym a=b) =<Sig[ (\x -> Dec (a === x)) ] (sym (decEq-sym a==b=yes)) > (decEq-trans b==c=yes (decEq-sym a==c=yes)) 
    -- ((encodeDec' (transSubst' (sym (decEq-sym a==b=yes)) (decEq-trans b==c=yes (decEq-sym a==c=yes)))) i)
    -- (sym (decEq-sym a==b=yes)) =<P (decEq-trans b==c=yes (decEq-sym a==c=yes)) >= refl 
    -- decEq-trans-triag : a == b === yes a=b -> b == c === yes b=c -> a == c === yes a=c -> a == b =< b=c || (\x -> Dec (a === x)) >= a == c
    -- decEq-trans-triag {a} {b} {a=b} {c} {b=c} {a=c} a==b=yes b==c=yes a==c=yes = a==b=yes =<P (\i -> yes $ sym {a = b=c i} {b = a} ((encodeDec' {A = a === b} {B = a === c}{A=B = {!   !}} (transSubst' (sym (decEq-sym a==b=yes)) (decEq-trans b==c=yes (decEq-sym a==c=yes)))) i)) >= sym a==c=yes

    module _ {x y : A} {b c : B} where
        applyEq-<?dec> : x === y -> x == y <?dec>[ b ][ c ] === b
        applyEq-<?dec> eq = 
            ifDec' x == y
            then (\_ x==y=yes -> x==y=yes || _<?dec>[ b ][ c ] )-- (x == y <?dec>[ b ][ c ]) =< x==y=yes || _<?dec>[ b ][ c ] > b qed)
            else \ ¬a _ -> absurd (¬a eq)

        applyNEq-<?dec> : x =/= y -> x == y <?dec>[ b ][ c ] === c
        applyNEq-<?dec> ¬eq = 
            ifDec' x == y
            then (\eq _ -> absurd (¬eq eq))
            else \_ x==y=no -> x==y=no || _<?dec>[ b ][ c ] -- (x == y <?dec>[ b ][ c ]) =< x==y=no || _<?dec>[ b ][ c ] > c qed


open PropositionalEq using () renaming (_===_ to _=P=_ ; _=/=_ to _=/P/=_)

record PropDecEq (A : Set i) : Set i where
    field
        _==_ : (a b : A) -> Dec (a =P= b)

record DecEqPropIso (A : Set i) : Set (lsuc i) where
    field
        propDecEq     : PropDecEq A
        eqIso     : {a b : A} -> Isomorphism (a === b) (a =P= b)

    prop-eq-eq : {a b : A} -> (a === b) === (a =P= b)
    prop-eq-eq = Iso->=== eqIso

    -- propDecEq : PropDecEq A
    -- propDecEq .PropDecEq._==_ a b = coerce (prop-eq-eq || Dec) (DecEq._==_ decEq a b)

    -- decEq : DecEq A    
    -- decEq .DecEq._==_ a b = coerce (sym prop-eq-eq || Dec) (PropDecEq._==_ propDecEq a b)