{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.BooleanInstances where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import OwnPrelude.Data.Decidables

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u e : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G M : Set i -> Set j
        a b x y z m : A
        f g : A -> B

CoverBool : Bool -> Bool -> Set
CoverBool false false = Unit
CoverBool false true  = Zero
CoverBool true  false = Zero
CoverBool true  true  = Unit

encodeReflBool : CoverBool a a
encodeReflBool {a = false} = unit
encodeReflBool {a = true } = unit

encodeBool : {a b : Bool} -> a === b -> CoverBool a b
encodeBool {a} = J (\b _ -> CoverBool a b) encodeReflBool

boolEqSymProp : {a b : Bool} -> (eq : a === b) -> eq =< (\i -> eq i === eq (~ i)) >= (sym eq)
boolEqSymProp {a} {b} eq i j = eq ((~ i /\-path j) \/-path (i /\-path ~ j))

-- encodeBoolSymProp :  encodeBool eq === 
-- encodeBoolSymProp eb = {!!}

boolDecEq : DecEq Bool
DecEq._==_ boolDecEq false false = yes refl
DecEq._==_ boolDecEq false true  = no encodeBool
DecEq._==_ boolDecEq true  false = no encodeBool
DecEq._==_ boolDecEq true  true  = yes refl
boolDecEq .DecEq.decEq-refl {(false)} = refl
boolDecEq .DecEq.decEq-refl {(true)} = refl
boolDecEq .DecEq.decEq-sym {(false)} {(false)}  {a=b} yesrefl=yesa=b = yes (sym refl) =< (encodeDec yesrefl=yesa=b || yes o sym) >  yes (sym a=b) qed
boolDecEq .DecEq.decEq-sym {(false)} {(true)}   {a=b} yesrefl=yesa=b = absurd (encodeDec yesrefl=yesa=b)
boolDecEq .DecEq.decEq-sym {(true)}  {(false)}  {a=b} yesrefl=yesa=b = absurd (encodeDec yesrefl=yesa=b)
boolDecEq .DecEq.decEq-sym {(true)}  {(true)}   {a=b} yesrefl=yesa=b = yes (sym refl) =< (encodeDec yesrefl=yesa=b || yes o sym) >  yes (sym a=b) qed
boolDecEq .DecEq.decEq-sym-no {(false)} {(false)} {(¬a=b)} noEB=noSymEB = absurd (encodeDec noEB=noSymEB)
boolDecEq .DecEq.decEq-sym-no {(false)} {(true)} {(¬a=b)} noEB=noSymEB = no encodeBool =< ((extens \eq -> absurd (encodeBool eq)) || no) > no (¬a=b o sym) qed
boolDecEq .DecEq.decEq-sym-no {(true)} {(false)} {(¬a=b)} noEB=noSymEB = no encodeBool =< ((extens \eq -> absurd (encodeBool eq)) || no) > no (¬a=b o sym) qed
boolDecEq .DecEq.decEq-sym-no {(true)} {(true)} {(¬a=b)} noEB=noSymEB = absurd (encodeDec noEB=noSymEB)
boolDecEq .DecEq.decEq-trans {a = false} {b = false} {a=b} {c = false} {b=c} a==b=yes b==c=yes = yes refl =< sym (trans-refl-refl || yes) > yes (trans refl refl) =< (\i -> yes (trans (encodeDec a==b=yes i) (encodeDec b==c=yes i))) > yes (trans a=b b=c) qed
boolDecEq .DecEq.decEq-trans {a = false} {b = false} {a=b} {c = true}  {b=c} a==b=yes b==c=yes = absurd (encodeBool b=c)
boolDecEq .DecEq.decEq-trans {a = false} {b = true}  {a=b} {c}         {b=c} a==b=yes b==c=yes = absurd (encodeBool a=b) 
boolDecEq .DecEq.decEq-trans {a = true}  {b = false} {a=b} {c}         {b=c} a==b=yes b==c=yes = absurd (encodeBool a=b) 
boolDecEq .DecEq.decEq-trans {a = true}  {b = true}  {a=b} {c = false} {b=c} a==b=yes b==c=yes = absurd (encodeBool b=c) 
boolDecEq .DecEq.decEq-trans {a = true}  {b = true}  {a=b} {c = true}  {b=c} a==b=yes b==c=yes = yes refl =< sym (trans-refl-refl || yes) > yes (trans refl refl) =< (\i -> yes (trans (encodeDec a==b=yes i) (encodeDec b==c=yes i))) > yes (trans a=b b=c) qed