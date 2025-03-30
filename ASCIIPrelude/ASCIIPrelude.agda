{-# OPTIONS --without-K --cubical-compatible #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module ASCIIPrelude.ASCIIPrelude where


open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _~U~_; lift to liftL; Lift to LiftL; Setω to Setw) public


private
    variable
        h i j k l l' l'' l''' l1 l2 l3 : Level
        A B C : Set l

it : forall {l} {A : Set l} -> {{ a : A }} -> A
it {{ a }} = a

module ProofSyntax where
    infix 1 typeOf
    typeOf : (A : Set i) -> A -> A
    typeOf _ a = a

    syntax typeOf A a = a :T: A

    infixr 0 _[premise]_
    _[premise]_ : A -> B -> B
    _ [premise] b = b
    
open ProofSyntax public

open import Function using (
        id
        ; const
        ; flip
        ; _$_
        ; _on_
    ) renaming (
        _∘_ to _o_
    ) public

infixr 9 _o'_
_o'_ : (B -> C) -> (A -> B) -> (A -> C)
f o' g = f o g

case_of_ : {A : Set i} {B : Set j} -> A -> (A -> B) -> B
case a of f = f a

caseOf : (A -> B) -> (B -> C) -> A -> C
caseOf f g = g o f

case_returning_of_ : forall {i j} {A : Set i} (x : A) (B : A -> Set j) -> (forall x -> B x) -> B x
case x returning B of f = f x

module BaseUnit where
    open import Data.Unit using () renaming (
        ⊤ to Unit
        ; tt to unit
        ) public

module PolyUnit where
    open import Data.Unit.Polymorphic using () renaming (
        ⊤ to Unit
        ; tt to unit
        ) public

module BaseZero where
    open import Data.Empty using () renaming (
        ⊥ to FALSITY
        ; ⊥-elim to absurd
        ) public
    open import Data.Empty using () renaming (
        ⊥ to Zero
        ) public

    ¬ : Set -> Set
    ¬ A = A -> Zero

module PolyZero where
    open import Data.Empty.Polymorphic using (⊥-elim)
    open import Data.Empty.Polymorphic using () renaming (
        ⊥ to FALSITY
        -- ; ⊥-elim to absurd
        ) public
    open import Data.Empty.Polymorphic using () renaming (
        ⊥ to Zero
        ) public

    absurd : {A : Set i} -> Zero {j} -> A
    absurd {A} ()

    ¬_ : Set i -> Set i
    ¬_ {i} A = A -> Zero {i}


open import Data.Bool using (
    Bool
    ; true
    ; false
    ; if_then_else_ ) public

module BoolOp where
    open import Data.Bool using (
            Bool
            ; _xor_
        ) renaming (
            not to notBool
            ; _∧_ to _andBool_
            ; _∨_ to _orBool_ 
        ) public

    _impliesBool_ : Bool -> Bool -> Bool
    x impliesBool y = (notBool x) orBool y

    _==_ : Bool -> Bool -> Bool
    x == y = notBool (x xor y)

module BoolOpQualified where
    open BoolOp renaming (
            _==_ to _=B=_
        ) public 

open import Data.Nat using (
        zero
    ) renaming (
        ℕ to Nat
        ; suc to 1+_
    ) public

module NatOp where
    open import Data.Nat using (
            _+_
            ; _*_
            ; _^_
            ; _%_
            ; _!
        ) renaming (
            _∸_ to _-_
            ; _⊔_ to max
            ; _⊓_ to min
            ; _≡ᵇ_ to _==_
            ; _<ᵇ_ to _<_
            ; _≤ᵇ_ to _leq_
            ; _/_ to _/safe_
        ) public
    open import Data.Nat using (nonZero; NonZero) renaming (
            _%_ to _mod_
            ; _! to fac
        ) public
        
    0e = 0
    1e = 1

    _/_ : Nat -> Nat -> Nat
    x / 0 = 0
    x / (1+ y) = x /safe (1+ y) 

    _div_ = _/_

    foldNatIdx : {A : Nat -> Set i} -> A 0 -> (forall n -> A n -> A (1+ n)) -> (n : Nat) -> A n
    foldNatIdx x _ 0 = x
    foldNatIdx x f (1+ n) = f n (foldNatIdx x f n)

module NatOpQualified where
    open NatOp renaming (
            _+_ to _+n_
            ; _*_ to _*n_
            ; _^_ to _^n_
            ; _/_ to _/n_
            ; _div_ to _divn_
            ; _-_ to _-n_
            ; _==_ to _=N=_
            ; _<_ to _<n_
            ; _leq_ to _leqn_
            ; 0e to 0en
            ; 1e to 1en
        ) public 

open import Data.Integer using ()
    renaming (
        ℤ to Int
    ) public

module IntegerOp where
    open import Data.Integer using (
            -_
            ; _^_
            ; _*_
            ; _+_
            ; _-_
        ) renaming (
            ∣_∣ to abs
            ; _≤ᵇ_ to _<=_
            ; _⊔_ to max
            ; _⊓_ to min
        ) public

module IntegerOpQualified where
    open IntegerOp using () renaming (
            -_ to -I_
            ; _^_ to _^I_
            ; _*_ to _*I_
            ; _+_ to _+I_
            ; _-_ to _-I_
            ; _<=_ to _<=I_
            ; abs to absI
            ; min to minI
            ; max to maxI
        ) public

open import Data.Char using (
        Char
    ) public

module CharOp where
    open import Data.Char using (_==_) renaming (
            toℕ to charToNat
            ; fromℕ to charFromNat
        ) public
    open NatOpQualified
    _<_ : Char -> Char -> Bool
    x < y = (charToNat x) <n (charToNat y)

module CharOpQualified where
    open CharOp renaming (
            _==_ to _=C=_
            ; _<_ to _<c_
        ) public 

open import Data.Float using (Float) public

module FloatOp where
    open import Data.Float renaming (
            _<ᵇ_ to _<_
            ; _≡ᵇ_ to _==_
            ; _**_ to _^_
            ; _÷_ to _/_
            ; fromℕ to fromNat
            ; fromℤ to fromInt
        ) public
    0e = 0.0
    1e = 1.0

module FloatOpQualified where
    open FloatOp renaming (
            _+_ to _+f_
            ; _*_ to _*f_
            ; _-_ to _-f_
            ; _/_ to _/f_
            ; _<_ to _<f_
            ; _^_ to _^f_
            ; _==_ to _=F=_
            ; 0e to 0ef
            ; 1e to 1ef
            ; fromNat to natToFloat
            ; fromInt to intToFloat
        ) public


module BaseFin where
    open import Data.Fin using (
            Fin
        ) renaming (
            #_ to finFromNat_
            ; fromℕ to maxFinFromNat
            ; toℕ to finToNat
            ; zero to f0
            ; suc to f1+_
            ; fold to foldFin
            ; fold′ to foldFin'
            ; inject₁ to injectFin1
        ) public

module PolyFin where
    open import Relation.Nullary.Decidable.Core
    private variable n : Nat
    module BF = BaseFin
    open BF using () renaming (f0 to f0'; f1+_ to f1+'_) public
    
    Fin : Nat -> Set i
    Fin {i} n = LiftL i (BF.Fin n)

    toBaseFin : Fin {i} n -> BF.Fin n
    toBaseFin (liftL fin) = fin

    fromBaseFin : BF.Fin n -> Fin {i} n
    fromBaseFin = liftL


    infix 10 finFromNat_
    finFromNat_ : (m : Nat) {n : Nat}
      {m<n : True (m Data.Nat.<? n)} ->
      Fin {i} n
    finFromNat_ m {n} {m<n}  = liftL (BF.finFromNat_ m {n} {m<n})
    
    
    maxFinFromNat : (n : Nat) -> Fin {i} (1+ n) 
    maxFinFromNat = fromBaseFin o BF.maxFinFromNat

    finToNat : Fin {i} n -> Nat
    finToNat      = BF.finToNat o toBaseFin

    -- patterns do not work well in the suc case. n - value needs to be lift-wrapped as well...
    -- pattern f0 = (liftL BF.f0) 
    -- pattern f1+_ n = (liftL (BF.f1+_ n))

    f0 : Fin {i} (1+ n)
    f0 = (liftL BF.f0) 

    f1+_ : Fin {i} n -> Fin {i} (1+ n)
    f1+_ (liftL fin) = fromBaseFin (BF.f1+_ fin)
    
    foldFin : (T : Nat -> Set j) {m : Nat} ->
      ({n : Nat} -> T n -> T (1+ n)) ->
      ({n : Nat} -> T (1+ n)) -> Fin {i} m -> T m
    foldFin T {m} f1 x (liftL fin) = BF.foldFin T {m} f1 x fin

    injectFin1 : Fin {i} n -> Fin {i} (1+ n)
    injectFin1 = fromBaseFin o BF.injectFin1 o toBaseFin

    foldFin' : {n : Nat} (T : Fin {k} (1+ n) -> Set j) ->
      ((i : Fin {k} n) -> T (injectFin1 i) -> T (f1+ i)) ->
      T f0 -> (i : Fin {k} (1+ n)) -> T i
    foldFin' T f1 x (liftL fin) = BF.foldFin' (T o fromBaseFin) (f1 o fromBaseFin) x fin

open import Data.List using (
        List
        ; []
    ) renaming (
        _∷_ to _::_
    ) public

module VecIndexed where
    open import Data.Vec using (
            Vec
            ; []
        ) renaming (
            _∷_ to _::_
        ) public


module ListOp where
    open import Data.List using (
              [_]
            ; map
            ; foldr
            ; head
            ; tail
            ; uncons
            ; concat
            ; concatMap
            ; catMaybes
            ; take
            ; drop
            ; length
            ; zip
            ; zipWith
            ; unzipWith
            ; replicate
            ; reverse
            ; any
            ; all
            ; and
            ; or
            ; null
            ; _++_ -- should be done via Monoid instance
        ) renaming (
            filterᵇ to filter
            ; findᵇ to find
            ; takeWhileᵇ to takeWhile
            ; dropWhileᵇ to dropWhile
            ; fromMaybe to maybeToList
        ) public

    guard : Bool -> List BaseUnit.Unit
    guard true = [ BaseUnit.unit ]
    guard false = []


-- module FinOp where

--     finList : {n : Nat} -> (Fin n -> A) -> List A
--     finList {A} {n} f = foldFin' (\_ -> List A) (\i -> f i ::_) [] (maxFinFromNat n)

module ListOpQualified where
    open ListOp renaming (
            _++_ to _++l_
        ) public

open import Data.String using (
        String
    ) public 

module StringOp where
    open import Data.String using (
            _==_
            ; _++_ -- should be done via Monoid instance
        ) renaming (
            toList to stringToList
            ; fromList to stringFromList
        ) public 
    
    open CharOpQualified
    open BoolOp
    
    _<_ : String -> String -> Bool
    a < b = temp (stringToList a) (stringToList b)
        where
            temp : List Char -> List Char -> Bool
            temp (x :: xs) (y :: ys) = 
                (notBool (y <c x)) andBool 
                (x <c y orBool (temp xs ys))
            temp _ (_ :: _) = true
            temp (_ :: _) [] = false
            temp [] [] = false

module StringOpQualified where
    open StringOp renaming (
            _==_ to _=S=_
            ; _++_ to _++s_
            ; _<_ to _<s_
        ) public

open import Data.Product using (
        curry
        ; uncurry
        ; _,_
    ) renaming (
        Σ to Sigma
        ; proj₁ to fst
        ; proj₂ to snd
        ; _×_ to _-x-_
        ; map₁ to mapFst
        ; map₂ to mapSnd
        ; dmap to mapTup
    ) public
open import Data.Product using () renaming (
        _×_ to _and_
    ) public

curry' : ((A -x- B) -> C) -> A -> B -> C
curry' = curry

uncurry' : (A -> B -> C) -> (A -x- B) -> C
uncurry' = uncurry


module ExistsSyntax where
    infix 2 exists
    exists = Sigma
    syntax exists A (\ a -> B) = exists[ a of A ] B
    
    infix 2 exists'
    exists' : forall {i j} -> {A : Set i} -> 
        (A -> Set j) ->
        Set (i ~U~ j)
    exists' {A = A} = Sigma A
    syntax exists' (\ a -> B) = exists[ a ] B


module VecOp where
    open VecIndexed
    open import Data.Vec using (
              [_]
            ; length
            ; head
            ; tail
            ; iterate   
            ; insertAt
            ; removeAt
            ; map
            ; _++_
            ; concat
            ; zipWith
            ; unzipWith
            ; zip
            ; unzip
            ; foldr
            ; foldl
            ; take
            ; drop
            ; toList
            ; fromList
        ) renaming (
              lookup to _!!_
            ; updateAt to _!!_:=_   
            ; _⊛_ to _applyPointwise_
            ; foldr₁ to foldr1
            ; foldl₁ to foldl1
        ) public

    open PolyUnit
    private
        variable
            n : Nat

    nTup : Nat -> Set i -> Set i
    nTup 0 _ = Unit
    nTup 1 A = A
    nTup (1+ n) A = A -x- nTup n A

    vecToTup : Vec A n -> nTup n A
    vecToTup [] = unit
    vecToTup (x :: []) = x
    vecToTup (x :: y :: xs) = x , vecToTup (y :: xs)

open import Data.Sum using () renaming (
          _⊎_ to _or_
        ; inj₁ to left
        ; inj₂ to right
        ; map to mapSum
        ; map₁ to mapLeft
        ; map₂ to mapRight
        ; [_,_] to fromSum
        ; fromInj₁ to fromLeft
        ; fromInj₂ to fromRight
    ) public
open import Data.Sum using () renaming (
          _⊎_ to _-+-_
    ) public

open import Data.Maybe using (
      Maybe
    ; just
    ; nothing
    ; fromMaybe
    ; is-just
    ; is-nothing
    ; maybe
    ) renaming (
        map to mapMaybe
    ) public

joinMaybe : Maybe (Maybe A) -> Maybe A
joinMaybe (just m) = m
joinMaybe nothing  = nothing

module PropositionalEq where
    open import Relation.Binary.PropositionalEquality.Core renaming (_≡_ to _===_; _≢_ to _=/=_) public

module State where
    open import Effect.Monad.State using (
            State
            ; runState
            ; evalState
            ; execState
        ) public

    module _ {S : Set l} where
        open import Effect.Monad.State using (
                monadState
            ) renaming (
                RawMonadState to MonadState
            )
        open MonadState (monadState {S = S}) public


Morphism : Set l -> Set l' -> Set (l ~U~ l')
Morphism A B = A -> B

module Functors where
    open import Effect.Functor using () renaming (RawFunctor to Functor) public

    module IdentityFunctor {l} where
        private 
            functor : Functor {l} id
            Functor._<$>_ functor = _$_
        open Functor functor public

    module ConstantFunctor {l} {A : Set l} where
        private
            functor : Functor {l} (const A)
            Functor._<$>_ functor = flip const
        open Functor functor public

    module FunctionFunctor {l l'} {A : Set l} where
        private
            functor : Functor (Morphism {l' = l'} A)
            Functor._<$>_ functor fbc fab = fbc o fab

        open Functor functor public

    module MaybeFunctor {l} where
        open import Data.Maybe.Effectful
        open Functor (functor {l}) public

    module ListFunctor {l} where
        open import Data.List.Effectful
        open Functor (functor {l}) public

    module StateFunctor {S : Set l} where
        open import Effect.Monad.State using (functor)
        open Functor (functor {S = S}) public

    module SumLeftFunctor (A : Set l) {l'} where
        open import Data.Sum.Effectful.Left A l' using (functor)
        open Functor (functor) public

    module SumRightFunctor (B : Set l) {l'} where
        open import Data.Sum.Effectful.Right l' B using (functor)
        open Functor (functor) public

module Applicatives where
    open import Effect.Applicative using () renaming (RawApplicative to Applicative) public

    module IdentityApplicative {l} where
        private
            applicative : Applicative {l} id
            Applicative.rawFunctor applicative = record {Functors.IdentityFunctor}
            Applicative.pure applicative = id
            Applicative._<*>_ applicative = _$_
        open Applicative applicative public

    module FunctionApplicative {l l'} {A : Set l} where
        private
            applicative : Applicative (Morphism {l' = l'} A)
            Applicative.rawFunctor applicative = record {Functors.FunctionFunctor}
            Applicative.pure applicative = const
            Applicative._<*>_ applicative ff fa a' = (ff a') (fa a')
        
        open Applicative applicative public

    module MaybeApplicative {l} where
        open import Data.Maybe.Effectful using (applicative)
        open Applicative (applicative {l}) public
    
    module ListApplicative {l} where
        open import Data.List.Effectful using (applicative)
        open Applicative (applicative {l}) public
    
    module ListZipApplicative {l} where
        open ListOp
        private
            applicative : Applicative {l} List
            Applicative.rawFunctor applicative = record {Functors.ListFunctor}
            Applicative.pure applicative = [_] -- replicate 1000 a -- Problem: returning just one element for pure in the zip context means that only one element ever exists, and applying a function in the applicative is not the same as an fmap. DO NOT USE IDIOM BRACKETS IN THIS CASE!
            Applicative._<*>_ applicative la a = zipWith _$_ la a
        open Applicative applicative public

    module StateApplicative {S : Set l} where
        open import Effect.Monad.State using (applicative)
        open Applicative (applicative {S = S}) public

    module SumLeftApplicative (A : Set l) {l'} where
        open import Data.Sum.Effectful.Left A l' using (applicative)
        open Applicative (applicative) public

    module SumRightApplicative (B : Set l) {l'} where
        open import Data.Sum.Effectful.Right l' B using (applicative)
        open Applicative (applicative) public

module Monads where
    open import Effect.Monad using () renaming (RawMonad to Monad) public

    module MonadAddOp {M : Set i -> Set j} (mon : Monad M) where
        open Monad mon
        _<<*_ : M A -> (A -> M B) -> M A
        ma <<* fmb = do
            a <- ma
            fmb a
            return a

    module MaybeMonad {l} where
        open import Data.Maybe.Effectful using (monad)
        open Monad (monad {l}) public
    
    module ListMonad {l} where
        open import Data.List.Effectful using () renaming (monad to listMonad) public
        open Monad (listMonad {l}) public
    
    module StateMonad {S : Set l} where
        open import Effect.Monad.State using (monad)
        open Monad (monad {S = S}) public

    module StateTMonad 
        {S : Set l} 
        {M : Set l -> Set l'} 
        {{mon : Monad M}}
        where
        open import Effect.Monad.State.Transformer using (monad)
        open Monad (monad {S = S} mon) public

    module SumLeftMonad (A : Set l) {l'} where
        open import Data.Sum.Effectful.Left A l' using (monad)
        open Monad (monad) public

    module SumRightMonad (B : Set l) {l'} where
        open import Data.Sum.Effectful.Right l' B using (monad)
        open Monad (monad) public

module Alternatives where
    open import Effect.Applicative using () 
        renaming (RawAlternative to Alternative) public

    module ListAlternative {i} where
        open import Data.List.Effectful public using () renaming
            (alternative to listAlternative)
        open Alternative {i} listAlternative public

module MonadPluses where
    open import Effect.Monad using () 
        renaming (RawMonadPlus to MonadPlus) public

    module MonadPlusAddOp {M : Set i -> Set j} (mp : MonadPlus M) where
        open MonadPlus mp
        open Alternatives
        open Alternative rawAlternative using (guard)
        open Monads.MonadAddOp (rawMonad)
        
        _such-that_ : M A -> (A -> Bool) -> M A
        ma such-that f = ma <<* (guard o f)

    module ListMonadPlus {i} where
        open import Data.List.Effectful public using () renaming
            (monadPlus to listMonadPlus)
        open MonadPlus {i} listMonadPlus public
                

module StateT where
    open import Effect.Monad.State.Transformer using (
        StateT
        ; mkStateT
        ; runStateT
        ; evalStateT
        ; execStateT
        ) public
    open Monads

    module _ 
        {S : Set l} 
        {M : Set l -> Set l'} 
        {{mon : Monad M}}
        where
        open import Effect.Monad.State.Transformer using (
                monadState
            ) renaming (
                RawMonadState to MonadState
            )
        open MonadState (monadState {S = S} mon) public


module MonadTransformers where
    open import Effect.Monad using () renaming (RawMonadTd to MonadT) public

    open Monads

    module StateTMonadT 
        {S : Set l} 
        {M : Set l -> Set l'} 
        {{mon : Monad M}}
        where
        open import Effect.Monad.State.Transformer using (monadT)
        open MonadT (monadT {S = S} mon) public

    module SumLeftMonadT 
        (A : Set l) {l'}
        {M : Set (l ~U~ l') -> Set (l ~U~ l')} 
        {{mon : Monad M}} where
        open import Data.Sum.Effectful.Left.Transformer A l' using (monadT)
        open MonadT (monadT mon) public

    module SumRightMonadT 
        (B : Set l) {l'}
        {M : Set (l ~U~ l') -> Set (l ~U~ l')} 
        {{mon : Monad M}} where
        open import Data.Sum.Effectful.Right.Transformer l' B using (monadT)
        open MonadT (monadT mon) public

module IndexedMonads where
    open import Effect.Monad.Indexed using () renaming
        ( RawIMonad to IMonad
        ; RawIMonadT to IMonadT
        ; RawIMonadPlus to IMonadPlus ) public

module Typeclasses where
    record Eq (A : Set l) : Set l where
        infix 100 _==_
        field
            _==_ : A -> A -> Bool

        _/=_ : A -> A -> Bool
        a /= b = notBool (a == b)
            where open BoolOp using (notBool)

    record Monoid (A : Set l) : Set l where
        field
            empty : A
            _++_ : A -> A -> A

    record Ord (A : Set l) : Set l where
        infix 30 _<_
        infix 30 _<=_
        infix 30 _>_
        infix 30 _>=_
        field
            overlap {{eq}} : Eq A
            _<_ : A -> A -> Bool

        open Eq eq public
        open BoolOpQualified

        _<=_ : A -> A -> Bool
        x <= y = x < y orBool x == y

        _>_ : A -> A -> Bool
        x > y = y < x

        _>=_ : A -> A -> Bool
        x >= y = x > y orBool x == y

    record Num (A : Set l) : Set l where
        infixr 9 _+_
        infixr 10 _-_
        infixr 11 _*_
        infixr 12 _/_
        field
            0e : A
            1e : A
            _+_ : A -> A -> A
            _-_ : A -> A -> A
            _*_ : A -> A -> A
            _/_ : A -> A -> A

    module _ where
        open Eq
        open BoolOpQualified
        open NatOpQualified
        open FloatOpQualified
        open CharOpQualified
        open StringOpQualified

        BoolEq : Eq Bool
        _==_ BoolEq = _=B=_

        NatEq : Eq Nat 
        _==_ NatEq = _=N=_

        FloatEq : Eq Float
        _==_ FloatEq = _=F=_

        CharEq : Eq Char
        _==_ CharEq = _=C=_

        StringEq : Eq String
        _==_ StringEq = _=S=_ 

        -- ListEq : {{eq : Eq A}} -> Eq (List A)
        -- _==_ ListEq [] [] = true
        -- _==_ (ListEq {{eq}}) (x :: xs) (y :: ys) = 
        --     (_==_ eq x y) andBool _==_ ListEq xs ys
        -- _==_ ListEq _ _ = false

    module _ where
        open Monoid

        open ListOpQualified
        open StringOpQualified

        ListMonoid : Monoid (List A)
        empty ListMonoid = []
        _++_ ListMonoid = _++l_

        StringMonoid : Monoid String
        empty StringMonoid = ""
        _++_ StringMonoid = _++s_

    module _ where
        open Ord
        private
            instance
                natEq = NatEq
                floatEq = FloatEq
                charEq = CharEq
                stringEq = StringEq
        
        NatOrd : Ord Nat
        NatOrd = record {NatOp}

        FloatOrd : Ord Float
        FloatOrd = record {FloatOp}

        CharOrd : Ord Char
        CharOrd = record {CharOp}

        StringOrd : Ord String
        StringOrd = record {StringOp}

    module _ where
        NatNum : Num Nat
        NatNum = record {NatOp}

        FloatNum : Num Float
        FloatNum = record {FloatOp}

    module Instances where
        open Eq {{...}}
        open Monoid {{...}}
        open Ord {{...}}

        instance
            boolEq = BoolEq
            natEq = NatEq
            floatEq = FloatEq
            charEq = CharEq
            stringEq = StringEq
            -- listEq = ListEq

            listMonoid = ListMonoid
            stringMonoid = StringMonoid

            natOrd = NatOrd
            floatOrd = FloatOrd
            charOrd = CharOrd
            stringOrd = StringOrd

            natNum = NatNum
            floatNum = FloatNum

