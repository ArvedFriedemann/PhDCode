{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.Applicatives where

open import ASCIIPrelude.ASCIIPrelude hiding (_o_) renaming (_o'_ to _o_)
open PolyUnit
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Functors

private
    variable
        h i j k k' l i' j' c : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j

record RawApplicative (F : Set i -> Set j) : Set (lsuc i ~U~ j) where
    infixl 5 _<*>_
    field
        pure  : A -> F A
        _<*>_ : F (A -> B) -> F A -> F B

    rawFunctor : RawFunctor F
    RawFunctor._<$>_ rawFunctor f v = pure f <*> v

    open RawFunctor rawFunctor public

    when : Bool -> F A -> F Unit
    when true m = void m
    when false _ = pure unit

    when' : Bool -> F Unit -> F Unit
    when' true m = m
    when' false _ = pure unit

    unless : Bool -> F A -> F Unit
    unless false m = void m
    unless true _ = pure unit

    unless' : Bool -> F Unit -> F Unit
    unless' false m = m
    unless' true _ = pure unit

module _ {F : Set i -> Set j} where
    private variable
        u v w : F A
        f : A -> B
        x y : X
    
    record IsApplicative (rawApplicative : RawApplicative F) : Set (lsuc i ~U~ j) where
        open RawApplicative rawApplicative
        field
            identity     : pure id <*> v === v
            composition  : {u : F (B -> C)} {v : F (A -> B)} {w : F A}-> 
                pure _o_ <*> u <*> v <*> w === u <*> (v <*> w)
            homomorphism : pure f <*> pure x === pure (f x)
            interchange  : u <*> pure y === pure (_$ y) <*> u

        open IsFunctor

        isFunctor : IsFunctor rawFunctor
        fmap-id isFunctor = extens \v -> 
            fmap id v     =<>
            pure id <*> v =< identity >
            id v          qed
        fmap-comp isFunctor {f} {g} = extens \v -> 
            fmap (f o g) v                       =<>
            pure (f o g) <*> v                   =< sym homomorphism || _<*> v >
            pure (f o_) <*> pure g <*> v         =< sym homomorphism || (\z -> z <*> pure g <*> v) >
            pure _o_ <*> pure f <*> pure g <*> v =< composition >
            pure f <*> (pure g <*> v)            =<>
            ((pure f <*>_) o (pure g <*>_)) v    =<>
            (fmap f o fmap g) v                  qed

        open IsFunctor isFunctor public

record Applicative (F : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawApplicative : RawApplicative F
        isApplicative  : IsApplicative  rawApplicative
    open RawApplicative rawApplicative public
    open IsApplicative  isApplicative  public

    functor : Functor F
    Functor.rawFunctor functor = rawFunctor
    Functor.isFunctor  functor = isFunctor