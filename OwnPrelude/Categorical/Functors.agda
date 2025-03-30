{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.Functors where

open import ASCIIPrelude.ASCIIPrelude
open import OwnPrelude.Equality
open PolyUnit

private
    variable
        h i j k k' l i' j' c : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j

record RawFunctor (F : Set i -> Set j) : Set (lsuc i ~U~ j) where
    infixl 5 _<$>_
    field
        _<$>_ : (A -> B) -> F A -> F B
    
    fmap = _<$>_

    void : F A -> F Unit
    void = fmap (const unit)

module _ {F : Set i -> Set j} where
    record IsFunctor (rawFunctor : RawFunctor F) : Set (lsuc i ~U~ j) where
        open RawFunctor rawFunctor
        field
            fmap-id : fmap id === (id :T: (F A -> F A))
            fmap-comp : forall {f : B -> C} {g : A -> B} ->
                fmap (f o g) === (fmap f) o (fmap g)

record Functor (F : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawFunctor : RawFunctor F
        isFunctor  : IsFunctor  rawFunctor
    open RawFunctor rawFunctor public
    open IsFunctor  isFunctor  public


module _ {F : Set j -> Set k} {G : Set i -> Set j} (funcF : Functor F) (funcG : Functor G) where
    module F = Functor funcF
    module G = Functor funcG
        
    FunctorComposition : Functor (F o G)
    FunctorComposition .Functor.rawFunctor .RawFunctor._<$>_ = F.fmap o G.fmap
    FunctorComposition .Functor.isFunctor .IsFunctor.fmap-id = extens \x -> 
        (F.fmap o G.fmap) id x =< G.fmap-id || (\h -> F.fmap h x) >
        F.fmap id x            =< F.fmap-id || (_$ x) >
        x                      qed
    FunctorComposition .Functor.isFunctor .IsFunctor.fmap-comp {f} {g} = extens \x -> 
        (F.fmap o G.fmap) (f o g) x =< G.fmap-comp || (\h -> F.fmap h x) >
        (F.fmap (G.fmap f o G.fmap g) x) =< F.fmap-comp || (_$ x) >
        (((F.fmap o G.fmap) f) o ((F.fmap o G.fmap) g)) x qed