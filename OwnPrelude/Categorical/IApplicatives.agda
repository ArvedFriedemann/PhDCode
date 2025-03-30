{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.IApplicatives where

open import ASCIIPrelude.ASCIIPrelude hiding (_o_) renaming (_o'_ to _o_)
open PolyUnit
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Functors

private
    variable
        hl il jl kl kl' ll il' jl' cl ul : Level
        n n' : Nat
        A B C X Y Z L S : Set il
        F G : Set il -> Set jl

module _ {I : Set ul} where 
    private
        variable
            h i j k : I
            
    record RawIApplicative (F : I -> I -> Set il -> Set jl) : Set (lsuc il ~U~ jl ~U~ ul) where 
        infixl 5 _<*>_
        field
            pure  : A -> F i i A
            _<*>_ : F i j (A -> B) -> F j k A -> F i k B

        module _ {i j : I} where
            rawFunctor : RawFunctor (F i j)
            RawFunctor._<$>_ rawFunctor f v = pure f <*> v

            open RawFunctor rawFunctor public

        when : Bool -> F i i A -> F i i Unit
        when true m = void m
        when false _ = pure unit

        when' : Bool -> F i i Unit -> F i i Unit
        when' true m = m
        when' false _ = pure unit

        unless : Bool -> F i i A -> F i i Unit
        unless false m = void m
        unless true _ = pure unit

        unless' : Bool -> F i i Unit -> F i i Unit
        unless' false m = m
        unless' true _ = pure unit

    module _ {F : I -> I -> Set il -> Set jl} where
        private variable
            u v w : F i j A
            f : A -> B
            x y : X
        
        record IsIApplicative (rawIApplicative : RawIApplicative F) : Set (lsuc il ~U~ jl ~U~ ul) where
            open RawIApplicative rawIApplicative
            field
                identity     : pure id <*> v === v
                composition  : {u : F h i (B -> C)} {v : F i j (A -> B)} {w : F j k A}-> 
                    pure _o_ <*> u <*> v <*> w === u <*> (v <*> w)
                homomorphism : pure f <*> pure x === pure {i = i} (f x)
                interchange  : u <*> pure y === pure (_$ y) <*> u

            open IsFunctor

            module _ {i j : I} where
                isFunctor : IsFunctor (rawFunctor {i} {j})
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

    record IApplicative (F : I -> I -> Set il -> Set jl) : Set (lsuc il ~U~ jl ~U~ ul) where
        field
            rawIApplicative : RawIApplicative F
            isIApplicative  : IsIApplicative rawIApplicative
        open RawIApplicative rawIApplicative public
        open IsIApplicative  isIApplicative  public

        module _ {i j : I} where
            functor : Functor (F i j)
            Functor.rawFunctor functor = rawFunctor
            Functor.isFunctor  functor = isFunctor