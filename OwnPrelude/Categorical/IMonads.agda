{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.IMonads where

open import ASCIIPrelude.ASCIIPrelude hiding (_o_) renaming (_o'_ to _o_)
open import OwnPrelude.ASCIIPreludeProofs
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.IApplicatives
open import OwnPrelude.Categorical.Functors

private
    variable
        il jl ul : Level
        n n' : Nat
        A B C X Y Z L S : Set il
        F G : Set il -> Set jl
        x y z m : A
        f g : A -> B

module _ {I : Set ul} where 
    private
        variable
            h i j k : I

    record RawIMonad (M : I -> I -> Set il -> Set jl) : Set (lsuc il ~U~ jl ~U~ ul) where
        infixl 4 _>>=_ _>>_ _>=>_ 
        infixr 4 _=<<_ _<=<_
        field
            return : A -> M i i A
            _>>=_  : M i j A -> (A -> M j k B) -> M i k B

        rawIApplicative : RawIApplicative M
        RawIApplicative.pure rawIApplicative = return
        RawIApplicative._<*>_ rawIApplicative mf ma = do 
            f <- mf 
            a <- ma 
            return (f a)

        open RawIApplicative rawIApplicative public

        _>>_ : M i j A -> M j k B -> M i k B
        ma >> mb = ma >>= const mb

        _=<<_ : (A -> M j k B) -> M i j A -> M i k B
        _=<<_ = flip _>>=_

        _>=>_ : (A -> M i j B) -> (B -> M j k C) -> (A -> M i k C)
        (amb >=> bmc) = \a -> amb a >>= bmc

        _<=<_ : (B -> M j k C) -> (A -> M i j B) -> (A -> M i k C)
        _<=<_ = flip _>=>_

        _<<*_ : M i j A -> (A -> M j k B) -> M i k A
        ma <<* f = ma >>= \a -> f a >> return a

        _*>>_ : (A -> M j k B) -> M i j A -> M i k A
        _*>>_ = flip _<<*_

    record IsIMonad {M : I -> I -> Set il -> Set jl}
        (rawIMonad : RawIMonad M) : Set (lsuc il ~U~ jl ~U~ ul) where
        open RawIMonad rawIMonad
        field
            left-identity  : return x >>= f === f x
            right-identity : m >>= return === m
            associative    : (m >>= f) >>= g === m >>= (f >=> g)

        open IsIApplicative

        isIApplicative : IsIApplicative rawIApplicative
        -- pure id <*> v === v
        identity     isIApplicative {v} = 
            pure id <*> v                                    =<> 
            return id <*> v                                  =<>
            (return id >>= \ f -> v >>= \ a -> return (f a)) =< left-identity >
            (v >>= \a -> return (id a))                      =<>
            (v >>= return o id)                              =< o-right-id || v >>=_ >
            v >>= return                                     =< right-identity >
            v                                                qed
        -- pure _o_ <*> u <*> v <*> w === u <*> (v <*> w)
        composition  isIApplicative {u} {v} {w} = 
            pure _o_ <*> u <*> v <*> w                                                                =<> 
            return _o_ <*> u <*> v <*> w                                                              =<> 
            (return _o_ >>= \f -> u >>= \uf -> return (f uf)) <*> v <*> w                             =< left-identity || (\h -> h <*> v <*> w) > 
            (u >>= \uf -> return (uf o_)) <*> v <*> w                                                 =<>
            ((u >>= \uf -> return (uf o_)) >>= \ufo -> v >>= \vf -> return (ufo vf)) <*> w            =< associative || _<*> w >
            (u >>= \uf -> return (uf o_) >>= \ufo -> v >>= \vf -> return (ufo vf)) <*> w              =< (\uf -> left-identity {x = uf o_}) |f (\h -> (u >>= \uf -> h uf) <*> w) > 
            (u >>= \uf -> v >>= \vf -> return (uf o vf)) <*> w                                        =<>
            ((u >>= \uf -> v >>= \vf -> return (uf o vf)) >>= \ufovf -> w >>= \a -> return (ufovf a)) =< associative >
            (u >>= \uf -> (v >>= \vf -> return (uf o vf)) >>= \ufovf -> w >>= \a -> return (ufovf a)) =< ((\uf -> associative {f = \vf -> return (uf o vf)}) |f (\h -> u >>= \uf -> h uf)) >
            (u >>= \uf -> v >>= \vf -> return (uf o vf) >>= \ufovf -> w >>= \a -> return (ufovf a))   =< ((\ uf vf -> left-identity {x = uf o vf}) |f2 (\h -> u >>= \uf -> v >>= \vf -> h uf vf)) >
            (u >>= \uf -> v >>= \vf -> w >>= \a -> return ((uf o vf) a))                              =<>
            (u >>= \uf -> v >>= \vf -> w >>= \a -> return (uf (vf a)))                                =< ((\ uf vf a -> sym (left-identity {x = vf a} {f = \vw -> return (uf vw)})) |f3 (\h -> u >>= \uf -> v >>= \vf -> w >>= \a -> h uf vf a)) >
            (u >>= \uf -> v >>= \vf -> w >>= \a -> return (vf a) >>= \vw -> return (uf vw))           =< (\ uf vf -> sym (associative {f = \a -> return (vf a)} {g = \vw -> return (uf vw)})) |f2 (\h -> u >>= \uf -> v >>= \vf -> h uf vf) >
            (u >>= \uf -> v >>= \vf -> (w >>= \a -> return (vf a)) >>= \vw -> return (uf vw))         =< (\uf -> sym (associative {g = \vw -> return (uf vw)})) |f (\h -> u >>= \uf -> h uf) >
            (u >>= \uf -> (v >>= \vf -> w >>= \a -> return (vf a)) >>= \vw -> return (uf vw))         =<>
            (u >>= \uf -> (v <*> w) >>= \vw -> return (uf vw))                                        =<>
            u <*> (v <*> w)                                                                           qed
        -- pure f <*> pure x === pure (f x)
        homomorphism isIApplicative {f} {x} = 
            pure f <*> pure x                                    =<>
            (return f >>= \f -> return x >>= \x -> return (f x)) =< left-identity >
            (return x >>= \x -> return (f x))                    =< left-identity >
            return (f x)                                         =<>
            pure (f x)                                           qed
        -- u <*> pure y === pure (_$ y) <*> u
        interchange  isIApplicative {u} {y} = 
            u <*> pure y =<>
            (u >>= \uf -> return y >>= \y -> return (uf y))          =< (\uf -> left-identity {f = \y -> return (uf y)}) |f (\h -> u >>= \uf -> h uf) >
            (u >>= \uf -> return (uf y))                             =<>
            (u >>= \uf -> return (uf $ y))                           =< sym left-identity >
            (return (_$ y) >>= \ _$y -> u >>= \uf -> return (uf $y)) =<>
            pure (_$ y) <*> u                                        qed

        open IsIApplicative isIApplicative public

    record IMonad (M : I -> I -> Set il -> Set jl) : Set (lsuc il ~U~ jl ~U~ ul) where
        field
            rawIMonad : RawIMonad M
            isIMonad  : IsIMonad rawIMonad
        open RawIMonad rawIMonad public
        open IsIMonad  isIMonad  public

        iApplicative : IApplicative M
        IApplicative.rawIApplicative iApplicative = rawIApplicative
        IApplicative.isIApplicative  iApplicative = isIApplicative

        functor : Functor (M i j)
        functor = IApplicative.functor iApplicative