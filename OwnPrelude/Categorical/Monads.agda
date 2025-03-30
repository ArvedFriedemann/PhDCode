{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.Monads where

open import ASCIIPrelude.ASCIIPrelude hiding (_o_) renaming (_o'_ to _o_)
open import OwnPrelude.ASCIIPreludeProofs
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Functors

private
    variable
        i j k k' l i' j' c : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        x y z m f g h a b m' ma mb : A

record RawMonad (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    infixl 4 _>>=_ _>>_ _>=>_ 
    infixr 4 _=<<_ _<=<_
    field
        return : A -> M A
        _>>=_  : M A -> (A -> M B) -> M B

    rawApplicative : RawApplicative M
    RawApplicative.pure rawApplicative = return
    RawApplicative._<*>_ rawApplicative mf ma = do 
        f <- mf 
        a <- ma 
        return (f a)

    open RawApplicative rawApplicative public

    _>>_ : M A -> M B -> M B
    ma >> mb = ma >>= const mb

    _=<<_ : (A -> M B) -> M A -> M B
    _=<<_ = flip _>>=_

    _>=>_ : (A -> M B) -> (B -> M C) -> (A -> M C)
    (amb >=> bmc) = \a -> amb a >>= bmc

    _<=<_ : (B -> M C) -> (A -> M B) -> (A -> M C)
    _<=<_ = flip _>=>_

    _<<*_ : M A -> (A -> M B) -> M A
    ma <<* f = ma >>= \a -> f a >> return a

    _*>>_ : (A -> M B) -> M A -> M A
    _*>>_ = flip _<<*_

record IsMonad {M : Set i -> Set j}
    (rawMonad : RawMonad M) : Set (lsuc i ~U~ j) where
    open RawMonad rawMonad
    field
        left-identity  : return x >>= f === f x
        right-identity : m >>= return === m
        associative    : (m >>= f) >>= g === m >>= (f >=> g)

    open IsApplicative

    isApplicative : IsApplicative rawApplicative
    -- pure id <*> v === v
    identity     isApplicative {v} = 
        pure id <*> v                                    =<> 
        return id <*> v                                  =<>
        (return id >>= \ f -> v >>= \ a -> return (f a)) =< left-identity >
        (v >>= \a -> return (id a))                      =<>
        (v >>= return o id)                              =< o-right-id || v >>=_ >
        v >>= return                                     =< right-identity >
        v                                                qed
    -- pure _o_ <*> u <*> v <*> w === u <*> (v <*> w)
    composition  isApplicative {u} {v} {w} = 
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
    homomorphism isApplicative {f} {x} = 
        pure f <*> pure x                                    =<>
        (return f >>= \f -> return x >>= \x -> return (f x)) =< left-identity >
        (return x >>= \x -> return (f x))                    =< left-identity >
        return (f x)                                         =<>
        pure (f x)                                           qed
    -- u <*> pure y === pure (_$ y) <*> u
    interchange  isApplicative {u} {y} = 
        u <*> pure y =<>
        (u >>= \uf -> return y >>= \y -> return (uf y))          =< (\uf -> left-identity {f = \y -> return (uf y)}) |f (\h -> u >>= \uf -> h uf) >
        (u >>= \uf -> return (uf y))                             =<>
        (u >>= \uf -> return (uf $ y))                           =< sym left-identity >
        (return (_$ y) >>= \ _$y -> u >>= \uf -> return (uf $y)) =<>
        pure (_$ y) <*> u                                        qed

    open IsApplicative isApplicative public

    fmap-simplified : fmap f === _>>= return o f
    fmap-simplified {f} = 
        fmap f                                        =<>
        (\m -> return f >>= \f' -> m >>= return o f') =< (\_ -> left-identity) |f id >
        _>>= return o f                               qed
    
    fmap-return : fmap f o return === return o f
    fmap-return {f} = 
        fmap f o return            =< fmap-simplified || _o return >
        (_>>= return o f) o return =< extens (\_ -> left-identity) >
        return o f                 qed

    module _ {A B C : Set i} {f : A -> B} {g : B -> M C} where
        fmap-bind : (_>>= g) o fmap f === _>>= (g o f)
        fmap-bind =
            (_>>= g) o fmap f =< fmap-simplified || (_>>= g) o_ >
            (_>>= g) o (_>>= return o f) =< (extens \_ -> associative) >
            (_>>= (return o f >=> g)) =< (\_ -> left-identity) |f (\h -> _>>= h) >
            _>>= (g o f) qed

    fmap-kleisli-switch : fmap f o (g >=> h) === g >=> fmap f o h
    fmap-kleisli-switch {f} {g} {h} = 
        fmap f o (g >=> h)                 =<>
        fmap f o (\x -> g x >>= h)         =<>
        (\x -> fmap f (g x >>= h))         =< fmap-simplified || (\hl -> (\x -> hl (g x >>= h))) >
        (\x -> (g x >>= h) >>= return o f) =< extens (\_ -> associative) >
        (\x -> g x >>= (h >=> return o f)) =< (\c ->  sym fmap-simplified || (_$ h c)) |f (\hl -> (\x -> g x >>= hl)) >
        g >=> fmap f o h                   qed

    binOp-simplified : (| f a b |) === (a >>= \a' -> b >>= \b' -> return (f a' b'))
    binOp-simplified {f} {a} {b} = 
        (| f a b |) =<>
        (do
            fa <- do
                f <- return f
                a' <- a
                return (f a')
            b' <- b
            return (fa b')
        ) =< left-identity || _>>= (\_ -> b >>= _) >

        (do
            fa <- do
                a' <- a
                return (f a')
            b' <- b
            return (fa b')
        ) =< associative >

        (do
            a' <- a
            fa <- return (f a')
            b' <- b
            return (fa b')
        ) =< (\_ -> left-identity) |f a >>=_ >

        (do
            a' <- a
            b' <- b
            return (f a' b')
        ) qed

record Monad (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawMonad : RawMonad M
        isMonad  : IsMonad rawMonad
    open RawMonad rawMonad public
    open IsMonad  isMonad  public
    
    applicative : Applicative M
    Applicative.rawApplicative applicative = rawApplicative
    Applicative.isApplicative applicative = isApplicative

    functor : Functor M
    functor = Applicative.functor applicative

module _ {M : Set i -> Set j} where
    record LocallyCommutativeMonad (mon : Monad M) : Set (lsuc i ~U~ j) where
        open Monad mon
        field
            commute : forall {f : A -> B -> M C} -> 
                (ma >>= \a -> mb >>= \b -> f a b) === (mb >>= \b -> ma >>= \a -> f a b)

module EndoMonad {M : Set i -> Set i} (mon : Monad M) where
    open Monad mon public

    join : (M o M) A -> M A
    join = _>>= id

    join-bind : join o fmap f === _>>= f
    join-bind {f} = 
        fmap f >=> id            =< fmap-simplified || _>=> id >
        (_>>= return o f) >=> id =< extens (\_ -> associative) >
        _>>= (return o f >=> id) =< extens (\_ -> left-identity) || flip _>>=_ >
        _>>= f                   qed

    join-fmap : fmap f o join === join o (fmap o fmap) f
    join-fmap {f} = extens \m -> 
        fmap f (join m) =<>
        fmap f (m >>= id) =< fmap-simplified || (\h -> h (m >>= id)) > 
        (m >>= id) >>= return o f =< associative > 
        m >>= (id >=> return o f) =<> 
        m >>= (_>>= return o f) =< sym fmap-simplified || m >>=_ > 
        m >>= fmap f =< sym join-bind || (_$ m) >
        (fmap o fmap) f m >>= id =<>
        (join o (fmap o fmap) f) m qed