{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --without-K --cubical-compatible #-}
{-# OPTIONS --safe #-}
module ASCIIPrelude.CustomDefinitions where

open import ASCIIPrelude.ASCIIPrelude hiding (module StateT)
open MonadTransformers
open Monads
open Applicatives
open Functors

private
    variable
        h i j k l i' j' : Level
        n n' : Nat
        A B X Y S : Set i
        M F G : Set i -> Set j

module ListT where
    ListT : (M : Set i -> Set j) -> Set i -> Set j
    ListT M A = M (List A)

module MaybeT where
    MaybeT : (M : Set i -> Set j) -> Set i -> Set j
    MaybeT M A = M (Maybe A)

    module _ (func : Functor M) where
        open Functor func
        functorMaybeT : Functor (MaybeT M)
        Functor._<$>_ functorMaybeT f ma = mapMaybe f <$> ma

    module _ (mon : Monad M) where
        open Monad mon hiding (_<$>_)
        open Functor (functorMaybeT (Monad.rawFunctor mon))
        applicativeMaybeT : Applicative (MaybeT M)
        Applicative.rawFunctor applicativeMaybeT = functorMaybeT (Monad.rawFunctor mon)
        Applicative.pure applicativeMaybeT = return o just
        Applicative._<*>_ applicativeMaybeT fab ma = do
            mf <- fab
            case mf of \{
                 (just f) -> f <$> ma
                ; nothing -> return nothing
                }

    module _ (mon : Monad M) where
        open Monad mon
        monadMaybeT : Monad (MaybeT M)
        Monad.rawApplicative monadMaybeT = applicativeMaybeT mon
        Monad._>>=_ monadMaybeT ma fmb = do
            ma <- ma
            case ma of \{
                 (just a) -> fmb a
                ; nothing -> return nothing
                }

    module _ (mon : Monad M) where
        open Monad mon
        monadTMaybeT : MonadT M (MaybeT M)
        MonadT.lift monadTMaybeT = just <$>_
        MonadT.rawMonad monadTMaybeT = monadMaybeT mon

module StateT where
    StateT : Set k -> (M : Set (i ~U~ k) -> Set j) -> Set i -> Set (j ~U~ k)
    StateT S M X = S -> M (S -x- X)

    module GetAction {S : Set i} {M : Set i -> Set j} (app : Applicative M) where 
        open Applicative app
        get : StateT S M S
        get s = pure (s , s)

    module _ {S : Set k} {M : Set (i ~U~ k) -> Set j} where
        module StateActions (app : Applicative M) where
            open Applicative app
            open PolyUnit
            module _ {A : Set i} where
                getS : (S -> A) -> StateT S M A
                getS f s = pure (s , f s)

            modify : (S -> S) -> StateT S M (Unit {i})
            modify f s = pure (f s , unit)

            put : S -> StateT S M (Unit {i})
            put s _ = pure (s , unit)


        module _ (func : Functor M) where
            open Functor func renaming (_<$>_ to fmap)
            functorStateT : Functor {i} (StateT S M)
            Functor._<$>_ functorStateT f m s = fmap (mapSnd f) (m s)

        module _ (mon : Monad M) where
            open Monad mon
            applicativeStateT : Applicative {i} (StateT S M)
            Applicative.rawFunctor applicativeStateT = functorStateT (Monad.rawFunctor mon)
            Applicative.pure applicativeStateT x s = return (s , x)
            Applicative._<*>_ applicativeStateT mf ma s = do
                (s'  , f) <- mf s
                (s'' , a) <- ma s'
                return (s'' , f a)

        module _ (mon : Monad M) where
            open Monad mon
            monadStateT : Monad {i} (StateT S M)
            Monad.rawApplicative monadStateT = applicativeStateT mon
            Monad._>>=_ monadStateT ma fmb s = do
                (s' , a) <- ma s
                fmb a s'

    module _ {S : Set i} {M : Set i -> Set j} where
        module _ (mon : Monad M) where
            open Monad mon
            monadTStateT : MonadT M (StateT S M)
            MonadT.lift monadTStateT m s = (s ,_) <$> m
            MonadT.rawMonad monadTStateT = monadStateT mon