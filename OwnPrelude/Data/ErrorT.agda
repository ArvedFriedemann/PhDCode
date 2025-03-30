{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.ErrorT where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadTs
open import OwnPrelude.Categorical.Alternatives
open import OwnPrelude.Categorical.MonadFailAlternatives
open import OwnPrelude.Categorical.MonadErrors

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G M : Set i -> Set j
        a b x y z m : A
        f g : A -> B

ErrorT : (Err : Set u) -> (M : Set (i ~U~ u) -> Set j) -> Set i -> Set j
ErrorT Err M X = M (X or Err)

module _ (Err : Set u) {M : Set (i ~U~ u) -> Set j}
    (mon : RawMonad M) where
    module _ where
        open RawMonad mon
        rawMonad : RawMonad {i} (ErrorT Err M)
        RawMonad.return rawMonad = return o left
        RawMonad._>>=_ rawMonad ma fmb = 
            ma >>= fromSum fmb (return o right)

        rawMonadErrorOver : RawMonadErrorOver rawMonad Err
        RawMonadErrorOver.throw rawMonadErrorOver = return o right
        RawMonadErrorOver.catch rawMonadErrorOver ma errma = ma >>= fromSum (return o left) errma


module _ (Err : Set u) {M : Set (i ~U~ u) -> Set j}
    (mon : Monad M) where
    open Monad mon 
        hiding (isMonad)
        renaming (rawMonad to rawMonadM)

    isMonad : IsMonad {i} (rawMonad Err rawMonadM)
    IsMonad.left-identity isMonad {x} {f} = left-identity
    IsMonad.right-identity isMonad {m} = 
        m >>= fromSum (return o left) (return o right) =< (fromSum (\_ -> refl) (\_ -> refl)) |pi m >>=_ >
        m >>= return =< right-identity >
        m qed
    IsMonad.associative isMonad {m} {f} {g} =
        (m >>= (\a -> fromSum f (return o right) a) >>= (\b -> fromSum g (return o right) b)) =< associative >
        (m >>= (\a -> fromSum f (return o right) a >>= (\b -> fromSum g (return o right) b))) =< 
            (fromSum 
                (\x -> (\_ -> refl) |pi f x >>=_) 
                (\_ -> left-identity) 
                |pi m >>=_) 
            >
        m >>= fromSum (\a -> f a >>= fromSum g (return o right)) (return o right) =<>
        m >>= fromSum (f >=> fromSum g (return o right)) (return o right) qed

    monad : Monad {i} (ErrorT Err M)
    Monad.rawMonad monad = rawMonad Err (Monad.rawMonad mon)
    Monad.isMonad monad = isMonad

    isMonadErrorOver : IsMonadErrorOver isMonad (rawMonadErrorOver Err rawMonadM)
    IsMonadErrorOver.left-absorb isMonadErrorOver = left-identity
    IsMonadErrorOver.throw-catch isMonadErrorOver {e} {f} = left-identity

    monadErrorOver : MonadErrorOver monad Err
    MonadErrorOver.rawMonadErrorOver monadErrorOver = rawMonadErrorOver Err (Monad.rawMonad mon)
    MonadErrorOver.isMonadErrorOver monadErrorOver = isMonadErrorOver

module _ (Err : Set u) {M : Set (i ~U~ u) -> Set j}
    (mon : Monad M) where

    module _ where
        open Monad mon hiding (rawMonad)

        rawMonadT : RawMonadT {i ~U~ u} M (ErrorT Err M)
        RawMonadT.rawInnerMonad rawMonadT = Monad.rawMonad mon
        RawMonadT.rawOuterMonad rawMonadT = rawMonad Err (Monad.rawMonad mon)
        RawMonadT.lift rawMonadT = fmap left

    module _ where
        open Monad mon hiding (isMonad; rawMonad)

        isMonadT : IsMonadT rawMonadT
        IsMonadT.isInnerMonad isMonadT = Monad.isMonad mon
        IsMonadT.isOuterMonad isMonadT = isMonad Err mon
        IsMonadT.lift-return isMonadT = extensPi \x -> 
            (fmap left o return) x =< homomorphism >
            return (left x) qed
        IsMonadT.lift-bind isMonadT {m} {f} = 
            left <$> (m >>= f)                                                                    =<>
            pure left <*> (m >>= f)                                                               =<>
            (return left >>= \l -> (m >>= f) >>= \r -> return (l r))                              =< left-identity >
            ((m >>= f) >>= \r -> return (left r))                                                 =< associative >
            (m >>= (\q -> f q >>= \r -> return (left r)))                                         =< (\_ -> sym left-identity) |f m >>=_ >
            (m >>= (\q -> return left >>= \l -> f q >>= \r -> return (l r)))                      =<>
            (m >>= (\q -> pure left <*> (f q)))                                                   =<>
            (m >>= (\q -> fmap left (f q)))                                                       =<>
            m >>= (fmap left o f)                                                                 =< (\_ -> sym left-identity) |f (m >>=_) >
            (m >>= \r -> return (left r) >>= fromSum (fmap left o f) (return o right))            =< sym associative >
            m >>= return o left >>= fromSum (fmap left o f) (return o right)                      =< sym left-identity >
            return left >>= (\l -> m >>= return o l >>= fromSum (fmap left o f) (return o right)) =< sym associative >
            (return left >>= \l -> m >>= return o l) >>= fromSum (fmap left o f) (return o right) =<>
            (left <$> m) >>= fromSum (fmap left o f) (return o right)                             qed

        monadT : MonadT M (ErrorT Err M)
        MonadT.rawMonadT monadT = rawMonadT
        MonadT.isMonadT  monadT = isMonadT

module _ (Err : Set u) {M : Set (i ~U~ u) -> Set j}
    (monad : Monad M)
    (mfa : MonadFailAlternativeOver monad) where

    module _ where
        open MonadT (monadT {i = i} Err monad)
        open MonadFailAlternativeOver mfa 
            hiding (rawMonoid; isMonoid; rawMonadFailAlternativeOver; isMonadFailAlternativeOver; rawAlternativeOver; isAlternativeOver)
        open Monad monad hiding (rawMonad)

        rawMonoid : {X : Set (i ~U~ u)} -> RawMonoid (ErrorT Err M X)
        RawMonoid.epsilon rawMonoid = lift empty
        RawMonoid._<>_ rawMonoid m1 m2 = m1 <|> m2

        rawAlternativeOver : RawAlternativeOver (RawMonad.rawApplicative rawOuterMonad)
        RawAlternativeOver.rawMonoid rawAlternativeOver = rawMonoid

        rawMonadFailAlternativeOver : RawMonadFailAlternativeOver (rawMonad Err (Monad.rawMonad monad))
        RawMonadFailAlternativeOver.rawAlternativeOver rawMonadFailAlternativeOver = rawAlternativeOver

        isMonoid : IsMonoid (rawMonoid {X})
        IsMonoid.left-identity isMonoid {a} = 
            fmap left empty <|> a                     =<>
            (return left >>= \_ -> empty >>= _) <|> a =< (\_ -> left-absorb) |f (\h -> (return left >>= h) <|> a) >
            (return left >>= \_ -> empty) <|> a       =< left-identity || _<|> a >
            empty <|> a                               =< left-identity-monoid >
            a                                         qed
        IsMonoid.right-identity isMonoid {a} = 
            a <|> fmap left empty                     =<>
            a <|> (return left >>= \_ -> empty >>= _) =< (\_ -> left-absorb) |f (\h -> a <|> (return left >>= h)) >
            a <|> (return left >>= \_ -> empty)       =< left-identity || a <|>_ >
            a <|> empty                               =< right-identity-monoid >
            a                                         qed
        IsMonoid.associative isMonoid = associative-monoid

        isAlternativeOver : IsAlternativeOver (Monad.applicative outerMonad) rawAlternativeOver
        IsAlternativeOver.isMonoid isAlternativeOver = isMonoid

        isMonadFailAlternativeOver : IsMonadFailAlternativeOver outerMonad rawMonadFailAlternativeOver
        IsMonadFailAlternativeOver.isAlternativeOver isMonadFailAlternativeOver = isAlternativeOver
        IsMonadFailAlternativeOver.left-absorb isMonadFailAlternativeOver {f} = 
            (lift empty) >>= fromSum f (return o right)                        =<>
            (fmap left empty) >>= fromSum f (return o right)                   =<>
            (return left >>= \l -> empty >>= _) >>= fromSum f (return o right) =< left-identity ||  _>>= _ >
            (empty >>= _) >>= fromSum f (return o right)                       =< left-absorb || _>>= _ >
            empty >>= fromSum f (return o right)                               =< left-absorb >
            empty                                                              =< sym left-identity >
            (return left >>= \_ -> empty)                                      =< (\_ -> sym left-absorb) |f return left >>=_ >
            (return left >>= \l -> empty >>= return o l)                       =<>
            lift empty                                                         qed

        monadFailAlternativeOver : MonadFailAlternativeOver outerMonad
        MonadFailAlternativeOver.rawMonadFailAlternativeOver monadFailAlternativeOver = rawMonadFailAlternativeOver
        MonadFailAlternativeOver.isMonadFailAlternativeOver  monadFailAlternativeOver = isMonadFailAlternativeOver
  