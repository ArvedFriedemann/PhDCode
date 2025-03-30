{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.ListCategorical where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.ASCIIPreludeProofs
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Alternatives
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadPlus
open import OwnPrelude.Categorical.MonadFailAlternatives
open ListOp

private
    variable
        h i j k k' l i' j' : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b c x y z m : A
        f g : A -> B

module _ where
    open RawMonad

    listRawMonad : RawMonad {i} List
    return listRawMonad a = a :: []
    _>>=_ listRawMonad lsta flstb = concatMap flstb lsta

module _ {i} where
    open RawMonad {i} listRawMonad

    listMonad : Monad {i} List 
    Monad.rawMonad listMonad = listRawMonad
    -- return x >>= f === f x
    IsMonad.left-identity (Monad.isMonad listMonad) {x} {f} = concatMap-singleton {f = f} {x = x}
    -- m >>= return === m
    IsMonad.right-identity (Monad.isMonad listMonad) {m} = 
        m >>= return       =<>
        concatMap return m =< concatMap-return-id >
        m                  qed
    -- (m >>= f) >>= g === m >>= (f >=> g)
    IsMonad.associative (Monad.isMonad listMonad) {m} {f} {g} = 
        (m >>= f) >>= g                       =<>
        concatMap g (concatMap f m)           =< sym (concatMap-compose {lst = m}) >
        concatMap (concatMap g o f) m         =<>
        concatMap (\a -> concatMap g (f a)) m =<>
        concatMap (\a -> f a >>= g) m         =<>
        concatMap (f >=> g) m                 =<>
        m >>= (f >=> g) qed

listRawMonoid : RawMonoid (List A)
RawMonoid.epsilon listRawMonoid = []
RawMonoid._<>_ listRawMonoid = _++_

module _ {A : Set i} where
    open RawMonoid {i} (listRawMonoid {A = A})
    
    listMonoid : Monoid (List A)
    Monoid.rawMonoid listMonoid = listRawMonoid
    -- epsilon <> a === a
    IsMonoid.left-identity (Monoid.isMonoid listMonoid) {a} = refl
    -- a <> epsilon === a
    IsMonoid.right-identity (Monoid.isMonoid listMonoid) = []-right-id
    -- (a <> b) <> c === a <> (b <> c)
    IsMonoid.associative (Monoid.isMonoid listMonoid) {a} {b} {c} = sym $ ++-assoc {xs = a} {ys = b} {zs = c}

listRawMonadPlus : RawMonadPlus {i} List
RawMonadPlus.rawMonoid listRawMonadPlus = listRawMonoid
RawMonadPlus.rawMonad listRawMonadPlus = listRawMonad

module _ {i} where
    open RawMonadPlus {i} listRawMonadPlus
    
    listMonadPlus : MonadPlus {i} List
    MonadPlus.rawMonadPlus listMonadPlus = listRawMonadPlus
    IsMonadPlus.isMonoid (MonadPlus.isMonadPlus listMonadPlus) = Monoid.isMonoid listMonoid
    IsMonadPlus.isMonad (MonadPlus.isMonadPlus listMonadPlus) = Monad.isMonad listMonad
    IsMonadPlus.left-absorb (MonadPlus.isMonadPlus listMonadPlus) = refl
    IsMonadPlus.right-absorb (MonadPlus.isMonadPlus listMonadPlus) {m} = 
        m >> mzero =<>
        (m >>= \_ -> mzero) =<>
        (concatMap (const []) m) =< concatMap-elim {lst = m} >
        mzero qed

listRawAlternativeOver : RawAlternativeOver {i} (RawMonad.rawApplicative listRawMonad)
RawAlternativeOver.rawMonoid listRawAlternativeOver = listRawMonoid

module _ {i} where
    open RawAlternativeOver {i} listRawAlternativeOver
    
    listAlternativeOver : AlternativeOver {i} (Monad.applicative listMonad)
    AlternativeOver.rawAlternativeOver listAlternativeOver = listRawAlternativeOver
    IsAlternativeOver.isMonoid (AlternativeOver.isAlternativeOver listAlternativeOver) = Monoid.isMonoid listMonoid

listRawMonadFailAlternativeOver : RawMonadFailAlternativeOver {i} listRawMonad
RawMonadFailAlternativeOver.rawAlternativeOver listRawMonadFailAlternativeOver = listRawAlternativeOver

module _ {i} where
    open RawMonadFailAlternativeOver {i} listRawMonadFailAlternativeOver
 
    listMonadFailAlternativeOver : MonadFailAlternativeOver {i} listMonad 
    MonadFailAlternativeOver.rawMonadFailAlternativeOver listMonadFailAlternativeOver = listRawMonadFailAlternativeOver
    IsMonadFailAlternativeOver.isAlternativeOver (MonadFailAlternativeOver.isMonadFailAlternativeOver listMonadFailAlternativeOver) = AlternativeOver.isAlternativeOver listAlternativeOver
    IsMonadFailAlternativeOver.left-absorb (MonadFailAlternativeOver.isMonadFailAlternativeOver listMonadFailAlternativeOver) = refl