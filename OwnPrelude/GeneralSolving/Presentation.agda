{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-postfix #-}
-- {-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.Presentation where


open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality

open ExistsSyntax

private
    variable
        ST : Set _
        a b c d f g h i j k l m n n' p q r s s' st t u v w x x' y z fm i' j' k' l' A B C D E F G H K L M N O Q R S T W X Y Z alg Ctx  : ST



































{-
record RawMonad (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        return : A -> M A
        _>>=_  : M A -> (A -> M B) -> M B

    _>=>_ : (A -> M B) -> (B -> M C) -> (A -> M C)
    (amb >=> bmc) a = amb a >>= bmc

record IsMonad {M : Set i -> Set j} (mon : RawMonad M) : Set (lsuc i ~U~ j) where 
    open RawMonad mon
    field
        right-id : m >>= return === m
        left-id : return x >>= f === f x
        associative : m >>= (f >=> g) === (m >>= f) >>= g

    _<*>_ : M (A -> B) -> M A -> M B
    mab <*> ma = mab >>= (\f -> ma >>= (return o f))

    fmap : (A -> B) -> M A -> M B
    fmap f ma = return f <*> ma

    fmap-simplified : fmap f m === m >>= (return o f)
    fmap-simplified {f} {m} = 
        fmap f m =<>
        (return f <*> m) =<>
        (return f >>= (\f -> m >>= (return o f))) =< left-id >
        m >>= (return o f) qed


record Monad (M : Set i -> Set j) : Set (lsuc i ~U~ j) where
    field
        rawMonad : RawMonad M
        isMonad  : IsMonad  rawMonad
    open RawMonad rawMonad public
    open IsMonad  isMonad  public

State : Set k -> Set i -> Set (i ~U~ k)
State S X = S -> (S -x- X)

module _ {S : Set k} where
    stateMonad : Monad {i} (State S)
    RawMonad.return (Monad.rawMonad stateMonad) x s = (s , x)
    RawMonad._>>=_ (Monad.rawMonad stateMonad) mx xmy s = uncurry (flip xmy) (mx s)
    IsMonad.left-id (Monad.isMonad stateMonad) = refl
    IsMonad.right-id (Monad.isMonad stateMonad) = refl
    IsMonad.associative (Monad.isMonad stateMonad) = refl -- {m} {f} {g} i s = refl {a = g (snd (f (snd (m s)) (fst (m s)))) (fst (f (snd (m s)) (fst (m s))))} i 

-}