{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.FreeMonads where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import OwnPrelude.Data.Containers
open import OwnPrelude.Categorical.Monads

open ExistsSyntax

private
    variable
        k l : Level
        n n' n'' n1 n2 n3 : Nat
        ST : Set k
        A B C D X Y Z : ST
        a b c x y z fx T mes g f p q fa fv h alg i j i' j' : ST
        M F G : Set i -> Set j

open ContainerClosures
open RecursiveFixpoints
open Container
open ContainerOps

FreeMonadC : (C : Container i j) -> Set i -> Container i j
FreeMonadC C X = KC X :+: C

pattern purec x {p} = (left x , p)
pattern impurec s p = (right s , p)

FreeMonad : (C : Container i j) -> Set i -> Set (i ~U~ j)
FreeMonad C X = W (FreeMonadC C X)

module MonadicNames {C : Container i i} where
    return : A -> FreeMonad C A
    return a = In $ purec a {\()}

    fmap : (A -> B) -> FreeMonad C A -> FreeMonad C B
    fmap f = foldC \{ (purec x) -> In (purec (f x) {\()})
                    ; (impurec s p) -> In (impurec s p)}

    join : FreeMonad C (FreeMonad C A) -> FreeMonad C A
    join = foldC \{ (purec x) -> x
                  ; (impurec s p) -> In (impurec s p)}

    _>>=_ : FreeMonad C A -> (A -> FreeMonad C B) -> FreeMonad C B
    ma >>= f = join (fmap f ma)

module _ {C : Container i i} where
    open MonadicNames {C = C}

    private
        left-identity : forall {f : A -> FreeMonad C B} -> return x >>= f === f x
        left-identity = refl

    freeMonad : Monad {i} (FreeMonad C) 
    freeMonad .Monad.rawMonad .RawMonad.return = return
    freeMonad .Monad.rawMonad .RawMonad._>>=_ = _>>=_
    freeMonad .Monad.isMonad .IsMonad.left-identity = refl
    freeMonad .Monad.isMonad .IsMonad.right-identity {m} = foldPi {A = \m -> m >>= return === m} (
        \{ (purec x)     -> 
            join (fmap return (In (purec x {\()}))) =<>
            join (In (purec (return x) {\()}))      =<>
            (return x)                              =< extens (\()) || In o (\p -> purec x {p}) >
            In (purec x)                            qed
        ;  (impurec s p) -> 
            (In (impurec s (fst o p)) >>= return) =<>
            join (fmap return (In (impurec s (fst o p)))) =<>
            In (impurec s (join o fmap return o fst o p)) =<>
            In (impurec s (\p' -> fst (p p') >>= return)) =< (\p' -> snd (p p')) |pi In o impurec s >
            In (impurec s (\p' -> fst (p p'))) qed}) m
    freeMonad .Monad.isMonad .IsMonad.associative {m} {f} {g} = foldPi {A = \m -> (m >>= f) >>= g === m >>= (\a -> f a >>= g) } (
        \{ (purec x) ->
            ((In (purec x {\()}) >>= f) >>= g)          =< left-identity {f = f} || _>>= g >
            (f x >>= g)                                 =< sym (left-identity {f = \x -> f x >>= g}) >
            (In (purec x {\()}) >>= (\ a -> f a >>= g)) qed
        ;  (impurec s p) -> 
            ((In (map fst (impurec s p)) >>= f) >>= g)                              =<>
            (join (fmap f (In (map fst (impurec s p)))) >>= g)                      =<>
            (join (In (impurec s (fmap f o fst o p))) >>= g)                        =<>
            (In (impurec s (join o fmap f o fst o p)) >>= g)                        =<>
            (join o fmap g) (In (impurec s (join o fmap f o fst o p)))              =<>
            (In (impurec s ((join o fmap g) o (join o fmap f) o fst o p)))          =< (\p' -> snd (p p')) |pi In o impurec s >
            (In (impurec s (join o fmap ((join o fmap g) o f) o fst o p)))          =<>
            (In (impurec s (join o fmap (\ a -> (join o fmap g) (f a)) o fst o p))) =<>
            join (In (impurec s (fmap (\ a -> f a >>= g) o fst o p)))               =<>
            join (fmap (\ a -> f a >>= g) (In (impurec s (fst o p))))               =<>
            (In (impurec s (fst o p)) >>= (\ a -> f a >>= g)) qed}) m