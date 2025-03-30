{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.ASCIIPreludeProofs where

open import ASCIIPrelude.ASCIIPrelude
open import OwnPrelude.Equality

private
    variable
        h i j k k' l i' j' c : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G : Set i -> Set j
        a b x y z m : A
        f g : A -> B
        xs ys zs lst : List A

o-right-id : f o id === f
o-right-id = extens \_ -> refl

o-left-id : id o f === f
o-left-id = extens \_ -> refl

open ListOp

[]-right-id : {lst : List A} -> lst ++ [] === lst
[]-right-id {lst = []} = refl
[]-right-id {lst = x :: lst} = []-right-id || (x ::_)

concat-:: : (x :: xs) ++ ys === x :: (xs ++ ys)
concat-:: {xs = []} = refl
concat-:: {x} {xs = y :: xs} {ys} = 
    (x :: y :: xs) ++ ys   =<>
    x :: ((y :: xs) ++ ys) =< concat-:: {xs = xs} || (\h -> x :: h) >
    x :: (y :: xs ++ ys)   qed

++-assoc : xs ++ (ys ++ zs) === (xs ++ ys) ++ zs
++-assoc {xs = []} = refl
++-assoc {xs = x :: xs} = ++-assoc {xs = xs} || (x ::_)

concatMap-return-id : {lst : List A} -> concatMap (_:: []) lst === lst
concatMap-return-id {lst = []} = refl
concatMap-return-id {lst = x :: lst} = concatMap-return-id || (x ::_)

concatMap-++ : {f : A -> List B}{xs ys : List A} -> 
    concatMap f (xs ++ ys) === concatMap f xs ++ concatMap f ys
concatMap-++ {xs = []} = refl
concatMap-++ {f} {xs = x :: xs} {ys} = 
    concatMap f (x :: xs ++ ys)                 =< concat-:: {xs = xs} {ys = ys} || concatMap f >
    concatMap f (x :: (xs ++ ys))               =<>
    (f x) ++ (concatMap f (xs ++ ys))           =< concatMap-++ {xs = xs} {ys = ys} || (f x ++_) >
    (f x) ++ (concatMap f xs ++ concatMap f ys) =< ++-assoc {xs = f x} {ys = concatMap f xs} {zs = concatMap f ys} >
    ((f x) ++ concatMap f xs) ++ concatMap f ys =<>
    concatMap f (x :: xs) ++ concatMap f ys     qed

concatMap-++-comp : {lst : List A}{f : B -> List C}{g : A -> List B}{x : A} -> 
    concatMap f (g x) ++ concatMap f (concatMap g lst) === concatMap f (concatMap g (x :: lst))
concatMap-++-comp {lst = []} {f} {g} {x} with g x 
... | [] = refl
... | gx :: xs = 
    (f gx ++ foldr _++_ [] (map f xs)) ++ [] =< []-right-id >
    (f gx ++ foldr _++_ [] (map f xs)) =< sym ([]-right-id {lst = xs}) || (\h -> f gx ++ foldr _++_ [] (map f h)) >
    f gx ++ foldr _++_ [] (map f (xs ++ [])) qed
concatMap-++-comp {lst = x' :: lst} {f} {g} {x} = 
    concatMap f (g x) ++ concatMap f (concatMap g (x' :: lst))               =<>
    concatMap f (g x) ++ concatMap f ((g x') ++ concatMap g lst)             =< concatMap-++ {xs = g x'} {ys = concatMap g lst} || concatMap f (g x) ++_ >
    concatMap f (g x) ++ concatMap f (g x') ++ concatMap f (concatMap g lst) =< concatMap-++-comp {lst = lst} {f = f} {g = g} {x = x'} ||  concatMap f (g x) ++_ >
    concatMap f (g x) ++ concatMap f (concatMap g (x' :: lst))               =< sym (concatMap-++ {f = f} {xs = g x} {ys = concatMap g (x' :: lst)}) >
    concatMap f (concatMap g (x :: x' :: lst))                               qed

concatMap-compose : {lst : List A}{f : B -> List C}{g : A -> List B} -> 
    concatMap (concatMap f o g) lst === concatMap f (concatMap g lst)
concatMap-compose {lst = []} = refl
concatMap-compose {lst = x :: lst} {f} {g} = 
    concatMap (concatMap f o g) (x :: lst)                   =<>
    (concatMap f o g $ x) ++ concatMap (concatMap f o g) lst =< concatMap-compose {lst = lst} || (\h -> (concatMap f o g $ x) ++ h) >
    (concatMap f o g $ x) ++ concatMap f (concatMap g lst)   =<>
    (concatMap f) (g x) ++ concatMap f (concatMap g lst)     =< concatMap-++-comp {lst = lst} >
    concatMap f (concatMap g (x :: lst))                     qed

concatMap-elim : concatMap {B = B} (const []) lst === []
concatMap-elim {lst = []} = refl
concatMap-elim {lst = x :: lst} = 
    concatMap (const []) (x :: lst) =<>
    [] ++ concatMap (const []) lst  =<>
    concatMap (const []) lst        =< concatMap-elim {lst = lst} >
    []                              qed

concatMap-singleton : concatMap f (x :: []) === f x
concatMap-singleton {f} {x} with f x
... | [] = refl
... | x' :: xs = []-right-id || x' ::_

module CoverSumGeneral {X : Set i}{Y : Set j} where
    open PolyZero
    
    CoverSum : X -+- Y -> X -+- Y -> Set (i ~U~ j)
    CoverSum (left x) (left y)   = LiftL j (x === y)
    CoverSum (right x) (right y) = LiftL i (x === y)
    CoverSum _ _ = Zero

    encodeReflSum : CoverSum a a
    encodeReflSum {a = left  x} = liftL refl
    encodeReflSum {a = right x} = liftL refl

    encodeSum : {a b : X -+- Y} -> a === b -> CoverSum a b
    encodeSum {a} = J (\b _ -> CoverSum a b) encodeReflSum

module CoverSumSameLevel {X : Set i}{Y : Set i} where
    open PolyZero
    
    CoverSum : X -+- Y -> X -+- Y -> Set i
    CoverSum (left x) (left y)   = (x === y)
    CoverSum (right x) (right y) = (x === y)
    CoverSum _ _ = Zero

    encodeReflSum : CoverSum a a
    encodeReflSum {a = left  x} = refl
    encodeReflSum {a = right x} = refl

    encodeSum : {a b : X -+- Y} -> a === b -> CoverSum a b
    encodeSum {a} = J (\b _ -> CoverSum a b) encodeReflSum


module _ {X : Set i} where
    open PolyZero
    open PolyUnit
    
    CoverMaybe : Maybe X -> Maybe X -> Set i
    CoverMaybe (just x) (just y) = x === y
    CoverMaybe nothing nothing   = Unit
    CoverMaybe _ _ = Zero

    encodeReflMaybe : CoverMaybe a a
    encodeReflMaybe {a = just  x} = refl
    encodeReflMaybe {a = nothing} = unit

    encodeMaybe : {a b : Maybe X} -> a === b -> CoverMaybe a b 
    encodeMaybe {a} = J (\b _ -> CoverMaybe a b) encodeReflMaybe