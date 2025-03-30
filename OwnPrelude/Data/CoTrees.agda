{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.CoTrees where

open import ASCIIPrelude.ASCIIPrelude 
-- open NatOp
open PolyUnit
open PolyZero
open NatOp hiding (_^_) renaming (_leq_ to _leqB_)
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp
open import OwnPrelude.Equality
open import Level.Literals

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.Containers
open import OwnPrelude.Relation.Functions

open ExistsSyntax

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d e f g h i j k l m n p q r s t u v w x y z fm i' j' k' l' A B C D E F G H I K L M N O P Q  R S T U V X Y Z alg xs ys lst  : ST

open Container using ([[_]])
open ContainerClosures
open CorecursiveFixpoints
open RecursiveFixpoints hiding (Out)

module Perhaps where

    record Perhaps (A : Set i) : Set i where
        constructor PC
        coinductive
        field
            val? : A -+- Perhaps A

        --TODO: make those patterns?
        val : A -> A -+- Perhaps A
        val = left

        ctd : Perhaps A -> A -+- Perhaps A
        ctd = right

    open Perhaps public
    
    extract : Nat -> Perhaps A -> Maybe A
    extract 0 _      = nothing
    extract (1+ n) p with val? p 
    ... | left  d  =  just d
    ... | right ph = extract n ph

module PerhapsState where
    record PerhapsState (S : Set i) (X : Set j) : Set (i ~U~ j) where
        constructor PSC
        coinductive
        field
            run : S -> S -x- (X -+- PerhapsState S X)

    open PerhapsState public

    pattern val x = left x
    pattern ctd x = right x
    
    extract : Nat -> PerhapsState S X -> S -> S -x- Maybe X
    extract 0 p s with (run p) s
    ... | s' , val x = s' , just x
    ... | s' , ctd y = s' , nothing
    extract (1+ n) p s with (run p) s 
    ... | s' , val x = s' , just x
    ... | s' , ctd y = extract n y s'

-- Co Trees are just corecursive container fixpoints. They may carry leaves or nodes through their constructing container. 
-- We can stress this by requireing a container family, to allow the structure to carry outside data.
-- however, for our constructions, it is beneficial to delimit the functor carrying the recusive call from the one carrying the data.
-- empty leaves are modeled as an empty object of the recursive functor

-- CoTree : (C : Set k -> Container i j) (A : Set k) -> Set (i ~U~ j ~U~ k)
-- CoTree {k} C A = CoW (C A)

-- CoTreeF : (Set k -> Container i j) -> Container i j -> (A : Set k) -> Container i j
-- CoTreeF {k} D R A = D A :+: R

-- recc = rightc
-- datc = leftc

-- CoTree : (R : Container i j) -> (A : Set i) -> Set (i ~U~ j)
-- CoTree {i} R A = CoW (CoTreeF KC R A)

CoTree : (R : Container i j) -> Set (i ~U~ j)
CoTree R = CoW R

module _ {A : Set i} {F : Container i j} where
    open CoW
    open ContainerOps

    mkDataTree : (A -> ([[ R :o: F ]]) A) -> A -> CoTree (R :o: F)
    mkDataTree coalg = cofold coalg

    -- sidenote: we are aware that the algebra can also just make up a constructor, but that does not matter when enumeration is complete. 
    -- however: It could fill n existing constructor with a new recursive call. This does not matter when all recursive calls are the same!
    getRep : ([[ R :o: F ]] (CoW (R :o: F)) -> [[ F ]] (CoW (R :o: F))) -> CoTree (R :o: F) -> CoW F
    Out (getRep alg t) with (s , p) <- alg (Out t) = (s , getRep alg o p)
    -- Out (getRep alg t) = map (getRep alg) (alg (Out t))

    -- maybe the above should be done monadically, so that we can also derive indexed types via a state
    --TODO: implement the statewise definition of retrieving a data type that is indexed

    --this turns into a normal data type when for example given some fuel. Can also be realised with a stream of Sigma Nat ...
    getRep' : ([[ R :o: F ]] (CoW (R :o: F)) -> [[ F ]] (CoW (R :o: F))) -> [[ F ]] (W F) -> Nat -> CoTree (R :o: F) -> W F
    getRep' alg f0 0      t = In f0
    getRep' alg f0 (1+ n) t = In (map (getRep' alg f0 n) (alg (Out t)))
