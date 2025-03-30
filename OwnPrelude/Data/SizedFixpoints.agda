{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.SizedFixpoints where

open import ASCIIPrelude.ASCIIPrelude 
open NatOp renaming (_leq_ to _leqb_)
open VecIndexed
open PolyUnit
open PolyZero
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.LatticeConstructions
open import OwnPrelude.Relation.Functions

open ExistsSyntax

private
    variable
        k l : Level
        n n' n'' n1 n2 n3 : Nat
        A B C X Y Z : Set k
        a b c x y z fx T mes g f p q fa fv h alg i j : A
        M F G : Set i -> Set j


FixN : Nat -> (F : Set i -> Set i) -> Set i
FixN 0 F = Zero
FixN (1+ n) F = F (FixN n F)

OutN : FixN (1+ n) F -> F (FixN n F)
OutN fx = fx

InN : F (FixN n F) -> FixN (1+ n) F
InN fx = fx 

-- completely wrong. This does not allow for recursive values to be smaller.
-- FixMaxN : Nat -> (F : Set i -> Set i) -> Set i
-- FixMaxN n F = exists[ n' ] ((1+ n') leq n -x- FixN (1+ n') F)

FixMaxN : (n : Nat) -> (F : Set i -> Set i) -> Set i
FixMaxN 0 F = Zero
FixMaxN (1+ n) F = (F (FixMaxN n F)) or (FixMaxN n F)

liftFixMaxN : FixMaxN n F -> FixMaxN (n' + n) F
liftFixMaxN {(n)} {F} {n' = zero} fx = fx
liftFixMaxN {(n)} {F} {n' = 1+ n'} fx = right (liftFixMaxN fx)

liftFixMaxN1 : FixMaxN n F -> FixMaxN (1+ n) F
liftFixMaxN1 fx = right fx

liftLeqFixMaxN : FixMaxN n F -> n leq n' -> FixMaxN n' F
liftLeqFixMaxN {n} {F} {n'} fx (n'' , eq) = coerce (trans (comm-+ {n''} {n}) eq || \h -> FixMaxN h F) (liftFixMaxN fx) 

liftMaxLeftFixMaxN : (n' : Nat) -> FixMaxN n F -> FixMaxN (max n n') F
liftMaxLeftFixMaxN n' fx = liftLeqFixMaxN fx left-leq-max

liftMaxRightFixMaxN : (n' : Nat) -> FixMaxN n F -> FixMaxN (max n' n) F
liftMaxRightFixMaxN n' fx = liftLeqFixMaxN fx right-leq-max

homFixMaxFst : FixMaxN n F -> FixMaxN n' G -> FixMaxN (max n n') F
homFixMaxFst fxf fxg = liftLeqFixMaxN fxf left-leq-max

homFixMaxSnd : FixMaxN n F -> FixMaxN n' G -> FixMaxN (max n n') G
homFixMaxSnd fxf fxg = liftLeqFixMaxN fxg right-leq-max

-- module OutMaxF {F : Set i -> Set i} (func : Functor F) where
--     open Functor func
--     OutMaxN : FixMaxN n F -> F (FixMaxN n F)
--     OutMaxN {1+_ n} (left  fv) = liftFixMaxN1 <$> fv
--     OutMaxN {1+_ n} (right fx) = liftFixMaxN1 <$> OutMaxN fx

InMaxN : F (FixMaxN n F) -> FixMaxN (1+ n) F
InMaxN = left

module OutMaxF {F : Set i -> Set i} (func : Functor F) where
    open Functor func
    
    OutMaxN : FixMaxN (1+ n) F -> F (FixMaxN n F)
    OutMaxN (left  fx) = fx
    OutMaxN {1+ n} (right fy) = liftFixMaxN1 <$> OutMaxN fy

module SetIndexedFixpoints {I : Set i} where

    -- important: not the standard indexed functor variant
    FixNI : Nat -> (F : (I -> Set k) -> (I -> Set k)) -> I -> Set k
    FixNI 0 _ _ = Zero
    FixNI (1+ n) F i = F (FixNI n F) i

    FixMaxNI : Nat -> (F : (I -> Set k) -> (I -> Set k)) -> I -> Set k
    FixMaxNI 0 _ _ = Zero
    FixMaxNI (1+ n) F i = (F (FixNI n F)) i or (FixMaxNI n F i)

module GenIndexedFixpoints {I : Set i} {K : Set k} (zer : K) (_or_ : K -> K -> K) where
    FixNI : Nat -> (F : (I -> K) -> (I -> K)) -> I -> K
    FixNI 0 _ _ = zer
    FixNI (1+ n) F i = F (FixNI n F) i

    FixMaxNI : Nat -> (F : (I -> K) -> (I -> K)) -> I -> K
    FixMaxNI 0 _ _ = zer
    FixMaxNI (1+ n) F i = (F (FixNI n F)) i or (FixMaxNI n F i)

record SizedFixpoint (F : Set i -> Set i) (Fix : Nat -> Set i) : Set (lsuc i) where
    field
        In  : F (Fix n)  -> Fix (1+ n)
        Out : Fix (1+ n) -> F (Fix n)
        liftF : Fix n -> Fix (n + n')
        fold : (F A -> A) -> Fix n -> A
    --     functor : Functor F
    -- open Functor functor

    -- to-alg : (forall n -> Fix n -> A) -> F A -> A -- only computable in certain categories...
    -- to-alg f fa = {!    !}
    field
        -- fold-prop : fold {n = n} (to-alg f) === f n
        in-o-out-id : In {n = n} o Out === id
        out-o-in-id : Out {n = n} o In === id
        liftF-prop : fold alg o' liftF {n = n} {n' = n'} === fold alg

    -- Out : Fix -> F Fix
    -- Out = fold join -- TODO: this only works for monads

    -- to-alg : (Fix n -> A) -> F A -> A
    -- to-alg f fa = 

record SizedIndexedMutualFixpoint 
    (Fix' : Nat -> Set j) 
    (Fix : forall {n} -> Fix' n -> Set j) 
    (F : forall {n} -> (Fix' n -> Set j) -> (Fix' n -> Set j)) : Set j where
    field
        liftFix : Fix' n -> Fix' (n' + n)
    liftFix1 : Fix' n -> Fix' (1+ n)
    liftFix1 = liftFix
    field
        In : F (Fix {n}) i -> Fix {1+ n} (liftFix1 i)
        Out : Fix {1+ n} (liftFix1 i) -> F (Fix {n}) i
        In-Out-IsIso : IsIsomorphism (In {i = i}) Out

        InFix : Fix {n} i -> Fix' (1+ n)
        OutFix : Fix' (1+ n) -> exists[ i ] Fix {n} i
        InFix-OutFix-IsIso : IsIsomorphism (InFix {n = n} o snd) OutFix

module TestFunctor {I : Nat -> Set i} (zer : forall {n} -> I n) (_or_ : forall {n} -> I n -> I n -> I n) where
    data toSet {A : Set i} (a : A) : Set i where
        ts : toSet a

    module FP {n : Nat} where
        open GenIndexedFixpoints {I = I n} (zer {n}) (_or_ {n}) public
    open FP
        
    -- TODO: This only works if we lift the WHOLE thing into a category. Like...all of type theory. This specifically only
    -- works for the type of type theory so...we might as well just create a fixpoint for exactly that type...
    -- this would look as follows: We have pointers to the data constructors together with pointers to its subelements. This would be some kind of sigma type or something. 
    -- we then show that we can unwrap this into the usual type of type theory. 
    -- testFunctor : 
    --     (IdxFix : forall {n : Nat} (F : (I n -> I n) -> (I n -> I n)) -> I (1+ n) -> (exists[ j of (I n) ] (FixMaxNI (1+ n) F) j)) ->
    --     (FixIdx : forall {n : Nat} {j : I n} (F : (I n -> I n) -> (I n -> I n)) -> FixMaxNI n F j -> I n) ->
    --     (n : Nat) ->
    --     (A : I n -> I n) -> (I n -> I n)
    -- testFunctor _ _ 0 _ _ = zer
    -- testFunctor IdxFix FixIdx (1+ n) A j = toSet (IdxFix (testFunctor IdxFix FixIdx n) j) -- IdxFix (testFunctor n Fix In Out IdxFix) j -- (Fx : Fix (testFunctor n Fix In Out) j) -> {! Out Fx  !}
    -- -- This already works with the indexed functor fixpoint from above!

module _ {k : Level} where
    

-- This is a fixpoint for a certain class of functors. 
-- finite functors are definitely in, but also some functors that use functions.
-- these functions have to be able to tell the siye of the output given the input. 
-- this is possible for all functions that we would write with a finite representation

Fix : (F : Set i -> Set i) -> Set i
Fix F = exists[ n ] FixMaxN n F

maxToFix : FixMaxN n F -> Fix F
maxToFix {n} fx = n , fx

_[[_]]^ : Fix F -> Nat -> Set
(n , fv) [[ n' ]]^ = n leq n'

module _ {F : Set i -> Set i}  where
    sizedFixMax : {fx : Fix F} -> _[[_]]^ {F = F} fx n -> FixMaxN n F
    sizedFixMax {n} {fx = n' , fv} (n'' , eq) = coerce (trans (comm-+ {n''} {n'}) eq || \n -> FixMaxN n F) (liftFixMaxN fv)

-- module OutF {F : Set i -> Set i} (func : Functor F) where
--     open Functor func
--     open OutMaxF func
--     Out : Fix F -> F (Fix F)
--     Out (1+ n , left  fv) = maxToFix <$> fv
--     Out (1+ n , right fx) = maxToFix <$> OutMaxN fx

module _ where
    open VecOp 

    maxSize : Vec (Fix F) n -> Nat
    maxSize [] = 0
    maxSize ((n , _) :: vec) = max n (maxSize vec)
    
    homFixLst : (v : Vec (Fix F) n) -> Vec (FixMaxN (maxSize v) F) n
    homFixLst [] = []
    homFixLst ((n , fx) :: vec) = liftMaxLeftFixMaxN (maxSize vec) fx :: map (liftMaxRightFixMaxN n) (homFixLst vec)

module MaxFunctors {B : Set j} (sl : Semilattice B) where
    open Semilattice sl
    record MaxFunctor (F : Set i -> Set i) : Set (lsuc i ~U~ j) where
        field
            functor : Functor F
        open Functor functor
        field
            measure : F A -> (A -> B) -> B
            withMeasure : {C : B -> Set i} -> (fa : F A) -> (g : A -> B) -> ((a : A) -> (g a) P (measure fa g) -> C (measure fa g)) -> F (C (measure fa g))
            -- laws: functor should preserve shape and positions throughout this transformation
            pres-id : withMeasure {A = A} f g (\a _ -> a) === f
            mes-pres-fmap : measure (f <$> fa) g === measure fa (g o f)
            withMes-pres-fmap : {C : B -> Set i}{fx : F X}{f : X -> A}{g : A -> B} {h : (a : A) -> (g a) P (measure (f <$> fa) g) -> C (measure (f <$> fa) g)} -> 
                withMeasure {A = A} {C = C} (f <$> fa) g h === coerce (sym mes-pres-fmap || F o C) (withMeasure {A = X} {C = C} fa (g o f) (coerce (mes-pres-fmap || (\k -> (x : X) -> g (f x) P k -> C k)) (h o f)))


module NatMaxFunctors where  
    open MaxFunctors stdNatSemilattice public