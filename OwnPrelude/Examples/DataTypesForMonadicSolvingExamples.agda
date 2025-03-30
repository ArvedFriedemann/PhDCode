{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Examples.DataTypesForMonadicSolvingExamples where

open import ASCIIPrelude.ASCIIPrelude hiding (List; []; _::_)
open NatOp -- renaming (_leq_ to _leqb_)
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Data.Containers

open ExistsSyntax

-- \tagcode{DataTypesExamples}

private
    variable
        k l : Level
        n n' n'' n1 n2 n3 : Nat
        ST : Set k
        A B C X Y Z R : ST
        a b c x y z fx T mes g f p q fa fv h alg i j : ST
        M F G : Set i -> Set j

module ListExample where
    infixr 20 _::_
    data List (A : Set) : Set where
        []   : List A
        _::_ : A -> List A -> List A

    concat : List A -> List A -> List A
    concat []        y = y
    concat (x :: xs) y = x :: (concat xs y)

    bagsOfTwo : List A -> List (List A)
    bagsOfTwo  []            = []
    bagsOfTwo (a :: [])      = []
    bagsOfTwo (a :: b :: xs) = (a :: b :: []) :: bagsOfTwo xs

    bubbleSortStep : List Nat -> List Nat
    bubbleSortStep  [] = []
    bubbleSortStep (x :: []) = x :: []
    bubbleSortStep (x :: y :: ys) = 
        if x leq y 
         then x :: (bubbleSortStep (y :: ys)) 
         else y :: (bubbleSortStep (x :: ys))

module ListFExample where

    infixr 20 _::F_
    data ListF (A : Set) (R : Set) : Set where
        []F   : ListF A R
        _::F_ : A -> R -> ListF A R

    data ListFix (A : Set) : Set where
        InList : ListF A (ListFix A) -> ListFix A

    record ListCoFix (A : Set) : Set where
        coinductive
        constructor InCoList
        field
            OutCoList : ListF A (ListCoFix A)
    open ListCoFix

    cofoldList : (B -> ListF A B) -> B -> ListCoFix A
    OutCoList (cofoldList alg b) with alg b 
    ... | []F      = []F
    ... | x ::F xs = x ::F (cofoldList alg xs)

    foldList : (ListF A B -> B) -> ListFix A -> B
    foldList alg (InList []F) = alg []F
    foldList alg (InList (x ::F xs)) = alg (x ::F foldList alg xs)

    foldCtx : {M : Set -> Set} -> (ListF A (M B) -> M B) -> ListFix A -> M B
    foldCtx alg = foldList alg

    foldList2AlgCtx : {A : Set} -> Set -> Set
    foldList2AlgCtx {A} B = ListF A B -x- B

    foldList2Alg : (ListF A (ListF A B) -> B) -> 
        ListF A ((foldList2AlgCtx {A}) B) -> ((foldList2AlgCtx {A}) B)
    foldList2Alg alg []F                          = []F      , alg []F
    foldList2Alg alg (x ::F ([]F , ys))           = x ::F ys , ys
    foldList2Alg alg (x ::F (y ::F b  , ys))      = x ::F ys , alg (x ::F y ::F b)

    foldList2 : (ListF A (ListF A B) -> B) -> ListFix A -> B
    foldList2 {A} alg = snd o foldList (foldList2Alg alg)

    foldList2' : (ListF A (ListF A B) -> B) -> ListFix A -> B
    foldList2' alg (InList []F) = alg []F
    foldList2' alg (InList (x ::F InList []F)) = alg []F
    foldList2' alg (InList (x ::F InList (y ::F ys))) = alg (x ::F y ::F (foldList2' alg ys))

    module _ {alg : ListF A (ListF A B) -> B} where

        foldList2State-tuple : forall {x y ys} -> 
            foldList (foldList2Alg alg) (InList (x ::F InList (y ::F ys))) 
            ===
            (x ::F snd (foldList (foldList2Alg alg) (InList (y ::F ys)))) , alg (x ::F y ::F snd (foldList (foldList2Alg alg) ys))
        foldList2State-tuple {y} {InList []F} = refl
        foldList2State-tuple {x} {y} {InList (z ::F zs)} with foldList2Alg alg (z ::F foldList (foldList2Alg alg) zs)
        ... | []F     , _ = refl
        ... | _ ::F _ , _ = refl

        foldList2-correct : {lst : ListFix A} -> foldList2 alg lst === foldList2' alg lst
        foldList2-correct {InList []F} = refl
        foldList2-correct {InList (x ::F InList []F)} = refl
        foldList2-correct {InList (x ::F InList (y ::F ys))} = 
            foldList2 alg (InList (x ::F InList (y ::F ys)))                     =<>
            snd (foldList (foldList2Alg alg) (InList (x ::F InList (y ::F ys)))) =< foldList2State-tuple {x} {y} {ys} || snd >
            alg (x ::F y ::F snd (foldList (foldList2Alg alg) ys))               =< foldList2-correct {lst = ys} || alg o (\ys -> x ::F y ::F ys) >
            alg (x ::F y ::F foldList2' alg ys)                                  qed

    [] : ListFix A
    [] = InList []F

    infixr 20 _::_
    _::_ : A -> ListFix A -> ListFix A
    a :: lst = InList (a ::F lst) 

    {-# DISPLAY InList []F = [] #-}
    {-# DISPLAY InList (x ::F xs) = x :: xs #-}

    concat : ListFix A -> ListFix A -> ListFix A
    concat x y = foldList (\{ []F        -> y
                            ; (x ::F xs) -> x :: xs}) x

    bagsOfTwo : ListFix A -> ListFix (ListFix A)
    bagsOfTwo = foldList2
        \{ []F -> []
        ; (x ::F []F) -> []
        ; (x ::F y ::F ys) -> (x :: y :: []) :: ys
        }

    test : ListFix (ListFix Nat)
    test = bagsOfTwo (1 :: 2 :: 3 :: 4 :: 5 :: [])
    --ListFExample.test

    coConcat : ListCoFix A -> ListCoFix A -> ListCoFix A
    coConcat {A} xs ys = cofoldList (caseOf OutCoList 
        \{[]F -> OutCoList ys
        ; (x ::F xs') -> x ::F xs'}) xs

module ListContainer where
    open Container

    ListC : Set i -> Container i i 
    ListC {i} A = (Unit {i} or A) |> fromSum (\_ -> Zero) (\_ -> Unit)

    []F : [[ ListC A ]] R
    []F = left unit , \()

    _::F_ : A -> R -> [[ ListC A ]] R
    a ::F r = right a , \{unit -> r}

open import ASCIIPrelude.ASCIIPrelude using  (List; []; _::_)

module FixpointProofs where
    open BoolOp renaming (notBool to not``Bool)
    open Container
    open ContainerOps
    open ContainerClosures
    open RecursiveFixpoints

    not-inv : not``Bool (not``Bool x) === x
    not-inv {x = true } = refl :T: (not``Bool (not``Bool true ) === true )
    not-inv {x = false} = refl :T: (not``Bool (not``Bool false) === false)

    zero-right-id : x + 0 === x
    zero-right-id {x = 0} = refl :T: (0 + 0 === 0)
    zero-right-id {x = 1+ x} = (zero-right-id {x = x} || 1+_) :T: ((1+ x) + 0 === (1+ x))

    NatF : Container lzero lzero
    NatF = UnitC :+: IC

    NatC = W NatF

    +-alg : NatC -> [[ NatF ]] NatC -> NatC
    +-alg y (left unit , _)  = y
    +-alg y (right unit , p) = In (rightc (ic (p unit)))

    _+F_ : NatC -> NatC -> NatC
    x +F y = foldC (+-alg y) x

    zero-right-idC : x +F (In $ leftc unitc) === x
    zero-right-idC {x} = flip (foldPi {A = \x -> x +F (In $ leftc unitc) === x}) x
        \{ (left x  , p) -> extens (\()) || In o (left x ,_)
         ; (right y , p) -> 
            (In (right y , fst o p) +F In (leftc unitc))                                    =<>
            +-alg (In (leftc unitc)) (right y , foldC (+-alg (In (leftc unitc))) o fst o p) =<>
            In (rightc (ic ((foldC (+-alg (In (leftc unitc))) o fst o p) unit)))            =< extens (\_ -> snd (p unit)) || (\h -> In (rightc (ic ((h o fst o p) unit)))) >
            In (rightc (ic ((fst o p) unit)))                                               =<>
            (In (right y , fst o p))                                                        qed}