{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Relation.Functions where

open import ASCIIPrelude.ASCIIPrelude 
open PolyFin
open import ASCIIPrelude.ASCIIProofPrelude
open import OwnPrelude.Equality
open import OwnPrelude.Equality public using (Isomorphism; IsIsomorphism)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Categorical.Monads

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        ST : Set i
        A B C n : ST

repeat : Nat -> (A -> A) -> A -> A
repeat 0 _ a = a
repeat (1+ n) f a = repeat n f (f a)

module RepeatSyntax where
    _^_ : (A -> A) -> Nat -> A -> A
    f ^ n = repeat n f

    module _ {f : A -> A} where
        fof^n=f^1+n : f o f ^ n === f ^ (1+ n)
        fof^n=f^1+n {(zero)} = refl
        fof^n=f^1+n {1+_ n} = extens \a -> fof^n=f^1+n {n = n} || (_$ f a)

module _ {A : Set i} {B : Set j} where
    record IsInjection (f : A -> B) (g : B -> A) : Set (i ~U~ j) where
        field
            gof-id : g o f === id 


record Injection (A : Set i) (B : Set j) : Set (i ~U~ j) where
    field
        inf : A -> B
        outf : B -> A
        outfoinf-id : outf o inf === id 
    
    module _ {f : A -> C} where
        preserves-function : f o outf o inf === f
        preserves-function = outfoinf-id || f o_

injection-refl : Injection A A
Injection.inf injection-refl         = id
Injection.outf injection-refl        = id
Injection.outfoinf-id injection-refl = refl

module _ where
    open Injection

    injection-trans : Injection A B -> Injection B C -> Injection A C
    inf (injection-trans ab bc) = inf bc o inf ab
    outf (injection-trans ab bc) = outf ab o outf bc
    outfoinf-id (injection-trans ab bc) = 
        outf ab o outf bc o inf bc o inf ab =<>
        outf ab o (outf bc o inf bc) o inf ab =< outfoinf-id bc || (\h -> outf ab o h o inf ab) >
        outf ab o inf ab =< outfoinf-id ab >
        id qed

injectionIsPreOrder : IsPreOrder (Injection {i = i} {j = i})
IsPreOrder.reflexive injectionIsPreOrder = injection-refl
IsPreOrder.transitive injectionIsPreOrder = injection-trans

_inn_ : A -> (A -> Set i) -> Set i
a inn P = P a

module _ {A : Set i} {B : Set j} where
    infix 100 Image_
    Image_ : (f : A -> B) (b : B) -> Set (i ~U~ j)
    Image_ f b = exists[ a ] (f a === b)

module _ {f : A -> B} {b : B} (inj : Injection A C) where
    open Injection inj
    _preservesImageIn_ : (Image f) b -> (Image (f o outf)) b
    _preservesImageIn_ (a , fa=b) = (inf a) , (
        (f o (outf o inf)) a =< outfoinf-id || (\h -> (f o h) a) >
        f a                  =< fa=b >
        b                    qed)

    _preservesImageOut_ : (Image (f o outf)) b -> (Image f) b
    _preservesImageOut_ (a , fa=b) = (outf a) , fa=b

module _ {A : Set i} {B : Set j} {C : Set k} where
    -- \tagcode{Independence}
    Independence : (f : A -> B) (g : A -> C) -> Set (i ~U~ j ~U~ k)
    Independence f g = forall b c -> b inn Image f -> c inn Image g -> exists[ a ] ((f a === b) and (g a === c)) 
    
module _ {f : A -> B} {g : A -> C} where
    independence-commutative : Independence f g -> Independence g f
    independence-commutative indep b c imf img with indep c b img imf
    ...| (a , fa=b , ga=c) = a , ga=c , fa=b

module _ {A : Set i} {B : Set j} {C : Set k} {D : Set l} where
    functionProductIndependence : {f : A -> B} -> {g : C -> D} -> Independence (f o fst) (g o snd)
    functionProductIndependence {f} {g} b d ((a , _) , fa=b) ((_ , c) , gc=d) = (a , c) , fa=b , gc=d

record Finite (A : Set i) : Set i where
    field
        num : Nat
        iso : Isomorphism A (Fin {i} num)
    open Isomorphism iso public
        renaming 
            ( to to toIdx
            ; from to fromIdx )

    finiteToEq : A === Fin {i} num
    finiteToEq = Iso->=== iso

    -- fold-in-order : (A -> B -> B) -> B -> B
    -- fold-in-order {B} f b = foldFin' (\_ -> B) (f o fromIdx) b (maxFinFromNat num)

    module _ {B : Nat -> Set j} where
        -- open FinProp
        -- fold-in-order' : ({n : Nat} -> A -> B n -> B (1+ n)) -> B 0 -> B num
        -- fold-in-order' f b = foldFinNat (\{n} -> f {n} o fromIdx) b

module _ {n : Nat} where
    FinFinite : Finite (Fin {i} n)
    FinFinite .Finite.num = n
    FinFinite .Finite.iso = isomorphismRefl

identityMonad : Monad {i} id
identityMonad .Monad.rawMonad .RawMonad.return = id
identityMonad .Monad.rawMonad .RawMonad._>>=_ = flip _$_
identityMonad .Monad.isMonad .IsMonad.left-identity = refl
identityMonad .Monad.isMonad .IsMonad.right-identity = refl
identityMonad .Monad.isMonad .IsMonad.associative = refl


functionMonad : Monad {i} (Morphism A)
functionMonad .Monad.rawMonad .RawMonad.return = const
functionMonad .Monad.rawMonad .RawMonad._>>=_ f g a = g (f a) a
functionMonad .Monad.isMonad .IsMonad.left-identity = refl
functionMonad .Monad.isMonad .IsMonad.right-identity = refl
functionMonad .Monad.isMonad .IsMonad.associative = refl
