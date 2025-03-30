{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
-- {-# OPTIONS --safe #-} -- currently not safe due to indexed monoid postulate of lattice pre-order
module OwnPrelude.Data.ILatticeStates where

open import ASCIIPrelude.ASCIIPrelude 
open PolyZero
open PolyUnit
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Relation.IPreOrders
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.LatticeConstructions
open import OwnPrelude.Data.IConstrainedStates
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.MonadicVariables
open import OwnPrelude.Categorical.IMonads
open import OwnPrelude.Categorical.IMonadTs
open TupIdxIMonadT
open import OwnPrelude.Categorical.IMonoids

open ExistsSyntax

private
    variable
        cl ul ul' ujl il jl ol : Level
        n n' : Nat
        A B C X Y Z L : Set il
        F G M : Set il -> Set jl
        a b s x y z m : A
        f g : A -> B

-- \tagcode{ILatticeStates}

module ILatticeState
    {J : Set ujl}
    {M : J -> J -> Set (il ~U~ ul) -> Set (jl ~U~ ul)} 
    (monadM : IMonad M) where

    I = (Sigma (Set ul) BoundedSemilattice)
    S = fst

    -- \tagcode{BoundedSemilatticeInjectionRelation}

    record BoundedSemilatticeInjectionRelation
        (i i' : I)
        (x : S i) (y : S i') : Set ul where
        constructor <_,_>SIR
        open BoundedSemilattice using (semilattice)
        field
            bounded-semilattice-injection : BoundedSemilatticeInjection (snd i) (snd i')
        open BoundedSemilatticeInjection bounded-semilattice-injection public
        open BoundedSemilattice (snd i') renaming (_P_ to _P`$\subY$`_ ; _<>_ to _<>`$\subY$`_)
        field
            inj-directional : inf x P`$\subY$` y   


    module _ where
        open BoundedSemilatticeInjectionRelation
        open BoundedSemilattice

        SIRisPreOrder : IsIPreOrder {A = fst} BoundedSemilatticeInjectionRelation
        IsIPreOrder.reflexive SIRisPreOrder {i = (_ , bslX)} = < bounded-semilattice-injection-reflexive , BoundedSemilattice.reflexive bslX >SIR
        IsIPreOrder.transitive SIRisPreOrder {i = (_ , bslX)}{j = (_ , bslY)}{k = (_ , bslZ)} {a} {b} {c} sirXY sirYZ = 
            < bounded-semilattice-injection-transitive (bounded-semilattice-injection sirXY) (bounded-semilattice-injection sirYZ)
            , 
                inf sirYZ (inf sirXY a) <>`$\subZ$` c                           =< sym (inj-directional sirYZ) || inf sirYZ (inf sirXY a) <>`$\subZ$`_ >
                inf sirYZ (inf sirXY a) <>`$\subZ$` (inf sirYZ b <>`$\subZ$` c) =< associative bslZ >
                (inf sirYZ (inf sirXY a) <>`$\subZ$` inf sirYZ b) <>`$\subZ$` c =< sym (pres-inf sirYZ) || _<>`$\subZ$` c >
                inf sirYZ (inf sirXY a <>`$\subY$` b) <>`$\subZ$` c             =< inj-directional sirXY || (\h -> inf sirYZ h <>`$\subZ$` c) >
                inf sirYZ b <>`$\subZ$` c                                       =< inj-directional sirYZ >
                c                                                               qed 
            >SIR
            where
                open BoundedSemilattice bslX renaming (_<>_ to _<>`$\subX$`_)
                open BoundedSemilattice bslY renaming (_<>_ to _<>`$\subY$`_)
                open BoundedSemilattice bslZ renaming (_<>_ to _<>`$\subZ$`_)


    _-xi-_ : I -> I -> I
    (X , bslX) -xi- (Y , bslY) = (X -x- Y) , (bslX -xBSLx- bslY)
    
    module _ 
        {bslX : Sigma (Set ul) BoundedSemilattice}
        {bslY : Sigma (Set ul) BoundedSemilattice}  where
        open BoundedSemilattice

        SIRSndInjection : BoundedSemilatticeInjectionRelation bslY (bslX -xi- bslY) s (e (snd bslX) , s)
        SIRSndInjection = < semilatticeProductSndInjection , reflexive (snd (bslX -xi- bslY)) >SIR

        SIRFstInjection : BoundedSemilatticeInjectionRelation bslX (bslX -xi- bslY) s (s , e (snd bslY))
        SIRFstInjection = < semilatticeProductFstInjection , reflexive (snd (bslX -xi- bslY)) >SIR


    postulate semilatticeInjectionRelationIMonoid : IsIMonoid (IsIPreOrder.rawIMonoid SIRisPreOrder) 

    open ICBase -- {il = il ~U~ ul} BoundedSemilatticeInjectionRelation M
    open ICStateTMonad {il = il ~U~ ul} SIRisPreOrder monadM using (_>>P=_) renaming (monad to monadICStateT)
    monadIC = monadICStateT semilatticeInjectionRelationIMonoid
    open IMonad monadIC using () renaming (_>>=_ to _>>=C_ ; return to returnC)
    open IMonad monadM using () renaming (_>>=_ to _>>=M_ ; return to returnM)

    open LBVar renaming (read to readL; write to writeL)

    private variable
        i i' i'' : I
        j j' j'' : J

    ILState : (i j : I -x- J) -> Set (il ~U~ ul) -> Set (jl ~U~ ul)
    ILState = ICStateT BoundedSemilatticeInjectionRelation M

    IV : I -> Set (il ~U~ ul) -> Set (il ~U~ ul)
    IV (S , bsl) = LBVar S bsl

    module _ {X : Set (il ~U~ ul)} where
        open IMonad monadM
        open BoundedSemilattice
        open BoundedSemilatticeInjectionRelation

        -- \tagcode{IndexedNew}

        new : IV i' X -> ILState (i , j) ((i' -xi- i) , j) (IV (i' -xi- i) X) 
        new {i' = _ , bslX} {i = _ , bslS} v s = return ((e bslX , s) , SIRSndInjection , liftLBVar semilatticeProductFstInjection v)

    module VarAccess {X : Set (il ~U~ ul)}
        (readUnas : {A : Set (il ~U~ ul)}{i : I}{j j' : J} -> IV i X -> S i -> M j j' A)
        (readConf : {A : Set (il ~U~ ul)}{i : I}{j j' : J} -> IV i X -> S i -> M j j' A)
        (left-absorb-readUnas : forall {A B : Set (il ~U~ ul)}{i : I}{j j' j'' : J}{m : A -> M j' j'' B} {v : IV i X} {s : S i} -> 
            readUnas v s >>=M m === readUnas {j = j} v s)
        (left-absorb-readConf : forall {A B : Set (il ~U~ ul)}{i : I}{j j' j'' : J}{m : A -> M j' j'' B} {v : IV i X} {s : S i} -> 
            readConf v s >>=M m === readConf {j = j} v s) where
        open ICStateTMonadT.IMonadTProp {il = il ~U~ ul} SIRisPreOrder monadM semilatticeInjectionRelationIMonoid using (preserves-left-absorb; preserves-left-absorb-inside; monadT)
        open IMonadT monadT

        module _ {i : I} {j : J} where
            open IMonad monadM
            
            read : IV i X -> ILState (i , j) (i , j) X
            read v s = 
                unas: lift (readUnas v s) s
                conf: lift (readConf v s) s
                asm: (flip returnC s)
                (readL v s)

            open BoundedSemilattice (snd i)
            write : IV i X -> X -> ILState (i , j) (i , j) Unit
            write v x s = return (s <> writeL v x , < bounded-semilattice-injection-reflexive , directional >SIR , unit)

        module _ where
            open IMonad monadIC
            open BoundedSemilatticeInjectionRelation
            open ListOp

            _then-read_ : ILState (i , j) (i' , j') Y -> IV i X -> ILState (i , j) (i' , j') (Y -x- X)
            m then-read v = m >>P= \{(_ , _ , p) y -> read (liftLBVar (bounded-semilattice-injection p) v) >>= return o (y ,_)}

            _then-read'_ : ILState (i , j) (i' , j') Y -> IV i X -> ILState (i , j) (i' , j') X
            m then-read' v = snd <$> m then-read v

            liftVar : IV i X -> ILState (i , j) (i' , j) Y -> ILState (i , j) (i' , j) ((IV i' X) -x- Y)
            liftVar v m = m >>P= \{(_ , _ , p) y -> return (liftLBVar (bounded-semilattice-injection p) v , y)}

            liftVars : List (IV i X) -> ILState (i , j) (i' , j) Y -> ILState (i , j) (i' , j) (List (IV i' X) -x- Y)
            liftVars vs m = m >>P= \{(_ , _ , p) y -> return (map (liftLBVar (bounded-semilattice-injection p)) vs , y)}

            homVarProduct : (lst : List (exists[ i ] IV i X)) ->
                ILState (i , j) (foldr _-xi-_ i (map fst lst) , j) (List (IV (foldr _-xi-_ i (map fst lst)) X))
            homVarProduct [] = return []
            homVarProduct ((i' , vx) :: lst) = do
                vs <- homVarProduct lst
                (vs' , v)  <- liftVars vs (new vx)
                return (v :: vs')

            -- TODO: use this monad to formulate an arbitrary heterogenous product

