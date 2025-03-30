{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS --cubical #-}
module ChapterMonadicSolving.MonadicSolvingChapterPartII where

open import ASCIIPrelude.ASCIIPrelude hiding (module StateT)
open ExistsSyntax

open MonadTransformers
open Monads
open Applicatives
open Functors
open MonadPluses
open Alternatives

private
    variable
        h i j k k' l i' j' c : Level
        n n' : Nat
        A B X Y Z L S : Set i
        F G : Set i -> Set j
module Lattices where
    record IsEquivalence {A : Set i} (_===_ : A -> A -> Set j) : Set (i ~U~ j) where
        field
            reflexive : forall {a} -> a === a
            symmetric : forall {a b} -> a === b -> b === a
            transitive : forall {a b c} -> a === b -> b === c -> a === c

    module _ where
        open PropositionalEq
        propEqIsEquivalence : {A : Set i} -> IsEquivalence {i = i} {A = A} _===_
        IsEquivalence.reflexive propEqIsEquivalence = refl
        IsEquivalence.symmetric propEqIsEquivalence refl = refl
        IsEquivalence.transitive propEqIsEquivalence refl refl = refl

    module EQASCIIReasoning {A : Set i} {_===_ : A -> A -> Set l} (iseq : IsEquivalence _===_) where
        open IsEquivalence iseq

        -- infix 1 begin_
        -- begin_ : (a : A) -> a === a
        -- begin_ a = reflexive {a}

        infix 3 _qed
        _qed : (a : A) -> a === a
        _qed a = reflexive {a}

        infixr 2 step->
        step-> : forall {b c} -> (a : A) -> b === c -> a === b -> a === c
        step-> _ b=c a=b = transitive a=b b=c

        infixr 2 step->>
        step->> : forall {b} -> (a : A) -> a === b -> a === b
        step->> _ a=b = a=b

        syntax step-> a b=c a=b = a =< a=b > b=c
        syntax step->> a a=b = a =<> a=b

    record Semilattice (L : Set i) : Set i where
        infixr 20 _op_
        field
            _op_ : L -> L -> L
            
    record SemilatticeProp i j {L : Set i} 
        (sl : Semilattice L) : Set (i ~U~ lsuc j) where
        open Semilattice sl public
        infix 2 _===_
        field
            _===_ : L -> L -> Set j
            isEquivalence : IsEquivalence _===_
            comm : forall {x y} -> x op y === y op x
            idem : forall {x} -> x op x === x
            assoc : forall {x y z} -> (x op y) op z === x op (y op z)
            congruent : forall {w x y z} -> 
                x === z -> y === w -> x op y === z op w

        open IsEquivalence isEquivalence public

        congl : forall {x y z} -> x === z -> x op y === z op y
        congl x=z = congruent x=z reflexive

        congr : forall {x y z} -> y === z -> x op y === x op z
        congr y=z = congruent reflexive y=z

    record BoundedSemilattice (L : Set i) : Set i where
        field
            bound : L 
            semilattice : Semilattice L
        open Semilattice semilattice public

    record BoundedSemilatticeProp i j {L : Set i} (bsl : BoundedSemilattice L) : Set (i ~U~ lsuc j) where
        open BoundedSemilattice bsl public using (bound; semilattice)
        field
            semilatticeProp : SemilatticeProp i j semilattice
        open SemilatticeProp semilatticeProp public
        field
            leftId : forall {x} -> bound op x === x
            rightId : forall {x} -> x op bound === x

    record MeetSemilattice (L : Set i) : Set i where
        field
            semilattice : Semilattice L
        open Semilattice semilattice public renaming (_op_ to _/\_)

    record MeetSemilatticeProp i j {L : Set i} (msl : MeetSemilattice L) : Set (i ~U~ lsuc j) where
        open MeetSemilattice msl public
        field
            semilatticeProp : SemilatticeProp i j semilattice
        open SemilatticeProp semilatticeProp public

        _leq_ : L -> L -> Set j
        x leq y = x /\ y === y

        leq-refl : forall {x} -> x leq x
        leq-refl {x} = idem

        open EQASCIIReasoning isEquivalence

        leq-trans : forall {x y z} -> x leq y -> y leq z -> x leq z
        leq-trans {x} {y} {z} xly ylz = 
            xly :T: x /\ y === y [premise]
            ylz :T: y /\ z === z [premise]
            ------------------------------
            x /\ z        =< congr (symmetric ylz) > 
            x /\ (y /\ z) =< symmetric assoc >
            (x /\ y) /\ z =< congl xly >
            y /\ z        =< ylz >
            z             qed 

        increase : forall {x y} -> x leq (x /\ y)
        increase {x} {y} = 
            x /\ (x /\ y) =< symmetric assoc >
            (x /\ x) /\ y =< congl idem >
            x /\ y        qed

    record BoundedMeetSemilattice (L : Set i) : Set i where
        field
            boundedSemilattice : BoundedSemilattice L
        open BoundedSemilattice boundedSemilattice public renaming
            (_op_ to _/\_; bound to top)

open Lattices

module CVs (M : Set i -> Set j) where
    CV : Set i -> Set (i ~U~ j)
    CV X = X or M X

module Lenses where
    record Lens (A : Set i) (B : Set j) : Set (i ~U~ j) where
        field
            lget : A -> B
            lput : B -> A -> A

module Prisms where
    record Prism (A : Set i) (B : Set j) : Set (i ~U~ j) where
        field
            pget : A -> Maybe B
            pput : B -> A -> A

module MonadicVariables
    {M : Set i -> Set j}
    (mon : Monad {i} {j} M)
    {Z : Set i}
    -- {_===_ : {A : Set j} -> A -> A -> Set k} 
    {_===_ : M Z -> M Z -> Set k} 
    (iseq : IsEquivalence _===_) where
    open Monad mon
    open PolyUnit
    record MonVar {X : Set i} (read : M X) (write : X -> M (Unit {i})) : Set (lsuc i ~U~ j ~U~ k) where
        field
            distributive : forall {Y : Set i}{m' : M Y}{f : Y -> X -> M Z} ->
                (read >> m' >>= \y -> read >>= f y) === (read >>= \x -> m' >>= \y -> read >> f y x)
            read-write : forall {Y : Set i}{x : X}{m' : M Y}{f : Y -> X -> M Z} ->
                (write x >> m' >>= \y -> read >>= f y) === (write x >> m' >>= \y -> f y x)

module ThresholdAction
    {S : Set c}
    (msl : MeetSemilattice S)
    (msprop : MeetSemilatticeProp c l msl) where
    open MeetSemilatticeProp msprop hiding (_===_)
    open PolyUnit
    open PolyZero
    
    module TF {X : Set i} (_===_ : X -> X -> Set j) where
        _[_]Mab``leq_ : Maybe {i} X -> (P : X -> X -> Set j) -> Maybe {i} X -> Set j
        (just x) [ _P_ ]Mab``leq (just y) = x P y
        nothing  [  _  ]Mab``leq _  = Unit
        _ [ _ ]Mab``leq _ = Zero

        record ThresholdFunction (f : S -> Maybe X) : Set (c ~U~ l ~U~ j) where
            field
                increase-result-eq : forall {s s'} -> 
                    (s leq s') -> (f s [ _===_ ]Mab``leq f s')
        open Prisms
        open Prism
        record ThresholdPrism (p : Prism S X) : Set (c ~U~ l ~U~ j) where
            field
                tf : ThresholdFunction (pget p)                

module LatticeStateTransformer {S : Set c} (msl : MeetSemilattice {c} S) (mslProp : MeetSemilatticeProp c l msl) where
    open MeetSemilatticeProp mslProp renaming (_===_ to _=L=_)
    open PolyUnit
    
    prodlvl : (a b : Level) -> (A : Set a) -> (B : Set b) -> Set (a ~U~ b)
    prodlvl a b A B = _-x-_ {a} {b} A B

    syntax prodlvl a b A B = A - a x b - B

    module StateLatTTransformer (i j : Level) where
        private variable
            M : Set (i ~U~ c ~U~ l) -> Set j

        StateLatT : (Set (i ~U~ c ~U~ l) -> Set j) -> Set i -> Set (c ~U~ j)
        StateLatT M X = (s : S) -> M (exists[ s' of S ] s leq s' -x- X)

        module StateOp (app : Applicative {i ~U~ c ~U~ l} {j} M) where
            open Applicative app
            -- GetOp below
            module _ {X : Set i} where
                getS : (S -> X) -> StateLatT M X
                getS f s = return (_,_ {a = c} {b = l ~U~ i} s (leq-refl , f s))
                    -- return (s , leq-refl , f s)

                add : S -> StateLatT M (Unit {i})
                add s' s = return (_,_ {a = c} {b = l ~U~ i} (s /\ s') (increase , unit))
                    -- return (s /\ s' , increase , unit)

        module _ {X : Set i} (func : Functor {i ~U~ c ~U~ l} {j} M) where
            open Functor func
            open import ASCIIPrelude.CustomDefinitions
            open StateT
            removeProof : 
                (s : S) -> 
                exists[ s' of S ] s leq s' -x- X ->
                S -x- X
            removeProof s (s' , _ , x) = s' , x
            
            toStateT : StateLatT M X -> StateT S M X
            toStateT ma s = removeProof s <$> ma s
            -- no need to prove laws...new state transformer special old one. 

        module StateLatTFunctor (func : Functor {i ~U~ c ~U~ l} {j} M) where
            open Functor func renaming (_<$>_ to fmap)

            module _ {X Y : Set i} where
                mapResult : (s : S) -> (X -> Y) ->
                    exists[ s' of S ] s leq s' -x- X ->
                    exists[ s' of S ] s leq s' -x- Y
                mapResult s f (s' , p , a) = s' , p , f a

                _<$>_ : (X -> Y) -> StateLatT M X -> StateLatT M Y
                (f <$> sma) s = fmap (mapResult s f) (sma s)

        stateLatTFunctor : (Functor {i ~U~ c ~U~ l} {j} M) -> Functor {i} (StateLatT M)
        stateLatTFunctor func = record{StateLatTFunctor func}


        module StateLatTApplicative (mon : Monad {i ~U~ c ~U~ l} {j} M) where
            open Monad mon using (return ; _>>=_)

            rawFunctor = stateLatTFunctor (Monad.rawFunctor mon)

            module _ {X : Set i} where
                pure : X -> StateLatT M X
                pure x s = return (_,_ {a = c} {b = l ~U~ i} s (leq-refl , x))
                -- return (s , leq-refl , x)

            module _ {X Y : Set i} where
                _<*>_ : StateLatT M (X -> Y) -> StateLatT M X -> StateLatT M Y
                (mf <*> mx) s = do
                    (s' , p , f) <- mf s
                    (s'' , p' , x) <- mx s'
                    return (_,_ {a = c} {b = l ~U~ i} s'' (leq-trans p p' , f x))
                    -- return (s'' , leq-trans p p' , f x)

        stateLatTApplicative : (Monad {i ~U~ c ~U~ l} {j} M) -> Applicative {i} (StateLatT M)
        stateLatTApplicative mon = record{StateLatTApplicative mon}

        module StateLatTMonad (mon : Monad {i ~U~ c ~U~ l} {j} M) where
            rawApplicative = stateLatTApplicative mon

            module Bind {X Y : Set i} where
                open Monad mon

                _>>='_ : StateLatT M X -> (X -> StateLatT M Y) -> StateLatT M Y
                (mx >>=' fmy) s = do
                    (s' , p , x) <- mx s
                    (s'' , p' , y) <- fmy x s'
                    return (_,_ {a = c} {b = l ~U~ i} s'' (leq-trans p p' , y))
                    -- return (s'' , leq-trans p p' , y)
            open Bind public renaming (_>>='_ to _>>=_)

        stateLatTMonad : (Monad {i ~U~ c ~U~ l} {j} M) -> Monad {i} (StateLatT M)
        stateLatTMonad mon = record{StateLatTMonad mon}    

        module StateLatTMonadT (mon : Monad {i ~U~ c ~U~ l} {j} M) where
            rawMonad = stateLatTMonad mon

            module _ {X : Set i} where
                open Monad mon
                lift : M X -> StateLatT M X
                lift m s = do
                    x <- m
                    return (_,_ {a = c} {b = l ~U~ i} s (leq-refl , x))
                    -- return (s , leq-refl , x)

        stateLatTMonadT : (Monad {i ~U~ c ~U~ l} {j} M) -> MonadT {i} M (StateLatT M)
        stateLatTMonadT mon = record{StateLatTMonadT mon}

        module StateLatTMonadPlus (mp : MonadPlus {i ~U~ c ~U~ l} {j} M) where
            open MonadT {i} (stateLatTMonadT (MonadPlus.rawMonad mp))
            
            module _ {X : Set i} where
                open MonadPlus mp renaming (empty to emptyM; _<|>_ to _<|>M_)
                empty : StateLatT M X
                empty = lift emptyM

                _<|>_ : StateLatT M X -> StateLatT M X -> StateLatT M X
                (m1 <|> m2) s = (m1 s) <|>M (m2 s) 
                
            open import Effect.Monad
            open import Effect.Choice
            open import Effect.Empty

            rawEmpty : RawEmpty {i} (StateLatT M)
            RawEmpty.empty rawEmpty = empty

            rawMonadZero : RawMonadZero {i} (StateLatT M)
            RawMonadZero.rawMonad rawMonadZero = rawMonad
            RawMonadZero.rawEmpty rawMonadZero = rawEmpty

            rawChoice : RawChoice {i} (StateLatT M)
            RawChoice._<|>_ rawChoice = _<|>_

        stateLatTMonadPlus : 
            (MonadPlus {i ~U~ c ~U~ l} {j} M) -> 
            MonadPlus {i} (StateLatT M)
        stateLatTMonadPlus mp = record {StateLatTMonadPlus mp}

        module Laws {Z : Set i} {X : Set i} (mp : MonadPlus {i ~U~ c ~U~ l} {j} M) where 
            open PropositionalEq
            open ExistsSyntax
            
            module _ {M : Set (i ~U~ c ~U~ l) -> Set j} (mon : Monad M) where
                open Monad mon
                postulate
                    return-id : {X Y : Set (i ~U~ c ~U~ l)} {x : X} {f : X -> M Y} -> 
                        (return x >>= f) === (f x)
            
            module _ {A : Set k} where 
                open EQASCIIReasoning {A = A} propEqIsEquivalence public
            open ThresholdAction msl mslProp
            open TF {i = i} {X = X} _===_ 
            open MonadicVariables {i = i} {M = StateLatT M} (stateLatTMonad (MonadPlus.rawMonad mp)) {Z = Z} propEqIsEquivalence
            open StateOp (MonadPlus.rawApplicative mp)
            open MonadPlus {i} (stateLatTMonadPlus mp)
            open MonadT {i} (stateLatTMonadT (MonadPlus.rawMonad mp)) using (lift)
            open Prisms
            open Prism

            postulate 
                extensionality : {A : Set k} {B : A -> Set k'} {f g : (a : A) -> (B a)} -> 
                    ((a : A) -> f a === g a) -> f === g
                

            fail : {A : Set i} -> StateLatT M A
            fail = empty

            module ThresholdFuncToMonVar
                {p : Prism {i = c} {j = i} S X}
                (tp : ThresholdPrism p) where
                read : (S -> Maybe {i} X) -> StateLatT M X
                read f = getS f >>= fromMaybe fail o mapMaybe return
                    -- \{
                    --  (just x) -> return x
                    -- ; nothing -> fail
                    -- }

                open MonadPlus {i ~U~ c ~U~ l} mp using () renaming (
                    return to returnM; _>>=_ to _>>=M_; _>>_ to _>>M_; empty to emptyM)

                write : (X -> S -> S) -> X -> StateLatT M (Unit {i})
                write f x s = returnM (_,_ {a = c} {b = i ~U~ l} (s /\ (f x s)) (increase , unit {i}))
                    -- returnM ((s /\ (f x s)) , increase , unit) 

                -- read-prop : {f : (S -> Maybe {i} X)} -> 
                --     (s : S) -> (read f s === fail s) or (exists[ x of X ] (read f s === return x s))
                -- read-prop {f} s with f s
                -- ... | nothing = left $ 
                --     -- (returnM (s , leq-refl , nothing) >>=M {!!}) =<>
                --     (returnM (_,_ {a = c} {b = i ~U~ l} s (leq-refl , nothing)) >>=M _) =< return-id (MonadPlus.rawMonad mp) >
                --     {!  emptyM >>=M ? !} =< {!   !} >
                --     {!   !} qed
                -- ... | just x  = {!   !}

                -- -- (m >> m' >>= \y -> m >>= f y) === (m >>= \x -> m' >>= \y -> m >> f y x)
                -- mv : MonVar (read (pget p)) (write (pput p))
                -- MonadicVariables.MonVar.distributive mv {m'} {f} = extensionality helper
                --     where
                --         helper : (s : S) -> (read (pget p) >> m' >>= \y -> read (pget p) >>= f y) s === (read (pget p) >>= \x -> m' >>= \y -> read (pget p) >> f y x) s
                --         helper s with pget p s
                --         ... | nothing = 
                --                 -- (read (pget p) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --                 -- (read (pget p) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --                 -- (read (pget p) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --                 -- ((getS (pget p) >>= fromMaybe fail o mapMaybe return) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --                 -- ((return (pget p s) >>= fromMaybe fail o mapMaybe return) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --                 {!!} =< {!   !} >
                --                 {!!} qed
                --         ... | (just x)  = 
                --                 {!!} =< {!   !} >
                --                 {!!} qed
                --             -- (read (pget p) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --             -- ((getS (pget p) >>= fromMaybe fail o mapMaybe return) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --             -- -- (((\s -> returnM (s , leq-refl , pget p s)) >>= fromMaybe fail o mapMaybe return) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --             -- (((\s -> returnM (_,_ {a = c} {b = l ~U~ i} s (leq-refl , pget p s))) >>= fromMaybe fail o mapMaybe return) >> m' >>= \y -> read (pget p) >>= f y) s =<>
                --             -- {!!} =< {!   !} >
                --             -- {! !} qed
                -- MonadicVariables.MonVar.read-write mv = {!   !}


    module GetOp {M : Set (i ~U~ c ~U~ l) -> Set j} (app : Applicative {i ~U~ c ~U~ l} {j} M) where
        open Applicative app
        open StateLatTTransformer (i ~U~ c) j

        get : StateLatT M S
        get s = pure (_,_ {a = c} {b = l ~U~ i ~U~ c} s (_,_ {a = l} {b = c ~U~ i} leq-refl s))
            -- pure (s , leq-refl , s)

    module TLenses where
        -- TODO: we don't want the read of a specific lens, but of a 
        -- threshold function, which is a form of monadic state action!
        -- so...kind of a...threshold action 