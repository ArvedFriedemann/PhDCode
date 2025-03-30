{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-postfix #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.GeneralSolving where

open import ASCIIPrelude.ASCIIPrelude 
-- open NatOp
open PolyUnit
open PolyZero
open ListOp
open NatOp hiding (_^_) renaming (_leq_ to _leqB_)
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp
open import OwnPrelude.Equality
open import Level.Literals
-- open import Size renaming (↑_ to s^_ ; ∞ to inf ; _⊔ˢ_ to _~Us~_)

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.Perhaps
open import OwnPrelude.Relation.Functions

open ExistsSyntax

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d e f g h i j k l m n p q r s t u v w x y z fm i' j' k' l' A B C D E F G H K L M N O P Q R S T V W X Y Z alg Ctx  : ST

minimum : {A : Set i} -> (A -> Nat) -> Set i
minimum {A} f = exists[ a of A ] (forall {a' : A} -> f a leq f a')

getMin : {f : A -> Nat} -> minimum f -> A
getMin = fst

-- \tagcode{GeneralSolving}

module PerhapsSolver where

    record CoList (A : Set i) : Set i where
        constructor CL
        coinductive
        field
            next : (A -x- CoList A) -+- Unit {i}
    open CoList

    pattern nil x = right x --TODO: check if you can write nil = right unit
    pattern cons x xs = left (x , xs)

    []co : CoList A
    next []co = nil unit

    _::co_ : A -> CoList A -> CoList A
    next (a ::co lst) = cons a lst

    intersperse : CoList A -> CoList A -> CoList A
    next (intersperse xs ys) with next xs
    ... | nil unit = next ys
    ... | cons x xs' = cons x (intersperse  ys xs')

    finInterweave : List (CoList A) -> CoList A
    finInterweave = foldr intersperse []co

    prefix : List A -> CoList A -> CoList A
    next (prefix [] cl) = next cl
    next (prefix (x :: xs) cl) = cons x (prefix xs cl)

    -- coConcat : CoList (CoList A) -> CoList A
    -- next (coConcat cl) with next cl
    -- ... | nil unit = nil unit
    -- ... | cons x xs with next x
    -- ... | cons x' xs' = cons x' (coConcat (xs' ::co xs))
    -- ... | nil unit = {! coConcat xs  !} --this needs ctd to work. If the coList continues to contain empty list, there will never be a next element, but we will also never know when to stop with []co

    downtick : List (Perhaps X) -> X -+- List (Perhaps X)
    downtick lst with getVals lst
    ... | [] = right (getCtd lst)
    ... | x :: xs = left x

    -- end versions might not be needed because during dovetailing, some value will be chosen regardless. This is just to get rid of values that we know will not terminate
    downtickEnd : List (Perhaps (Maybe X)) -> X -+- List (Perhaps (Maybe X))
    downtickEnd lst with (concatMap (fromSum maybeToList (const []) o val?) lst) --TODO: cleanup with getVals
    ... | [] = right (concatMap (fromSum (const []) [_] o val?) lst)
    ... | x :: xs = left x
    
    dovetailChoose : CoList (Perhaps X) -> Perhaps X
    dovetailChoose = dovetailChoose' []
        where
            dovetailChoose' : List (Perhaps X) -> CoList (Perhaps X) -> Perhaps X
            val? (dovetailChoose' pre lst) with downtick pre
            ... | val x    = val x
            ... | ctd pre' with next lst
            ... | nil _     = ctd noValue 
            ... | cons x xs = ctd (dovetailChoose' (pre' ++ [ x ]) xs)

    dovetailChooseEnd : CoList (Perhaps (Maybe X)) -> Perhaps (Maybe X)
    dovetailChooseEnd = dovetailChooseEnd' []
        where
            dovetailChooseEnd' : List (Perhaps (Maybe X)) -> CoList (Perhaps (Maybe X)) -> Perhaps (Maybe X)
            val? (dovetailChooseEnd' pre lst) with downtickEnd pre
            ... | val x    = val (just x)
            ... | ctd pre' with next lst
            ... | nil _     = val nothing
            ... | cons x xs = ctd (dovetailChooseEnd' (pre' ++ [ x ]) xs)

    Enumeration : Set i -> Set i
    Enumeration = CoList o Perhaps
    --still needs the "complete" token

    mapEnum : (A -> B) -> Enumeration A -> Enumeration B
    next (mapEnum f enum) with next enum
    ... | nil _     = nil unit
    ... | cons x xs = cons (mapPerhaps f x) (mapEnum f xs)

    mapDepEnum : ((a : A) -> B a) -> Enumeration A -> Enumeration (Sigma A B)
    next (mapDepEnum f enum) with next enum
    ... | nil _     = nil unit
    ... | cons x xs = cons (mapDepPerhaps f x) (mapDepEnum f xs)






module InitialExample  where
    record SolvingMonad {i} (M : Set i -> Set i) (mon : Monad M) : Set (lsuc i) where
        field
            solve : (A : Set i) -> M A
            -- interpret : M A -> Maybe A -- TODO: Should probably be into some general category, left open
            -- MT : Set
            -- toMeta : M A -> MT -- could be used to get around universe polymorphism issue...
            _#rt : {A : Set i} -> A -> Nat
        open Monad mon public

        Interpretation : (Set i -> Set k) -> Set (lsuc i ~U~ k)
        Interpretation P = forall {A} -> M A -> P A

        -- this could be assumed to express the computational steps for computation (Maybe this should take the interpretation for the computation into consideration? Different interpretations might have different compute times)
        NatInterp : Set (lsuc i)
        NatInterp = Interpretation (\_ -> Nat)

        solveMin : forall (_~_ : M A -> M A -> Set i) -> NatInterp -> M A -> M A
        solveMin {A} _~_ toNat m = solve (minimum {A = exists[ m' of M A ] (m ~ m')} (toNat o fst)) >>= fst o getMin


        --TODO: It could ask itself to make a computation faster
        -- Main problem to solve: querying itself also takes time, has to be taken into consideration (this will recurse, so this will need treatment of cutting computation short on timeout)
        -- It can use a meta theory to avoid predicativity issues (Make statements about itself in the meta theory)

    module SAT-Example {M : forall {i} -> Set i -> Set i} {mon : forall {i} -> Monad (M {i})} {sm : forall {i} -> SolvingMonad {i} (M {i}) (mon {i})} where
        module _ {i} where
            open SolvingMonad (sm {i}) public

        funN : (n : Nat) (A : Set k) (B : Set k) -> Set k
        funN 0 A B = B
        funN (1+ n) A B = A -> (funN n A B)

        _^_ : Set k -> Nat -> Set k
        A ^ 0 = Unit
        A ^ (1+ n) = A -x- A ^ n

        _$n_ : funN n A B -> A ^ n -> B
        _$n_ {n = 0}    b unit      = b
        _$n_ {n = 1+ n} f (a , atp) = f a $n atp

        SAT-Solve : (f : funN n Bool Bool) -> M (Sigma (Bool ^ n) (\b -> f $n b === true))
        SAT-Solve {n} f = solve (Sigma (Bool ^ n) (\b -> f $n b === true))

module _ where

    module ImpredicativeSolver {i} where
        -- TODO: this will make proving statements about the solvers themselves complicated due to to the universe hierarchy
        Solver : Set (lsuc i)
        Solver = (X : Set i) -> Perhaps X 

        semi-complete : Solver -> Set (lsuc i)
        semi-complete solver = forall {X} (x : X) -> hasAnyVal (solver X)

    module UniverseSolver where
        record Universe {i} : Set (lsuc i) where
            field
                U : Set
                [_]U : U -> Set i
        
        module _ (Univ : Universe {i}) where
            open Universe Univ

            -- \tagcode{SolverType}
            
            Solver : Set i
            Solver = (X : U) -> Perhaps [ X ]U

            -- \tagcode{SemiCompleteness}

            semi-complete : Solver -> Set i
            semi-complete solver = forall {X : U} (x : [ X ]U) -> hasAnyVal (solver X)

            module Implementation 
                {M : Set i -> Set i}
                (coalg  : forall {X} -> M [ X ]U -> M [ X ]U -+- M [ X ]U)
                (seed   : forall {X} -> M [ X ]U)
                (interp : forall {X} -> M [ X ]U -> [ X ]U) where

                solve : Solver
                solve X = mapPerhaps interp (coFold coalg seed) 

                coAlgFromState : (A -> A -x- Maybe A) -> (A -> A -+- A)
                coAlgFromState mMa a with mMa a
                ... | a' , just x  = val x
                ... | a' , nothing = ctd a'

                stateFromCoAlg : (A -> A -+- A) -> (A -> A -x- Maybe A)
                stateFromCoAlg coAlg a with coAlg a
                ... | val x  = a , just x
                ... | ctd a' = a' , nothing

                coAlgFromStateT : (A -> Maybe (A -x- A)) -> (A -> A -+- A)
                coAlgFromStateT mMa a with mMa a
                ... | just (a' , x) = val x
                ... | nothing       = ctd a

                fail : forall {X : Set i} -> (A -> A -x- Maybe X)
                fail a = a , nothing


            module _ (SemSU : Sigma Solver semi-complete inn Image [_]U) where
                Sigma-Solver-semi-complete = fst SemSU

                -- \tagcode{CreateSolver}

                createSolver : Sigma Solver semi-complete -> Perhaps [ Sigma-Solver-semi-complete ]U
                createSolver (solve , semi-c) = solve Sigma-Solver-semi-complete

                module _ 
                    (measure : Solver -> Nat)  --In reality, this would be some type with a (partial) order defined on it
                    (MesU    : forall (solve : Solver) -> ((exists[ solve' of Solver ] (measure solve leq measure solve')) inn Image [_]U)) -- should be < and not leq
                    where

                    -- \tagcode{ImproveSolver}

                    improveSolver : (solve : Solver) -> Perhaps [ fst (MesU solve) ]U
                    improveSolver solve = solve (fst (MesU solve))

                    --TODO: Maximise improvement. The improvement above may still get stuck on local maxima
                    -- maybe also search for a proof of going towards the global maximum
                    -- also...search for improvement of improver

                    





module PerhapsTrees where

    data PTreeF (A : Set i) (B : Set j) : Set (i ~U~ j) where
        ptval : A -> PTreeF A B
        ptctd : B -> PTreeF A B
        _<,>_ : (a : B) -> (b : B) -> PTreeF A B 

    record CoPTree (A : Set i) : Set i where
       coinductive
       field
            next : PTreeF A (CoPTree A)
    open CoPTree

    emptyTree : CoPTree A
    next emptyTree = ptctd emptyTree

    getValsCoPT : List (CoPTree A) -> List A
    getValsCoPT = concatMap (help o next)
        where 
            help : PTreeF A (CoPTree A) -> List A
            help (ptval x) = [ x ]
            help _         = []

    getSuccNodes : List (CoPTree A) -> List (CoPTree A)
    getSuccNodes = concatMap (help o next)
        where
            help : PTreeF A (CoPTree A) -> List (CoPTree A)
            help (ptval x) = [] 
            help (ptctd t) = [ t ] 
            help (x <,> y) = x :: y :: []

    _<|>_ : CoPTree A -> CoPTree A -> CoPTree A
    next (a <|> b) = a <,> b

    mapCoPTree : (A -> B) -> CoPTree A -> CoPTree B
    next (mapCoPTree f t) with next t 
    ... | ptval x  = ptval (f x)
    ... | ptctd t' = ptctd (mapCoPTree f t')
    ... | a <,> b  = (mapCoPTree f a) <,> (mapCoPTree f b)

    mapCoPTreePi : ((a : A) -> B a) -> CoPTree A -> CoPTree (Sigma A B)
    mapCoPTreePi f = mapCoPTree (\x -> x , f x) 

    joinCoPTree : CoPTree (CoPTree A) -> CoPTree A
    next (joinCoPTree t) with next t 
    ... | ptval x  = next x
    ... | ptctd t' = ptctd (joinCoPTree t')
    ... | a <,> b  = (joinCoPTree a) <,> (joinCoPTree b)

    _>>=CPT_ : CoPTree A -> (A -> CoPTree B) -> CoPTree B
    ma >>=CPT fmb = joinCoPTree (mapCoPTree fmb ma)

    --TODO: write monadically
    _>>=CPTSig_ : CoPTree A -> ((a : A) -> CoPTree (B a)) -> CoPTree (Sigma A B)
    ma >>=CPTSig fmb = mapCoPTreePi fmb ma >>=CPT \{(a , mb) -> mapCoPTree (a ,_) mb }

    -- TODO: Monad

    record StateStrategy (S : Set i) (X : Set j) : Set (i ~U~ j) where
        field
            initialNode : CoPTree X -> S
            delta   : S -> S
            hasVal? : S -> Maybe X

    module _ (strat : StateStrategy S X) where
        open StateStrategy strat
        
        chooseStratState : S -> Perhaps X
        val? (chooseStratState s) with hasVal? s
        ... | just x = val x
        ... | nothing = ctd (chooseStratState (delta s))
        
        chooseStrat : CoPTree X -> Perhaps X
        chooseStrat t = chooseStratState (initialNode t)


    BFS-strategy : StateStrategy (List (CoPTree X)) X 
    StateStrategy.initialNode BFS-strategy a = a :: []
    StateStrategy.delta BFS-strategy         = getSuccNodes
    StateStrategy.hasVal? BFS-strategy       = head o getValsCoPT

    -- Problem with this DFS is that branches never fail, so unless failing branches are removed, this does not even do any search at all
    DFS-strategy : StateStrategy (List (CoPTree X)) X 
    StateStrategy.initialNode DFS-strategy a = a :: []
    StateStrategy.delta DFS-strategy [] = []
    StateStrategy.delta DFS-strategy (x :: lst) with next x
    ... | ptval x' = lst
    ... | ptctd t  = t :: lst
    ... | a <,> b  = a :: b :: lst 
    StateStrategy.hasVal? DFS-strategy = head o getValsCoPT
