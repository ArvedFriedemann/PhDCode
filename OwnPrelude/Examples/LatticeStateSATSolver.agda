{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
-- {-# OPTIONS --safe #-} -- currently unsafe due to indexed monoid postulate for lattice pre-order
{-# OPTIONS --warning=noUnsupportedIndexedMatch #-}
module OwnPrelude.Examples.LatticeStateSATSolver where

open import ASCIIPrelude.ASCIIPrelude
open ListOp using (length; take)
open BoolOp
    renaming 
    ( _andBool_ to _and``Bool_
    ; _orBool_  to _or``Bool_
    ; notBool to not``Bool )
open PolyZero
open PolyUnit
{-# DISPLAY liftL BaseUnit.unit = unit #-}
open StringOpQualified using (_=S=_)
open import OwnPrelude.Equality
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.LatticeStates
open import OwnPrelude.Data.TrivialLattices
open import OwnPrelude.Data.BooleanInstances
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.ListCategorical
open import OwnPrelude.Data.ErrorT using (ErrorT)
open import OwnPrelude.Data.ErrorT as ErrorT
open import OwnPrelude.Data.NTuples
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.LatticeConstructions
open import OwnPrelude.Categorical.MonadFailAlternatives
open import OwnPrelude.Categorical.Alternatives
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadErrors
private
    _^_ = NTup
{-# DISPLAY _`$\back^_$` A n = A ^ n #-}

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u e : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G M : Set i -> Set j
        a b x y z m : A
        f g : A -> B

-- \tagcode{SATSolvingExample}

infixr 10 _/\SF_
infixr  9 _\/SF_
data SATFormOver (V : Set i) : Set i where
    trueSF  : SATFormOver V
    falseSF : SATFormOver V
    varSF   : V -> SATFormOver V
    notSF   : SATFormOver V -> SATFormOver V
    _/\SF_  : SATFormOver V -> SATFormOver V -> SATFormOver V
    _\/SF_  : SATFormOver V -> SATFormOver V -> SATFormOver V

data SATFormOverF (R : Set i) : Set i where
    trueSFF  : SATFormOverF R
    falseSFF : SATFormOverF R
    notSFF   : R -> SATFormOverF R
    _/\SFF_  : R -> R -> SATFormOverF R
    _\/SFF_  : R -> R -> SATFormOverF R

module _ {V : Set i} where
    -- needs variable extraction...
    -- foldSF : (SATFormOverF V X -> X) -> SATFormOver V -> X
    -- foldSF alg trueSF     = alg trueSFF
    -- foldSF alg falseSF    = alg falseSFF
    -- foldSF alg (notSF a)  = alg (notSFF (foldSF alg a))
    -- foldSF alg (a /\SF b) = alg ((foldSF alg a) /\SFF (foldSF alg b))
    -- foldSF alg (a \/SF b) = alg ((foldSF alg a) \/SFF (foldSF alg b))


infixr 7 _=>SF_
_=>SF_ : {V : Set i} -> SATFormOver V -> SATFormOver V -> SATFormOver V
a =>SF b = notSF a \/SF b

infixr 8 _<=>SF_
_<=>SF_ : {V : Set i} -> SATFormOver V -> SATFormOver V -> SATFormOver V
a <=>SF b = (a =>SF b) /\SF (b =>SF a)


module _ where
    open import OwnPrelude.Data.ListCategorical
    open Monad {lzero} listMonad
    open ListOp

    _imageOf_ : (Bool -> Bool) -> Bool -> List Bool
    f imageOf aim = do
        x <- true :: false :: []
        guard (f x == aim)
        return x

    filterImage : Maybe Bool -> List Bool -> List Bool
    filterImage (just a) = filter (_== a)
    filterImage nothing  = id

    filterImage' : Maybe Bool -> List Bool -> List (Maybe Bool)
    filterImage' (just a) = map (\_ -> nothing)
    filterImage' nothing  = map just

    minimize : List (Maybe Bool) -> List (Maybe Bool)
    minimize (just true  :: just false :: []) = nothing :: []
    minimize (just false :: just true  :: []) = nothing :: []
    minimize = id
    
    _imageOf2_ : (Bool -> Bool -> Bool) -> Bool -> List (Bool -x- Bool)
    f imageOf2 aim = do
        x <- true :: false :: []
        y <- true :: false :: []
        guard (f x y == aim)
        return (x , y)

    filterImage2 : Maybe Bool -> Maybe Bool -> List (Bool -x- Bool) -> List (Bool -x- Bool)
    filterImage2 (just a) (just b) = filter (\{(x , y) -> x == a and``Bool y == b})
    filterImage2 (just a)  nothing = filter (\{(x , y) -> x == a})
    filterImage2  nothing (just b) = filter (\{(x , y) -> y == b})
    filterImage2  nothing  nothing = id

    filterImage2' : Maybe Bool -> Maybe Bool -> List (Bool -x- Bool) -> List (Maybe Bool -x- Maybe Bool)
    filterImage2' (just a) (just b) = map (\{(_ , _) -> (nothing , nothing)}) o filter (\{(x , y) -> x == a and``Bool y == b})
    filterImage2' (just a)  nothing = map (\{(_ , y) -> (nothing , just y )}) o filter (\{(x , y) -> x == a})
    filterImage2'  nothing (just b) = map (\{(x , _) -> (just x  , nothing)}) o filter (\{(x , y) -> y == b})
    filterImage2'  nothing  nothing = map (\{(x , y) -> (just x  , just y)})

    _=Mab=_ : Maybe Bool -> Maybe Bool -> Bool
    nothing =Mab= nothing = true
    (just a) =Mab= (just b) = a == b
    _ =Mab= _ = false

    _/Mab=_ : Maybe Bool -> Maybe Bool -> Bool
    a /Mab= b = not``Bool (a =Mab= b)

    minimize2 : List (Maybe Bool -x- Maybe Bool) -> List (Maybe Bool -x- Maybe Bool)
    minimize2 lst = 
        ( AddDon'tCareClauseIfNecessary
        o AddInvertsToDon'tCare
        o filterEmpty
        o QuineMcClusky)
        lst
        
        where
            AddDon'tCareClauseIfNecessary = (\ lst' -> 
                if (not``Bool (null lst)) and``Bool null lst' then (nothing , nothing) :: [] else lst')
            AddInvertsToDon'tCare = flip foldr [] (\{(a , b) lst' -> 
                    (a , b) ::
                    map (\{(a' , b') -> 
                        fromMaybe (mapMaybe not``Bool a) (mapMaybe just a') , 
                        fromMaybe (mapMaybe not``Bool b) (mapMaybe just b')}) lst'
                })
            filterEmpty = filter (\{(a , b) -> not``Bool (is-nothing a and``Bool is-nothing b)})
            QuineMcClusky = \lst -> map (
                \{(a , b) -> 
                    (if any (\{(a' , b') -> (a' =Mab= (mapMaybe not``Bool a)) and``Bool (b =Mab= b')}) lst then nothing else a) ,
                    (if any (\{(a' , b') -> (b' =Mab= (mapMaybe not``Bool b)) and``Bool (a =Mab= a')}) lst then nothing else b)})
                    lst
    
    -- (\ lst' -> map (
    --     \{(a , b) -> 
    --         (if any (\{(a' , b') -> (a' =Mab= (mapMaybe not``Bool a)) and``Bool (b =Mab= b')}) lst' then nothing else a) ,
    --         (if any (\{(a' , b') -> (b' =Mab= (mapMaybe not``Bool b)) and``Bool (a =Mab= a')}) lst' then nothing else b)}) lst') $

    -- minimize2 (filterImage2' (just true) nothing $ _or``Bool_ imageOf2 true)
    -- minimize2 (filterImage2' (just false) nothing $ _or``Bool_ imageOf2 true)
    -- minimize2 (filterImage2' nothing (just true)  $ _or``Bool_ imageOf2 true)
    -- minimize2 (filterImage2' nothing (just false)  $ _or``Bool_ imageOf2 true)
    -- minimize2 (filterImage2' nothing nothing $ _or``Bool_ imageOf2 true)

    -- minimize2 (filterImage2' (just true) nothing $ _and``Bool_ imageOf2 false)
    -- minimize2 (filterImage2' (just false) nothing $ _and``Bool_ imageOf2 false)
    -- minimize2 (filterImage2' nothing (just true)  $ _and``Bool_ imageOf2 false)
    -- minimize2 (filterImage2' nothing (just false)  $ _and``Bool_ imageOf2 false)
    -- minimize2 (filterImage2' nothing nothing $ _and``Bool_ imageOf2 false)


module SAT-Solver 
    {S : Set}
    (bsl : BoundedSemilattice S) 
    {M : Set -> Set}
    {monad : Monad M}
    (mfa : MonadFailAlternativeOver monad)
    {Err : Set e}
    (me : MonadErrorOver monad Err) where
    open LatticeState bsl monad public
    open Exports public
    open ExportMonadFailAlternative {Err = Err} mfa public
    open ExportMonadError me public
    module MFA = MonadFailAlternativeOver mfa
    module ME = MonadErrorOver me
    open Monad monad using () renaming (_>>=_ to _>>=M_ ; return to returnM)

    module Solver
        (readUnas : {A : Set} -> V Bool -> S -> M A)
        (readConf : {A : Set} -> {- V Bool -> S -> -} M A)
        (left-absorb-readUnas : forall {A B : Set} {m : A -> M B} {v s} -> 
            readUnas v s >>=M m === readUnas v s)
        (left-absorb-readConf : forall {A B : Set} {m : A -> M B} -> 
            readConf >>=M m === readConf)
        (_=e=_ : Err -> Err -> Bool)
        (unasError : Err) where

        open VarAccess readUnas (\_ _ -> readConf) left-absorb-readUnas left-absorb-readConf public
        private
            catchUnas : LState X -> LState X -> LState X
            catchUnas m1 m2 = catch m1 (\s -> if s =e= unasError then m2 else throw s)
                        
        safeRead : LState X -> LState (Maybe X)
        safeRead m = catchUnas (just <$> m) (return nothing)

        branchingRead : V Bool -> LState Bool
        branchingRead v = catchUnas (read v) ((write v true <|> write v false) >> read v)

        -- \tagcode{AssignmentAlg}

        assignmentAlg : SATFormOverF Bool -> Bool
        assignmentAlg trueSFF     = true
        assignmentAlg falseSFF    = false
        assignmentAlg (notSFF a)  = not``Bool a
        assignmentAlg (a /\SFF b) = a and``Bool b
        assignmentAlg (a \/SFF b) = a or``Bool  b

        -- make one version for evaluation and one version for solving!
        -- fold``Bool``LState : (V Bool -> LState Bool) -> (SATFormOverF Bool -> Bool) -> SATFormOver (V Bool) -> LState Bool
        -- fold``Bool``LState rd alg trueSF = return (alg trueSFF)
        -- fold``Bool``LState rd alg falseSF = return (alg falseSFF)
        -- fold``Bool``LState rd alg (varSF x) = rd x
        -- fold``Bool``LState rd alg (notSF a) = (| (alg o notSFF) (fold``Bool``LState rd alg a) |)
        -- fold``Bool``LState rd alg (a /\SF b) = (| alg (| (fold``Bool``LState rd alg a) /\SFF (fold``Bool``LState rd alg b) |) |)
        -- fold``Bool``LState rd alg (a \/SF b) = (| alg (| (fold``Bool``LState rd alg a) \/SFF (fold``Bool``LState rd alg b) |) |)

        irrelevant : (Bool -> Bool) -> Bool
        irrelevant f = f true == f false

        irrelevant2 : (Bool -> Bool -> Bool) -> Bool
        irrelevant2 f = 
            f true  true  == f true  false and``Bool
            f true  false == f false true  and``Bool
            f false true  == f false false and``Bool
            f false false == f true  true

        safeApplyFunc``Bool : (Bool -> Bool) -> LState Bool -> LState Bool
        safeApplyFunc``Bool f a = do
            a? <- safeRead a
            case a? of 
                \{ (just x) -> return (f x)
                 ;  nothing -> if irrelevant f
                        then return (f true)
                        else (| f a |) }

        safeApplyFunc2``Bool : (Bool -> Bool -> Bool) -> LState Bool -> LState Bool -> LState Bool
        safeApplyFunc2``Bool f a b = do
            a? <- safeRead a
            b? <- safeRead b
            case (a? , b?) of 
                \{ (just x , just y)   -> return (f x y)
                ;  (just x , nothing)  -> if irrelevant (f x)
                        then return (f x true)
                        else (| (f x) b |)
                ;  (nothing , just x)  -> if irrelevant (\y -> f y x)
                        then return (f true x)
                        else (| f a (| x |) |)
                ;  (nothing , nothing) -> if irrelevant2 f
                        then return (f true true)
                        else (| f a b |) }
            
        -- in general: Bool could be any X
        foldLS : (SATFormOverF Bool -> Bool) -> SATFormOver (V Bool) -> LState Bool
        foldLS alg trueSF      = (| (alg trueSFF) |)
        foldLS alg falseSF     = (| (alg trueSFF) |)
        foldLS alg (varSF v)   = read v
        foldLS alg (notSF a)   = (| (alg o notSFF) (foldLS alg a) |)
        foldLS alg (a /\SF b)  = (| alg (| (foldLS alg a) /\SFF (foldLS alg b) |) |)
        foldLS alg (a \/SF b)  = (| alg (| (foldLS alg a) \/SFF (foldLS alg b) |) |)

        fold``Bool``LState : (V Bool -> LState Bool) -> (SATFormOverF Bool -> Bool) -> SATFormOver (V Bool) -> LState Bool
        fold``Bool``LState rd alg trueSF     = (| (alg trueSFF)  |)
        fold``Bool``LState rd alg falseSF    = (| (alg falseSFF) |)
        fold``Bool``LState rd alg (varSF v)  = rd v
        fold``Bool``LState rd alg (notSF a)  = 
            safeApplyFunc``Bool 
            (alg o notSFF) 
            (fold``Bool``LState rd alg a)
        fold``Bool``LState rd alg (a /\SF b) = 
            safeApplyFunc2``Bool (\x y -> alg (x /\SFF y)) 
            (fold``Bool``LState rd alg a) 
            (fold``Bool``LState rd alg b)
        fold``Bool``LState rd alg (a \/SF b) = 
            safeApplyFunc2``Bool (\x y -> alg (x \/SFF y)) 
            (fold``Bool``LState rd alg a) 
            (fold``Bool``LState rd alg b)

        disjunctMap' : (X -> LState Unit) -> List X -> LState Unit
        disjunctMap' f [] = lift readConf
        disjunctMap' f (x :: []) = f x
        disjunctMap' f (x :: xs) = f x <|> disjunctMap' f xs

        whenJust : Maybe A -> (A -> LState Unit) -> LState Unit
        whenJust (just a) f = f a
        whenJust nothing  f = return unit

        -- naive
        solve``Bool``LStateNaive : (V Bool -> Bool -> LState Unit) -> (SATFormOverF Bool -> Bool) -> SATFormOver (V Bool) -> Bool -> LState Unit
        solve``Bool``LStateNaive wrt alg trueSF     aim = unless' (alg trueSFF  == aim) (lift readConf)
        solve``Bool``LStateNaive wrt alg falseSF    aim = unless' (alg falseSFF == aim) (lift readConf)
        solve``Bool``LStateNaive wrt alg (varSF v)  aim = wrt v aim
        solve``Bool``LStateNaive wrt alg (notSF a)  aim = do
            a? <- safeRead (fold``Bool``LState read alg a)
            disjunctMap' (solve``Bool``LStateNaive wrt alg a) (filterImage a? ((alg o notSFF) imageOf aim))
        solve``Bool``LStateNaive wrt alg (a /\SF b) aim = do
            a? <- safeRead (fold``Bool``LState read alg a)
            b? <- safeRead (fold``Bool``LState read alg b)
            disjunctMap' 
                (\{(a-aim , b-aim) -> solve``Bool``LStateNaive wrt alg a a-aim >> solve``Bool``LStateNaive wrt alg b b-aim})
                (filterImage2 a? b? ((\a b -> alg (a /\SFF b)) imageOf2 aim))
        solve``Bool``LStateNaive wrt alg (a \/SF b) aim = do
            a? <- safeRead (fold``Bool``LState read alg a)
            b? <- safeRead (fold``Bool``LState read alg b)
            disjunctMap' 
                (\{(a-aim , b-aim) -> solve``Bool``LStateNaive wrt alg a a-aim >> solve``Bool``LStateNaive wrt alg b b-aim})
                (filterImage2 a? b? ((\a b -> alg (a \/SFF b)) imageOf2 aim))

        solve``Bool``LState : (V Bool -> Bool -> LState Unit) -> (SATFormOverF Bool -> Bool) -> SATFormOver (V Bool) -> Bool -> LState Unit
        solve``Bool``LState wrt alg trueSF     aim = unless' (alg trueSFF  == aim) (lift readConf)
        solve``Bool``LState wrt alg falseSF    aim = unless' (alg falseSFF == aim) (lift readConf)
        solve``Bool``LState wrt alg (varSF v)  aim = wrt v aim
        solve``Bool``LState wrt alg (notSF a)  aim = do
            a? <- safeRead (fold``Bool``LState read alg a)
            disjunctMap' 
                (\a-aim -> whenJust a-aim (solve``Bool``LState wrt alg a)) 
                (minimize $ filterImage' a? ((alg o notSFF) imageOf aim))

        solve``Bool``LState wrt alg (a /\SF b) aim = do
            a? <- safeRead (fold``Bool``LState read alg a)
            b? <- safeRead (fold``Bool``LState read alg b)
            disjunctMap' 
                (\{(a-aim , b-aim) -> do 
                    whenJust a-aim (solve``Bool``LState wrt alg a) 
                    whenJust b-aim (solve``Bool``LState wrt alg b) })
                (minimize2 $ filterImage2' a? b? $ (\a b -> alg (a /\SFF b)) imageOf2 aim)

        solve``Bool``LState wrt alg (a \/SF b) aim = do
            a? <- safeRead (fold``Bool``LState read alg a)
            b? <- safeRead (fold``Bool``LState read alg b)
            disjunctMap' 
                (\{(a-aim , b-aim) -> do 
                    whenJust a-aim (solve``Bool``LState wrt alg a) 
                    whenJust b-aim (solve``Bool``LState wrt alg b) })
                (minimize2 $ filterImage2' a? b? $ (\a b -> alg (a \/SFF b)) imageOf2 aim)

        -- \tagcode{assignmentOf}

        assignmentOf : SATFormOver (V Bool) -> LState Bool
        assignmentOf trueSF  = return true
        assignmentOf falseSF = return false
        assignmentOf (varSF v) = read v     -- we could branch here for value
        assignmentOf (notSF form) = (| not``Bool (assignmentOf form) |)
        assignmentOf (a /\SF b) = (| (assignmentOf a) and``Bool (assignmentOf b) |) -- TODO: lazy read?
        assignmentOf (a \/SF b) = (| (assignmentOf a) or``Bool  (assignmentOf b) |)

        assignmentOfSafeNaive : SATFormOver (V Bool) -> LState Bool
        assignmentOfSafeNaive trueSF  = return true
        assignmentOfSafeNaive falseSF = return false
        assignmentOfSafeNaive (varSF v) = read v
        assignmentOfSafeNaive (notSF form) = (| not``Bool (assignmentOfSafeNaive form) |)
        assignmentOfSafeNaive (a /\SF b) = do
            a? <- safeRead (assignmentOfSafeNaive a)
            case a? of 
                \{ (just false) -> return false
                ;  _            -> assignmentOfSafeNaive b }
        assignmentOfSafeNaive (a \/SF b) = do
            a? <- safeRead (assignmentOfSafeNaive a)
            case a? of 
                \{ (just true) -> return true
                ;  _           -> assignmentOfSafeNaive b }

        assignmentOfSafe : SATFormOver (V Bool) -> LState Bool
        assignmentOfSafe trueSF  = return true
        assignmentOfSafe falseSF = return false
        assignmentOfSafe (varSF v) = read v
        assignmentOfSafe (notSF form) = (| not``Bool (assignmentOfSafe form) |)
        assignmentOfSafe (a /\SF b) = do
            a? <- safeRead (assignmentOfSafe a)
            b? <- safeRead (assignmentOfSafe b)
            case (a? , b?) of 
                \{ (just false , _ ) -> return false
                ;  ( _ , just false) -> return false
                ;  (just true , just b' )  -> return b'
                ;  (just true , nothing )  -> assignmentOfSafe b
                -- ;  ( just a' , just true)  -> return a'
                ;  ( nothing , just true)  -> assignmentOfSafe a
                ;  (nothing , nothing) -> (| (assignmentOfSafe a) and``Bool  (assignmentOfSafe b) |) } -- TODO: lazy read?
        assignmentOfSafe (a \/SF b) = do
            a? <- safeRead (assignmentOfSafe a)
            b? <- safeRead (assignmentOfSafe b)
            case (a? , b?) of 
                \{ (just true , _ )  -> return true
                ;  ( _ , just true)  -> return true
                ;  (just false , just b' ) -> return b'
                ;  (just false , nothing ) -> assignmentOfSafe b
                -- ;  ( just a' , just false) -> return a'
                ;  ( nothing , just false) -> assignmentOfSafe a
                ;  (nothing , nothing) -> (| (assignmentOfSafe a) or``Bool  (assignmentOfSafe b) |) }

        assignmentOf' : SATFormOver (V Bool) -> LState Bool
        assignmentOf' trueSF  = return true
        assignmentOf' falseSF = return false
        assignmentOf' (varSF v) = branchingRead v -- (write v true <|> write v fals) >> read v
        assignmentOf' (notSF form) = (| not``Bool (assignmentOf' form) |)
        assignmentOf' (a /\SF b) = (| (assignmentOf' a) and``Bool (assignmentOf' b) |)
        assignmentOf' (a \/SF b) = (| (assignmentOf' a) or``Bool  (assignmentOf' b) |)

        assignmentOfSolve : SATFormOver (V Bool) -> LState Bool
        assignmentOfSolve trueSF  = return true
        assignmentOfSolve falseSF = return false
        assignmentOfSolve (varSF v) = branchingRead v
        assignmentOfSolve (notSF form) = (| not``Bool (assignmentOfSolve form) |)
        assignmentOfSolve (a /\SF b) = do
            a? <- safeRead (assignmentOfSafe a)
            b? <- safeRead (assignmentOfSafe b)
            case (a? , b?) of 
                \{ (just false , _ ) -> return false
                ;  ( _ , just false) -> return false
                ;  (just true , _ )  -> assignmentOfSolve b
                ;  ( _ , just true)  -> assignmentOfSolve a
                ;  (nothing , nothing) -> (| (assignmentOfSolve a) and``Bool  (assignmentOfSolve b) |) }
        assignmentOfSolve (a \/SF b) = do
            a? <- safeRead (assignmentOfSafe a)
            b? <- safeRead (assignmentOfSafe b)
            case (a? , b?) of 
                \{ (just false , _ ) -> assignmentOfSolve b
                ;  ( _ , just false) -> assignmentOfSolve a
                ;  (just true , _ )  -> return true
                ;  ( _ , just true)  -> return true
                ;  (nothing , nothing) -> (| (assignmentOfSolve a) or``Bool  (assignmentOfSolve b) |) }

        -- \tagcode{SolveNaive}

        solve : SATFormOver (V Bool) -> Bool -> LState Unit
        solve trueSF  true   = return unit
        solve falseSF false  = return unit
        solve trueSF  false  = lift readConf
        solve falseSF true   = lift readConf
        solve (varSF v) b    = write v b -- >> void (read v)
        solve (notSF form) aim = solve form (not``Bool aim)
        solve (a /\SF b) true   = solve a true   >>  solve b true  -- TODO: fork should not catch when there is a conflict, only a read error!
        solve (a \/SF b) false  = solve a false  >>  solve b false -- TODO: BIG problem! This does not merge the possibilities for when a is true and b is true! Too much branching! Needs a nub or branching protection! 
        solve (a /\SF b) false  = solve a false  <|> solve b false -- TODO: this alone branches way too much
        solve (a \/SF b) true   = solve a true   <|> solve b true  -- TODO: make this more finegrained! One side having a solution should already suffice sometimes...

        solve'' : SATFormOver (V Bool) -> Bool -> LState Unit
        solve'' trueSF  true   = return unit
        solve'' falseSF false  = return unit
        solve'' trueSF  false  = lift readConf
        solve'' falseSF true   = lift readConf
        solve'' (varSF v) b    = write v b >> void (read v)
        solve'' (notSF form) aim = solve'' form (not``Bool aim)
        solve'' (a /\SF b) true   = solve'' a true   >>  solve'' b true  
        solve'' (a \/SF b) false  = solve'' a false  >>  solve'' b false 
        solve'' (a /\SF b) false  = solve'' a false  <|> (solve'' a true  >> solve'' b false) 
        solve'' (a \/SF b) true   = solve'' a true   <|> (solve'' a false >> solve'' b true )  

        solve' : SATFormOver (V Bool) -> Bool -> LState Unit
        solve' trueSF  true   = return unit
        solve' falseSF false  = return unit
        solve' trueSF  false  = lift readConf
        solve' falseSF true   = lift readConf
        solve' (varSF v) b    = write v b >> void (read v)
        solve' (notSF form) aim = solve' form (not``Bool aim)
        solve' (a /\SF b) true   = solve' a true   >> solve' b true -- TODO: both should run in parallel!
        solve' (a \/SF b) false  = solve' a false  >> solve' b false
        solve' (a /\SF b) false  = do
            a? <- safeRead (assignmentOfSafe a)
            b? <- safeRead (assignmentOfSafe b)
            case (a? , b?) of 
                \{ (just x , just y) -> unless' (not``Bool (x and``Bool y)) (lift readConf)
                ;  (just false , _ ) -> return unit
                ;  ( _ , just false) -> return unit
                ;  (just true , _ )  -> solve' b false
                ;  ( _ , just true)  -> solve' a false
                ;  (nothing , nothing) -> solve' a false  <|> (solve' a true >> solve' b false) }
        solve' (a \/SF b) true  = do
            a? <- safeRead (assignmentOfSafe a)
            b? <- safeRead (assignmentOfSafe b)
            case (a? , b?) of
                \{ (just x , just y) -> unless' (x or``Bool y) (lift readConf)
                ;  (just true , _ )  -> return unit
                ;  ( _ , just true)  -> return unit
                ;  (just false , _ ) -> solve' b true
                ;  ( _ , just false) -> solve' a true
                ;  (nothing , nothing) -> solve' a true  <|> (solve a false >> solve' b true) }

module ConcreteExample (n : Nat) where
    open ListOp using (map)
    open BoolOp
    open TrivialLattice

    bNLat = (trivialBoundedMeetSemilattice boolDecEq) BSL^ n
    open BoundedMeetSemilattice bNLat using (top)

    variables' : (LBVar (Bool tb `$\back^ n $`) bNLat Bool) `$\back^ n $`
    variables' = LBVarHomProduct (TrivLBVar boolDecEq)

    Err = String -- Err = Unit

    open SAT-Solver bNLat (ErrorT.monadFailAlternativeOver String listMonad listMonadFailAlternativeOver) (ErrorT.monadErrorOver String listMonad) public
    open Solver 
        (\_ _ -> ME.throw "read error") 
        (ME.throw "conflict") -- (\_ _ -> MFA.fail) 
        (\{_} {_} {m} -> ME.left-absorb {m = m}) 
        (\{_} {_} {m} -> ME.left-absorb {m = m}) -- (\{_} {_} {m} -> MFA.left-absorb {f = m})
        _=S=_
        "read error"
        public

    variables : (V Bool) `$\back^ n $`
    variables = variables'

    infix 3 AND
    AND : {n : Nat} -> (V Bool -> SATFormOver (V Bool)) -> (V Bool) `$\back^ n $` -> SATFormOver (V Bool)
    AND f = foldNTup
        (_/\SF_ o f)
        trueSF

    infix 3 ANDREM
    ANDREM : {n : Nat} -> (V Bool -> {n' : Nat} -> (V Bool) `$\back^ n' $` -> SATFormOver (V Bool)) -> (V Bool) `$\back^ n $` -> SATFormOver (V Bool)
    ANDREM f = fst {B = \_ -> exists[ n' of Nat ] ((V Bool) `$\back^ n' $`)} o foldNTup
        (\{v (r , _ , rvars) -> (f v rvars) /\SF r , _ , (v ,- rvars)})
        (trueSF , _ , unit)

    syntax AND (\v -> F) Vec = bigwedge[ v , Vec ] F
    syntax ANDREM (\v vars -> F) Vec = bigwedge``r[ v , Vec , vars ] F
    
    infix 2 OR
    OR : {n : Nat} -> (V Bool -> SATFormOver (V Bool)) -> (V Bool) `$\back^ n $` -> SATFormOver (V Bool)
    OR f = foldNTup
        (_\/SF_ o f)
        falseSF
    
    syntax OR (\v -> F) Vec = bigvee[ v , Vec ] F

    noneOf : {n : Nat} -> (V Bool) `$\back^ n $` -> SATFormOver (V Bool)
    noneOf vars = bigwedge[ v , vars ] notSF (varSF v)

    minOne : SATFormOver (V Bool)
    minOne = bigvee[ v , variables ] varSF v

    maxOne : SATFormOver (V Bool)
    maxOne = bigwedge``r[ v , variables , variables/v ] (varSF v) =>SF noneOf variables/v

    exactlyOne : SATFormOver (V Bool)
    exactlyOne = minOne /\SF maxOne

    getModel : LState (Maybe Bool `$\back^ n $`)
    getModel = foldNTupPi {B = \n -> LState (Maybe Bool `$\back^ n $`)}
        (\_ v m -> (| (safeRead (read v)) ,- m |))
        (return unit)
        variables

    run : {X : Set} -> LState X -> List (X or Err)
    run m = map (mapLeft (snd o snd)) (m top)

    runAssignmentOf' : List (Maybe Bool `$\back^ n $` or Err)
    runAssignmentOf' = run do
        -- res <- assignmentOf' exactlyOne -- >>= guard
        -- unless' res (throw "wrong output")
        -- res <- assignmentOfMon exactlyOne -- >>= guard
        -- unless' res (throw "wrong output") -- TODO: this guard should already automatically be weaved into the evaluation computation!
        -- res <- fold``Bool``LState branchingRead assignmentAlg exactlyOne
        -- unless' res (throw "wrong output")
        -- solve``Bool``LStateNaive (\v x -> write v x >> void (read v)) assignmentAlg exactlyOne true
        solve``Bool``LState (\v x -> write v x >> void (read v)) assignmentAlg exactlyOne true
        -- solve' exactlyOne true
        getModel
    -- ConcreteExample.runAssignmentOf' 3
    -- take 1 (ConcreteExample.runAssignmentOf' 3)

    readTest : List ((List Bool) or Err)
    readTest = run $ foldNTup
        (\v m -> do
            v' <- (write v true <|> write v false) >> read v
            m' <- m
            return (v' :: m')
        )
        (return [])
        variables

    -- ConcreteExample.readTest 3 

module PreliminaryExamples where
    open ConcreteExample 3

    v1 v2 v3 : V Bool
    v1 = fst variables
    v2 = fst $ snd variables
    v3 = snd $ snd variables

    -- assignmentOfTest : List (Bool or Err)
    -- assignmentOfTest = run do
    --     write v1 true
    --     write v2 true
    --     -- write v3 false
    --     -- assignmentOfSolve exactlyOne
    --     -- foldLS assignmentAlg exactlyOne
    --     fold``Bool``LState read assignmentAlg exactlyOne

    assignmentOfTest : List (Maybe Bool `$\back^ 3 $` or Err)
    assignmentOfTest = run do
        -- res <- assignmentOfSolve exactlyOne
        res <- fold``Bool``LState branchingRead assignmentAlg exactlyOne
        when' (not``Bool res) (throw "wrong output")
        getModel
   
    -- PreliminaryExamples.assignmentOfTest

    solveTest : List (Maybe Bool `$\back^ 3 $` or Err)
    solveTest = run do
        solve' exactlyOne true
        getModel
   
    -- PreliminaryExamples.solveTest


module BiggerExample where
    -- size/2 = 70
    -- size = 100
    -- size/2 = 2
    -- size = 3
    size/2 = 4
    size = 10
    open ConcreteExample size

    data IsJust {A : Set i} : Maybe A -> Set i where
        instance isJust : {a : A} -> IsJust (just a)

    fromJust : (m : Maybe A) -> {{ij : IsJust m}} -> A
    fromJust (just a) {{(isJust)}} = a

    vidx : Nat -> Maybe (V Bool)
    vidx = vidx' {n' = size} variables
        where
            vidx' : {n' : Nat} -> (V Bool) `$\back^ n' $` -> (n : Nat) -> Maybe (V Bool)
            vidx' {0} vars n = nothing
            vidx' {1+ 0} vars 0 = just vars
            vidx' {1+ (1+ n')} vars 0 = just (fst vars)
            vidx' {1+ 0} vars (1+ n) = nothing
            vidx' {1+ (1+ n')} vars (1+ n) = vidx' (snd vars) n

    v : (n : Nat) -> {{ij : IsJust (vidx n)}} -> V Bool
    v n {{ij}} = fromJust _ {{ij}}

    -- v1 v2 v3 : V Bool
    -- v1 = fst variables
    -- v2 = fst $ snd variables
    -- v3 = fst $ snd $ snd variables
    -- v4 = fst $ snd $ snd $ snd variables
    -- v5 = fst $ snd $ snd $ snd $ snd variables
    -- v6 = fst $ snd $ snd $ snd $ snd $ snd variables
    -- v7 = fst $ snd $ snd $ snd $ snd $ snd $ snd variables

    -- assignmentOfTest : List (Bool or Err)
    -- assignmentOfTest = run do
    --     write v1 true
    --     write v2 true
    --     -- write v3 false
    --     -- assignmentOfSolve exactlyOne
    --     -- foldLS assignmentAlg exactlyOne
    --     fold``Bool``LState read assignmentAlg exactlyOne

    assignmentOfTest : List (Maybe Bool `$\back^ size $` or Err)
    assignmentOfTest = run do
        -- res <- assignmentOfSolve exactlyOne
        write (v size/2) true
        res <- fold``Bool``LState branchingRead assignmentAlg exactlyOne
        when' (not``Bool res) (throw "wrong output")
        getModel
    -- test agains generate and test approach:
    -- BiggerExample.assignmentOfTest
   
    -- BiggerExample.assignmentOfTest

    solveTest : List (Maybe Bool `$\back^ size $` or Err)
    solveTest = take 1 $ run do
        write (v size/2) true
        solve``Bool``LState (\v x -> write v x >> void (read v)) assignmentAlg exactlyOne true
        -- solve' exactlyOne true
        getModel
   
    -- TODO: Slow for bigger number of variables!
    -- BiggerExample.solveTest
    -- length (BiggerExample.solveTest)
    -- TODO: Slow! 