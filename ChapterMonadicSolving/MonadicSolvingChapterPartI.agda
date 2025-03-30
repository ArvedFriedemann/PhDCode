{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS --cubical #-}
module ChapterMonadicSolving.MonadicSolvingChapterPartI where

open import ASCIIPrelude.ASCIIPrelude hiding (_and_; _or_; List)
        hiding (module StateT)

open MonadTransformers
open Monads
open Applicatives
open Functors
open MonadPluses
open Alternatives

private
    variable
        h i j k l i' j' : Level
        n n' : Nat
        X Y : Set i
        M F G : Set i -> Set j

-- \tagcode{MonadicSolvingChapterPartI}

module ListIntro where
    open BoolOp renaming
        ( _andBool_ to _and_
        ; _orBool_ to _or_
        ; _impliesBool_ to _implies_
        ; notBool to not
        )

    open import ASCIIPrelude.ASCIIPrelude using ()
        renaming (List to List_)
    open ListMonad
    open PolyUnit
    private variable
        A : Set i
    
    new``lBool : List Bool
    new``lBool = true :: false :: [] 

    Fun : Nat -> Set i -> Set i -> Set i
    Fun 0 A B = B
    Fun (1+ n) A B = A -> Fun n A B

    _`$\back\sub_\,$`->_ : Set i -> Nat -> Set i -> Set i
    A `$\back\sub n \,$`-> B = Fun n A B

    _^_->'_ : Set i -> Nat -> Set i -> Set i
    A ^ n ->' B = Fun n A B

    {-# DISPLAY _`$\back\sub_\,$`->_ A n B = A ^ n ->' B #-}

    Tup : Nat -> Set i -> Set i
    Tup 0 _ = Unit
    Tup 1 A = A
    Tup (1+ n) A = A -x- Tup n A

    infix 100 _`$\back^_$` 

    _`$\back^_$` : Set i -> Nat -> Set i
    A `$\back^ n $` = Tup n A

    infix 100 _^_

    _^_ : Set i -> Nat -> Set i
    A ^ n = Tup n A

    {-# DISPLAY _`$\back^_$` A n = A ^ n #-}

    onlyOne`$\sub3$` : Bool `$\back\sub 3 \,$`-> Bool 
    onlyOne`$\sub3$` x y z = 
            (x implies (not y and not z))
        and (y implies (not x and not z))
        and (z implies (not x and not y))
        and (x or y or z)

    fail : List A
    fail = []

    solveOnlyOne`$\sub3$` : List Bool `$\back^ 3 $`
    solveOnlyOne`$\sub3$` = do
        x <- new``lBool
        y <- new``lBool
        z <- new``lBool
        unless (onlyOne`$\sub3$` x y z) fail
        return (x , y , z)

    SAT-Solve : (Bool `$\back\sub n \,$`-> Bool) -> List Bool `$\back^ n $`
    SAT-Solve {0} f = do
        unless f fail
        return unit
    SAT-Solve {1} f = do
        x <- new``lBool
        unless (f x) fail
        return x
    SAT-Solve {1+ 1+ n} f = do
        x <- new``lBool
        (| (| x |) , SAT-Solve (f x) |)

    unsatExample : List Bool `$\back^ 1 $`
    unsatExample = SAT-Solve (\ a -> a and not a)

    -- ListIntro.SAT-Solve ListIntro.onlyOne`$\sub3$`
    -- ListIntro.unsatExample

module ListSolutionCounterMonadPlus where
    open BoolOp renaming
        ( _andBool_ to _and_
        ; _orBool_ to _or_
        ; _impliesBool_ to _implies_
        ; notBool to not
        )
    open import ASCIIPrelude.CustomDefinitions
    open MaybeT
    open import ASCIIPrelude.ASCIIPrelude using (List)
    open MonadPlus
    open ListMonad using (listMonad)
    open import Effect.Monad using (RawMonadZero)
    open import Effect.Empty using (RawEmpty)
    open import Effect.Choice using (RawChoice)
    open RawEmpty
    open RawMonadZero
    open RawChoice
    open ListMonadPlus renaming (_<|>_ to _<|>L_)
    listSolutionCounterMonadPlus : MonadPlus (MaybeT List)
    rawMonad (rawMonadZero listSolutionCounterMonadPlus) = monadMaybeT listMonad
    empty (rawEmpty (rawMonadZero listSolutionCounterMonadPlus)) = nothing :: []
    _<|>_ (rawChoice listSolutionCounterMonadPlus) = _<|>L_

module GeneralisedMonadPlus where
    open MonadPluses
    open Alternatives
    open import ASCIIPrelude.ASCIIPrelude using (List)

    module GenUniverseOps {M : Set i -> Set j} (mp : MonadPlus M) where
        open MonadPlus mp
        open MonadPlusAddOp mp
        
        new``lBool : M Bool
        new``lBool = (| true |) <|> (| false |)

        module _ {A : Set i} where
            newMaybe : A -> M (Maybe A)
            newMaybe a = (| nothing |) <|> (| (just a) |)

        data Fin : Nat -> Set where
            fzero : Fin (1+ n)
            f1+_ : Fin n -> Fin (1+ n)

        newFin : (n : Nat) -> M (Fin (1+ n))
        newFin 0 = (| fzero |)
        newFin (1+ n) = (| fzero |) <|> (| f1+ newFin n |)
    
        newNat : (n : Nat) -> M Nat
        newNat 0 = (| 0 |)
        newNat (1+ n) = (| 0 |) <|> (| 1+ newNat n |)

        module _ {A : Set i} where
            newList : (n : Nat) -> M A -> M (List A)
            newList 0 _ = (| [] |)
            newList (1+ n) ma = (| [] |) <|> (| ma :: newList n ma |)


    module LZeroUniverseOps {M : Set -> Set} (mp : MonadPlus M) where
        open GenUniverseOps mp
        open MonadPlus mp
        open MonadPlusAddOp mp
        open BoolOp renaming
            ( _andBool_ to _and_
            ; _orBool_ to _or_
            ; _impliesBool_ to _implies_
            ; notBool to not
            )
        
        module _ where
            open NatOp
            sorted : List Nat -> Bool
            sorted [] = true
            sorted (x :: []) = true
            sorted (x :: y :: xs) = 
                (x leq y) and sorted (y :: xs)

        sortedLists : (n : Nat) -> M (List Nat)
        sortedLists n = newList n (newNat n) such-that sorted
        -- GeneralisedMonadPlus.sortedLists (MonadPluses.ListMonadPlus.listMonadPlus) 2

    module ConcreteExamples where
        open ListSolutionCounterMonadPlus
        open LZeroUniverseOps listSolutionCounterMonadPlus public
        open ListOp
        
        sortedListVisitedNodes : Nat -> Nat
        sortedListVisitedNodes n = length (sortedLists n)

        sortedListFailedNodes : Nat -> Nat
        sortedListFailedNodes n = length (filter is-nothing (sortedLists n))

        -- GeneralisedMonadPlus.ConcreteExamples.sortedLists 2

        -- GeneralisedMonadPlus.ConcreteExamples.sortedListVisitedNodes 2
        -- GeneralisedMonadPlus.ConcreteExamples.sortedListFailedNodes 2

        -- GeneralisedMonadPlus.ConcreteExamples.sortedListVisitedNodes 4
        -- GeneralisedMonadPlus.ConcreteExamples.sortedListFailedNodes 4

        -- GeneralisedMonadPlus.ConcreteExamples.sortedListVisitedNodes 6
        -- GeneralisedMonadPlus.ConcreteExamples.sortedListFailedNodes 6

module ExplicitLazyness {M : Set i -> Set i} (mp : MonadPlus M) where
    open MonadPlus mp

    -- \tagcode{LISTM}

    {-# NO_POSITIVITY_CHECK #-}
    data ListM (A : Set i) : Set i where
        []M   : ListM A
        _::M_ : M A -> M (ListM A) -> ListM A 

    module _ {A : Set i} where
        newList : (n : Nat) -> M A -> M (ListM A)
        newList 0 _ = (| []M |)
        newList (1+ n) ma = (| []M |) <|> (| (ma ::M newList n ma) |)

    -- open GeneralisedMonadPlus public
    -- open GenUniverseOps mp public

module ConcreteExplicitLazyness {M : Set -> Set} (mp : MonadPlus M) where
    open ExplicitLazyness mp
    open MonadPlus mp
    open Alternative rawAlternative using (guard)
    open NatOp
    open import ASCIIPrelude.ASCIIPrelude using (List)
    open ListOp hiding (and; guard)
    open PolyUnit
    open GeneralisedMonadPlus.GenUniverseOps mp using (newNat)
    
    -- \tagcode{SortedListM}

    {-# TERMINATING #-}
    sorted : ListM Nat -> M Bool
    sorted []M = (| true |)
    sorted (mx ::M mxs) = do
        xs <- mxs
        case xs of \{
              []M -> mx >> (| true |)
            ; (my ::M mxs') -> do
                x <- mx
                y <- my 
                guard (x leq y)
                sorted ((| y |) ::M mxs')
            }
            
    unevalSortedLists : Nat -> M Unit
    unevalSortedLists n = newList n (newNat n) >>= sorted >>= guard

    {-# TERMINATING #-}
    toList : ListM X -> M (List X)
    toList []M = (| [] |)
    toList (mx ::M mxs) = (| mx :: (toList =<< mxs) |)

    sortedListsNaive : Nat -> M (List Nat)
    sortedListsNaive n = do
        lst <- newList n (newNat n)
        sorted lst >>= guard
        toList lst

module ConcreteExplicitLazynessExamples where
    open ListSolutionCounterMonadPlus
    open ConcreteExplicitLazyness listSolutionCounterMonadPlus public
    open ListOp

    -- ConcreteExplicitLazynessExamples.sortedListsNaive 2

    sortedListVisitedNodes : Nat -> Nat
    sortedListVisitedNodes n = length (unevalSortedLists n)

    sortedListFailedNodes : Nat -> Nat
    sortedListFailedNodes n = length (filter is-nothing (unevalSortedLists n))
    
    -- ConcreteExplicitLazynessExamples.sortedListVisitedNodes 2
    -- ConcreteExplicitLazynessExamples.sortedListFailedNodes 2

    -- ConcreteExplicitLazynessExamples.sortedListVisitedNodes 4
    -- ConcreteExplicitLazynessExamples.sortedListFailedNodes 4

    -- ConcreteExplicitLazynessExamples.sortedListVisitedNodes 6
    -- ConcreteExplicitLazynessExamples.sortedListFailedNodes 6



module Lenses where
    record Lens (A B : Set i) : Set i where
        constructor <_,_>lens
        field
            lget : A -> B
            lput : B -> A -> A
            
        lmodify : (B -> B) -> A -> A
        lmodify f a = lput (f (lget a)) a

module LensVarMonad {M : Set i -> Set i} (mp : MonadPlus {i} {i} M) where
    open import ASCIIPrelude.ASCIIPrelude using (List; _and_ ; _or_)
    open ListOp hiding (and; or; head; drop)
    open PolyUnit
    open import ASCIIPrelude.CustomDefinitions
    open StateT
    open Lenses
    open Lens
    open import Effect.Monad.State.Indexed
    private variable
        A B C : Set i

    module CVs {i} (M : Set i -> Set i) where
        -- Cached Val
        CV : Set i -> Set i
        CV A = A or M A

        pattern val a = left a
        pattern prod ma = right ma

        module _ {A : Set i} where
            onValClash : (A -> A -> A) -> CV A -> CV A -> CV A
            onValClash f (val x)   (val y)   = val (f x y)
            onValClash f (val x)   (prod _)  = val x
            onValClash f (prod _)  (val x)   = val x
            onValClash f (prod mx) (prod my) = prod mx -- hack

            leftOnValClash : CV A -> CV A -> CV A
            leftOnValClash = onValClash const

        module _ (func : Functor {i} M) where
            open Functor func
            functorCV : Functor {i} CV
            Functor._<$>_ functorCV f (val   a) = val (f a)
            Functor._<$>_ functorCV f (prod ma) = prod (f <$> ma)

    module StateOps (S : Set i) where
        open StateActions {i = i} {S = S} (MonadPlus.rawApplicative mp) public
        
        MS : Set i -> Set i
        MS = StateT S M

        module _ where
            open MonadPlus mp renaming (_<|>_ to _<|>M_)
            _<|>_ : MS A -> MS A -> MS A
            (m1 <|> m2) s = m1 s <|>M m2 s

            fail : MS A
            fail s = empty

        monadTMS : MonadT {i} M MS
        monadTMS = monadTStateT {S = S} (MonadPlus.rawMonad mp)

        open MonadT monadTMS
        open CVs {i} MS public

        V : Set i -> Set i
        V X = Lens S (CV X)

        read : V A -> MS A
        read l = do
            a+ma <- getS (lget l)
            case a+ma of \{
                  (val   a) -> return a
                ; (prod ma) -> do
                    a <- ma
                    modify (lput l (left a))
                    return a
                }

        idL : Lens A (CV A)
        lget idL = val
        lput idL (val   a) = const a
        lput idL (prod ma) = id -- TODO: this does not work unless we can evoke the monad when writing

        infixr 5 _oV_
        _oV_ : Lens B (CV C) -> Lens A (CV B) -> Lens A (CV C)
        lget (vc oV vb) s with lget vb s
        ... | val   a = lget vc a
        ... | prod ma = prod (ma >>= fromRight return o lget vc)
        lput (vc oV vb) cvc = lmodify vb (fmap (lput vc cvc))
            where 
                open Functor {i} (functorCV (MonadT.rawFunctor monadTMS))
                    renaming (_<$>_ to fmap)

module ListMs (M : Set i -> Set i) where

    {-# NO_POSITIVITY_CHECK #-}
    data ListM (A : Set i) : Set i where
        []M   : ListM A
        _::M_ : M A -> M (ListM A) -> ListM A

    
module LensVarMonadExamples where
    module ListExample {M : Set i -> Set i} (mp : MonadPlus {i} {i} M) (A : Set i) where
        open Lenses
        open Lens
        open LensVarMonad mp
        module _ where
            open StateOps
            {-# NO_POSITIVITY_CHECK #-}
            data ListM (A : Set i) : Set i where
                []M   : ListM A
                _::M_ : CV (ListM A) A -> CV (ListM A) (ListM A) -> ListM A
            open StateOps (ListM A) public

        open MonadT monadTMS
        open MonadAddOp (MonadT.rawMonad monadTMS)
        open PolyUnit

        mutual 
            --first one is the dominant one taken on conflict
            {-# TERMINATING #-} -- this terminates on inlining
            mergeListMCV : CV (ListM A) -> CV (ListM A) -> CV (ListM A)
            mergeListMCV = onValClash mergeListM

            mergeListM : (ListM A) -> (ListM A) -> (ListM A)
            mergeListM []M []M               = []M
            mergeListM (x ::M xs) (y ::M ys) = leftOnValClash x y ::M mergeListMCV xs ys
            mergeListM xs ys                 = xs

        newList : (n : Nat) -> MS A -> MS (ListM A)
        newList zero ma = (| []M |)
        newList (1+_ n) ma = (| []M |) <|> (| (prod ma ::M prod (newList n ma)) |) -- 

        -- TODO: For chapter, only consider reading lenses first
        nilL : Lens (ListM A) (CV Unit)
        lget nilL []M = val unit
        lget nilL (x ::M x1) = prod fail
        lput nilL cvu []M = []M
        lput nilL cvu (x ::M xs) = x ::M xs -- should fail!

        -- TODO: For chapter, only consider reading lenses first
        headL : Lens (ListM A) (CV A)
        lget headL []M = prod fail
        lget headL (cva ::M _) = cva
        lput headL cva []M = []M -- < - we should fail here!
        lput headL cva (x ::M xs) = leftOnValClash cva x ::M xs
        
        tailL : Lens (ListM A) (CV (ListM A))
        lget tailL []M = prod fail
        lget tailL (_ ::M cvlst) = cvlst
        lput tailL cvlst []M = []M -- < - we should fail here!
        lput tailL cvlst (cva ::M cvlst') = cva ::M mergeListMCV cvlst' cvlst

        -- {-# NO_POSITIVITY_CHECK #-}
        -- data ListV (A : Set i) : Set i where
        --     []M : ListV A
        --     _::M_ : V A -> V (ListM A) -> ListV A

        -- [_]LstPtr : V (ListM A) -> V (ListV A)
        -- lget [ v ]LstPtr []M       = left []M
        -- lget [ v ]LstPtr (_ ::M _) = left ((headL oV v) ::M (tailL oV v))
        -- lput [ v ]LstPtr (left []M) _           = []M -- should fail on override!
        -- lput [ v ]LstPtr (left (x ::M xs)) lstm = lget x lstm ::M lget xs lstm -- should fail on override!
        -- -- v - the case with still unpacking the pointer does not work
        -- --     because we cannot monadically unpack it here
        -- lput [ v ]LstPtr (right mlstv) = id -- wrong

        stateListPtr : V (ListM A)
        stateListPtr = idL

        open import ASCIIPrelude.ASCIIPrelude using (List)

        {-# TERMINATING #-}
        renderList : V (ListM A) -> MS (List A)
        renderList v = read v >>= \{
               []M      -> (| [] |)
            ; (_ ::M _) -> (| read (headL oV v) :: renderList (tailL oV v) |)
            }

        

    module ListNatExample {M : Set i -> Set i} (mp : MonadPlus {i} {i} M) where
        open ListExample mp Nat public
        open MonadT monadTMS
        open NatOp
        open PolyUnit
        open import ASCIIPrelude.ASCIIPrelude using (List)

        newNat : (n : Nat) -> MS Nat
        newNat 0 = (| 0 |) 
        newNat (1+ n) = (| (1+ n) |) <|> newNat n

        guard : Bool -> MS Unit
        guard false = fail
        guard true = return unit

        -- \tagcode{SortedVListM}

        mutual
            {-# TERMINATING #-}
            sorted : V (ListM Nat) -> MS Unit
            sorted v = read v >>= sorted' v
            
            sorted' : V (ListM Nat) -> ListM Nat -> MS Unit
            sorted' v []M = (| unit |)
            sorted' v (_ ::M _) = do
                lst <- read (tailL oV v)               
                case lst of \{
                        []M -> (| unit |)
                    ; (_ ::M _) -> do
                        a <- read (headL oV v)
                        b <- read (headL oV tailL oV v)
                        guard (a leq b)
                        sorted (tailL oV v)
                    }
        
        sortedLists : Nat -> MS (List {i} Nat)
        sortedLists n = do
            newList n (newNat n) >>= put
            sorted stateListPtr
            renderList stateListPtr

module ListNatConcreteExample where
    open LensVarMonadExamples
    open ListSolutionCounterMonadPlus
    open ListNatExample listSolutionCounterMonadPlus public
    open import ASCIIPrelude.ASCIIPrelude using (List)
    open ListOp
    open MonadT monadTMS

    sortedLists' : Nat -> List (ListM Nat)
    sortedLists' n = catMaybes $ map (mapMaybe fst) (sortedLists n []M) 
    
    -- ListNatConcreteExample.sortedLists' 2

    sortedListVisitedNodes : Nat -> Nat
    sortedListVisitedNodes n = length (sortedLists n []M)

    sortedListFailedNodes : Nat -> Nat
    sortedListFailedNodes n = length (filter is-nothing (sortedLists n []M))

    -- ListNatConcreteExample.sortedListVisitedNodes 2
    -- ListNatConcreteExample.sortedListFailedNodes 2

    -- ListNatConcreteExample.sortedListVisitedNodes 4
    -- ListNatConcreteExample.sortedListFailedNodes 4

    -- ListNatConcreteExample.sortedListVisitedNodes 6
    -- ListNatConcreteExample.sortedListFailedNodes 6
        
  