{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.ConstrainedStates where

open import ASCIIPrelude.ASCIIPrelude
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
-- open import OwnPrelude.Relation.Properties
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadTs
open import OwnPrelude.Categorical.IMonoids
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Categorical.MonadPlus
open import OwnPrelude.Categorical.Alternatives
open import OwnPrelude.Categorical.MonadFailAlternatives
open import OwnPrelude.Categorical.MonadErrors

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u e : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G M : Set i -> Set j
        a b x y z m : A
        f g : A -> B

-- \tagcode{CStateT}

CStateT : 
    (S : Set u) -> 
    (S -> S -> Set c) ->
    (Set (i ~U~ u ~U~ c) -> Set j) -> Set i -> Set (j ~U~ u)
CStateT S _P_ M X = (s : S) -> M (exists[ s' of S ] (s P s') -x- X)

module GetAction 
    {S : Set i} 
    {_P_ : S -> S -> Set c} 
    (po : IsPreOrder _P_) 
    {M : Set (i ~U~ c) -> Set j} 
    (mon : Monad M) where
    open IsPreOrder po
    open Monad mon
    
    get : CStateT S _P_ M S
    get s = return (s , reflexive , s)

module StateActions 
    {u : Level}
    {S : Set i} 
    {_P_ : S -> S -> Set c} 
    (po : IsPreOrder _P_) 
    {M : Set (i ~U~ c ~U~ u) -> Set j} 
    (mon : Monad M) where
    open IsPreOrder po
    open Monad mon
    module _ {X : Set u} where
        getS : (S -> X) -> CStateT S _P_ M X
        getS f s = return (s , reflexive , f s)

        local : CStateT S _P_ M X -> CStateT S _P_ M X
        local m s = do
            (_ , _ , x) <- m s
            return (s , reflexive , x)

module CStateTMonad 
    (S : Set u)
    {_P_ : S -> S -> Set c}
    (po : IsPreOrder _P_)
    {M : Set (i ~U~ u ~U~ c) -> Set j}
    (mon : Monad M) where
    open IsPreOrder po

    module _ where
        open Monad mon hiding (rawMonad)

        rawMonad : RawMonad {i} (CStateT S _P_ M)
        RawMonad.return rawMonad x s = return (s , reflexive , x)
        RawMonad._>>=_ rawMonad mx fmy s = do
            (s'  , p  , a) <- mx s
            (s'' , p' , b) <- fmy a s'
            return 
                ( s''
                ,  (p  :T: s  P s'  [premise]
                    p' :T: s' P s'' [premise]
                    -----------------------------
                    transitive p p' :T: s P s'')
                , b)

    module _ 
        (isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid po)) where

        open RawMonad rawMonad renaming (return to returnS; _>>=_ to _>>=S_; _>=>_ to _>=>S_)
        open Monad mon hiding (rawMonad; isMonad)
        open IsIMonoid isIMonoid renaming 
            ( left-identity to left-identity-P
            ; right-identity to right-identity-P
            ; associative to associative-P)
        
        isMonad : IsMonad rawMonad
        -- return x >>= f === f x
        IsMonad.left-identity isMonad {x} {f} = extensPi \s ->
            (returnS x >>=S f) s =<>
            
            (do 
                (s'  , p , x') <- return (s , reflexive , x) 
                (s'' , p' , b) <- f x' s'
                return (s'' , transitive p p' , b)
            ) =< left-identity > 

            (do 
                (s'' , p' , b) <- f x s
                return (s'' , transitive reflexive p' , b)
            ) =< (\{(_ , p' , _) -> left-identity-P {a = p'}}) |pi (\h -> f x s >>= \{(s'' , p' , b) -> return (s'' , h (s'' , p' , b) , b)}) > 

            (do 
                (s'' , p' , b) <- f x s
                return (s'' , p' , b)
            ) =< right-identity > 
            
            f x s qed
        -- m >>= return === m
        IsMonad.right-identity isMonad {m} = extensPi \s ->
            (m >>=S returnS) s =<>
            
            (do 
                (s'  , p , x) <- m s
                (s'' , p' , b) <- return (s' , reflexive , x)
                return (s'' , transitive p p' , b)
            ) =< ((\{(s' , p , x) -> left-identity {x = s' , reflexive , x}}) |pi (\h -> m s >>= \ctx -> h ctx)) > 

            (do 
                (s'  , p , x) <- m s
                return (s' , transitive p reflexive , x)
            ) =< (\{(_ , p , _) -> right-identity-P {a = p}}) |pi (\h -> m s >>= \{(s'  , p , x) -> return (s' , h (s' , p , x) , x)}) > 

            (do 
                (s'  , p , x) <- m s
                return (s' , p , x)
            ) =< right-identity >

            m s qed
            
        -- (m >>= f) >>= g === m >>= (f >=> g)
        IsMonad.associative isMonad {m} {f} {g} = extensPi \s -> 
            ((m >>=S f) >>=S g) s =<>

            (do
                (s''  , p''  , b) <- (m >>=S f) s
                (s''' , p''' , c) <- g b s''
                return (s''' , transitive p'' p''' , c)
            ) =<>

            (do
                (s''  , transp'p''  , b) <- do
                    (s'  , p'  , a) <- m s
                    (s'' , p'' , b) <- f a s'
                    return (s'' , transitive p' p'' , b)
                (s''' , p''' , c) <- g b s''
                return (s''' , transitive transp'p'' p''' , c)
            ) =< associative >

            (do
                (s'  , p'  , a) <- m s
                (s''  , transp'p''  , b) <- do
                    (s'' , p'' , b) <- f a s'
                    return (s'' , transitive p' p'' , b)
                (s''' , p''' , c) <- g b s''
                return (s''' , transitive transp'p'' p''' , c)
            ) =< (\{_ -> associative }) |pi (\h -> m s >>= \ctx -> h ctx) >

            (do
                (s'  , p'  , a) <- m s
                (s'' , p'' , b) <- f a s'
                (s''cpy  , transp'p''  , b) <- do
                    return (s'' , transitive p' p'' , b)
                (s''' , p''' , c) <- g b s''cpy
                return (s''' , transitive transp'p'' p''' , c)
            ) =< (\ _ _ -> left-identity) |pi2 (\h -> m s >>= \{(s'  , p'  , a) -> f a s' >>= \ctx -> h (s'  , p'  , a) ctx}) >

            (do
                (s'   , p'   , a) <- m s
                (s''  , p''  , b) <- f a s'
                (s''' , p''' , c) <- g b s''
                return (s''' , transitive (transitive p' p'') p''' , c)
            ) =< ((\{_ _ (s''' , p''' , c) -> associative-P}) |pi3 (\h -> m s >>= \{(s'   , p'   , a) -> f a s' >>= \{(s''  , p''  , b) -> g b s'' >>= \{(s''' , p''' , c) -> return (s''' , h (s'   , p'   , a) (s''  , p''  , b) (s''' , p''' , c) , c)}}})) >

            (do
                (s'   , p'   , a) <- m s
                (s''  , p''  , b) <- f a s'
                (s''' , p''' , c) <- g b s''
                return (s''' , transitive p' (transitive p'' p''') , c)
            ) =< (\{ (s'   , p'   , a) (s''  , p''  , b) (s''' , p''' , c) -> sym (left-identity {x = (s''' , transitive p'' p''' , c)} {f = \{(s''' , p'''' , c) -> return (s''' , transitive p' p'''' , c)}})} ) |pi3 (\h -> m s >>= \{(s'   , p'   , a) -> f a s' >>= \(s''  , p''  , b) -> g b s'' >>= h (s'   , p'   , a) (s''  , p''  , b) }) >

            (do
                (s'   , p'    , a) <- m s
                (s''  , p''   , b) <- f a s'
                (s''' , p'''  , c) <- g b s''
                (s''' , p'''' , c) <- return (s''' , transitive p'' p''' , c :T: exists[ s''' of S ] s' P s''' -x- _)
                return (s''' , transitive p' p'''' , c)
            ) =< ((\_ _ -> sym associative) |pi2 (\h -> m s >>= \{(s'   , p'    , a) -> f a s' >>= h (s'   , p'    , a)})) >

            (do
                (s'   , p'    , a) <- m s
                (s''  , p''   , b) <- f a s'
                (s''' , p'''' , c) <- do
                    (s''' , p'''  , c) <- g b s''
                    return (s''' , transitive p'' p''' , c)
                return (s''' , transitive p' p'''' , c)
            ) =< (\_ -> sym associative) |pi (m s >>=_) >

            (do
                (s'   , p'    , a) <- m s
                (s''' , p'''' , c) <- do
                    (s''  , p''   , b) <- f a s'
                    (s''' , p'''  , c) <- g b s''
                    return (s''' , transitive p'' p''' , c)
                return (s''' , transitive p' p'''' , c)
            ) =<>

            (do
                (s'   , p'    , a) <- m s
                (s''' , p'''' , c) <- (f >=>S g) a s'
                return (s''' , transitive p' p'''' , c)
            ) =<>

            (m >>=S (f >=>S g)) s qed
 
        monad : Monad {i} (CStateT S _P_ M)
        Monad.rawMonad monad = rawMonad
        Monad.isMonad  monad = isMonad

module CStateTMonadT 
    (S : Set u)
    {_P_ : S -> S -> Set c}
    (po : IsPreOrder _P_)
    {M : Set (i ~U~ u ~U~ c) -> Set j}
    (mon : Monad M) where  
    open IsPreOrder po

    module _ where
        open Monad mon        
        
        rawMonadT : RawMonadT M (CStateT S _P_ M)
        RawMonadT.rawInnerMonad rawMonadT = Monad.rawMonad mon
        RawMonadT.rawOuterMonad rawMonadT = CStateTMonad.rawMonad S po mon
        RawMonadT.lift rawMonadT m s = do
            x <- m
            return (s , reflexive , x)

    module MonadTProp (isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid po)) where

        open RawMonadT rawMonadT
        open RawMonad rawOuterMonad renaming (_>>=_ to _>>=C_ ; return to returnC)
        open Monad mon
        open IsIMonoid isIMonoid renaming 
            ( left-identity to left-identity-P
            ; right-identity to right-identity-P
            ; associative to associative-P)

        isMonadT : IsMonadT rawMonadT
        IsMonadT.isInnerMonad isMonadT = Monad.isMonad mon
        IsMonadT.isOuterMonad isMonadT = CStateTMonad.isMonad S po mon isIMonoid
        -- lift-return  : lift o returnM  === returnT {A = A}
        IsMonadT.lift-return isMonadT = extensPi \x -> extensPi \s ->
            (lift (return x)) s                                =<>
            return x >>= (\ x' -> return (s , reflexive , x')) =< left-identity >
            return (s , reflexive , x)                         =<>
            returnC x s                                        qed
        -- lift (m >>=M f) === (lift m) >>=T (lift o f)
        IsMonadT.lift-bind isMonadT {m} {f} = extensPi \s ->
            lift (m >>= f) s =<>

            (do
                x <- do 
                    y <- m
                    f y
                return (s , reflexive , x)
            ) =< associative >

            (do 
                y <- m
                x <- f y
                return (s , reflexive , x)
            ) =< (\_ _ -> sym left-identity-P) |pi2 (\h -> m >>= \y -> f y >>= \x -> return (s , h y x , x)) >

            (do 
                y <- m
                x <- f y
                return (s , transitive reflexive reflexive , x)
            ) =< (\_ _ -> sym left-identity) |pi2 (\h -> m >>= \y -> f y >>= h y) >

            (do 
                y <- m
                x <- f y
                (s'' , p' , x') <- do
                    return (s , reflexive , x)
                return (s'' , transitive reflexive p' , x')
            ) =< (\_ -> sym associative) |pi (\h -> m >>= h) >

            (do 
                y <- m
                (s'' , p' , x') <- do
                    x <- f y
                    return (s , reflexive , x)
                return (s'' , transitive reflexive p' , x')
            ) =< (\_ -> sym left-identity) |pi (\h -> m >>= h) >

            (do 
                y <- m
                (s' , p , y') <- do
                    return (s , reflexive , y)
                (s'' , p' , x') <- do
                    x <- f y'
                    return (s' , reflexive , x)
                return (s'' , transitive p p' , x')
            ) =< sym associative >

            (do
                (s' , p , y') <- do 
                    y <- m
                    return (s , reflexive , y)
                (s'' , p' , x') <- do
                    x <- f y'
                    return (s' , reflexive , x)
                return (s'' , transitive p p' , x')
            ) =<>

            ((lift m) >>=C (lift o f)) s qed

        monadT : MonadT M (CStateT S _P_ M)
        MonadT.rawMonadT monadT = rawMonadT
        MonadT.isMonadT  monadT = isMonadT

        module _ where
            open IsMonadT isMonadT

            preserves-left-absorb : {empty : {A : Set (i ~U~ u ~U~ c)} -> M A}{m' : A -> (CStateT S _P_ M B)} ->
                ({A B : Set (i ~U~ u ~U~ c)} {m : A -> M B} -> empty >>= m === empty) ->
                (lift empty) >>=C m' === (lift empty)
            preserves-left-absorb {empty} {m'} left-absorb = extensPi \s -> 
                (lift empty >>=C m') s =<>

                (do
                    (s1 , p1 , a) <- lift empty s
                    (s2 , p2 , b) <- m' a s1
                    return (s2 , transitive p1 p2 , b)
                ) =<>

                (do
                    (s1 , p1 , a) <- do
                        a <- empty
                        return (s , reflexive , a)
                    (s2 , p2 , b) <- m' a s1
                    return (s2 , transitive p1 p2 , b)
                ) =< (left-absorb || _>>= (\{(s1 , p1 , a) -> m' a s1 >>= _})) >

                (do
                    (s1 , p1 , a) <- empty
                    (s2 , p2 , b) <- m' a s1
                    return (s2 , transitive p1 p2 , b)
                ) =< left-absorb >

                empty =< sym left-absorb >

                (lift empty) s qed

            preserves-left-absorb-inside : {empty : {A : Set (i ~U~ u ~U~ c)} -> M A} ->
                ({A B : Set (i ~U~ u ~U~ c)} {m : A -> M B} -> empty >>= m === empty) ->
                {s : S} -> {m' : (exists[ s' of S ] s P s' and A) -> M (exists[ s' of S ] s P s' and B)} ->
                (lift empty s) >>= m' === (lift empty s)
            preserves-left-absorb-inside {empty} left-absorb {s} {m'} = 
                lift empty s >>= m'  =<>
                (empty >>= _) >>= m' =< left-absorb || _>>= _ >
                empty >>= m'         =< left-absorb >
                empty                =< sym left-absorb >
                empty >>= _          =<>
                lift empty s         qed

module CStateTMonadFailAlternative
    (S : Set u)
    {_P_ : S -> S -> Set c}
    (po : IsPreOrder _P_)
    {M : Set (i ~U~ u ~U~ c) -> Set j}
    {mon : Monad M}
    (mp : MonadFailAlternativeOver mon) where
    open IsPreOrder po 
    open MonadFailAlternativeOver mp hiding (rawMonadFailAlternativeOver; isMonadFailAlternativeOver; rawMonoid; rawAlternativeOver; isMonoid; isAlternativeOver)
    -- rawMonadC = CStateTMonad.rawMonad {i = i} S po mon
    open RawMonadT (CStateTMonadT.rawMonadT {i = i} S po mon) using (lift; rawOuterMonad)
    rawMonadC = rawOuterMonad

    module _ where
        module _ {X : Set _} where
            rawMonoid : RawMonoid (CStateT S _P_ M X)
            RawMonoid.epsilon rawMonoid = lift empty
            RawMonoid._<>_ rawMonoid m1 m2 s = m1 s <|> m2 s

        rawAlternativeOver : RawAlternativeOver (RawMonad.rawApplicative rawMonadC)
        RawAlternativeOver.rawMonoid rawAlternativeOver = rawMonoid

        rawMonadFailAlternativeOver : RawMonadFailAlternativeOver rawMonadC
        RawMonadFailAlternativeOver.rawAlternativeOver rawMonadFailAlternativeOver = rawAlternativeOver

    module _ (isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid po)) where
        open RawMonad rawOuterMonad using () renaming (_>>=_ to _>>=C_ ; return to returnC ; _>>_ to _>>C_)
        monadC = CStateTMonad.monad {i = i ~U~ u ~U~ c} S po mon isIMonoid
        open Monad monadC using (isApplicative; isMonad)
        open CStateTMonadT.MonadTProp {i = i} S po mon isIMonoid using (preserves-left-absorb)
        open Monad mon hiding (isApplicative)

        module _ {X : Set _} where
            isMonoid : IsMonoid (rawMonoid {X = X})
            IsMonoid.left-identity isMonoid {a} = extensPi \s -> 
                (lift empty) s <|> a s =<> 
                (empty >>= _) <|> a s  =< left-absorb || _<|> a s >
                empty <|> a s          =< left-identity-monoid >
                a s                    qed
            IsMonoid.right-identity isMonoid {a} = extensPi \s ->
                a s <|> (lift empty) s =<>
                a s <|> (empty >>= _)  =< left-absorb || a s <|>_ >
                a s <|> empty          =< right-identity-monoid >
                a s                    qed
            IsMonoid.associative isMonoid {a} {b} {c} = extensPi \s -> associative-monoid

        isAlternativeOver : IsAlternativeOver (Monad.applicative monadC) rawAlternativeOver
        IsAlternativeOver.isMonoid isAlternativeOver = isMonoid

        isMonadFailAlternativeOver : IsMonadFailAlternativeOver monadC rawMonadFailAlternativeOver
        IsMonadFailAlternativeOver.isAlternativeOver isMonadFailAlternativeOver = isAlternativeOver
        IsMonadFailAlternativeOver.left-absorb isMonadFailAlternativeOver {f} = preserves-left-absorb left-absorb

        monadFailAlternativeOver : MonadFailAlternativeOver monadC
        MonadFailAlternativeOver.rawMonadFailAlternativeOver monadFailAlternativeOver = rawMonadFailAlternativeOver
        MonadFailAlternativeOver.isMonadFailAlternativeOver monadFailAlternativeOver = isMonadFailAlternativeOver

-- TODO: lots of code doubling down there...
module CStateTMonadPlus 
    (S : Set u)
    {_P_ : S -> S -> Set c}
    (po : IsPreOrder _P_)
    {M : Set (i ~U~ u ~U~ c) -> Set j}
    (mp : MonadPlus M) where  
    open IsPreOrder po 

    module _ where
        open MonadPlus mp hiding (rawMonadPlus)
        open RawMonadT (CStateTMonadT.rawMonadT {i = i} S po monad) using (lift)

        rawMonadPlus : RawMonadPlus {i ~U~ u ~U~ c} (CStateT S _P_ M)
        RawMonoid.epsilon (RawMonadPlus.rawMonoid rawMonadPlus) = lift mzero
        RawMonoid._<>_ (RawMonadPlus.rawMonoid rawMonadPlus) m1 m2 s = m1 s <|> m2 s
        RawMonadPlus.rawMonad rawMonadPlus = CStateTMonad.rawMonad S po monad

    module _ (isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid po)) where
        open MonadPlus mp hiding (rawMonadPlus; isMonadPlus)
        open RawMonadT (CStateTMonadT.rawMonadT {i = i} S po monad) using (lift; rawOuterMonad)         
        open RawMonad rawOuterMonad using () renaming (_>>=_ to _>>=C_ ; return to returnC ; _>>_ to _>>C_)

        isMonadPlus : IsMonadPlus rawMonadPlus
        IsMonoid.left-identity (IsMonadPlus.isMonoid isMonadPlus) {a} = extensPi \s -> 
            (lift mzero) s <|> a s =<> 
            (mzero >>= _) <|> a s  =< left-absorb || _<|> a s >
            mzero <|> a s          =< left-identity-monoid >
            a s                    qed
        IsMonoid.right-identity (IsMonadPlus.isMonoid isMonadPlus) {a} = extensPi \s ->
            a s <|> (lift mzero) s =<>
            a s <|> (mzero >>= _)  =< left-absorb || a s <|>_ >
            a s <|> mzero          =< right-identity-monoid >
            a s                    qed
        IsMonoid.associative (IsMonadPlus.isMonoid isMonadPlus) {a} {b} {c} = extensPi \s -> associative-monoid
        IsMonadPlus.isMonad isMonadPlus = CStateTMonad.isMonad S po monad isIMonoid
        IsMonadPlus.left-absorb isMonadPlus {f} = extensPi \s -> 
            ((lift mzero) >>=C f) s =< associative >
            (mzero >>= _)           =< left-absorb >
            mzero                   =< sym left-absorb >
            (lift mzero) s          qed
        IsMonadPlus.right-absorb isMonadPlus {m} = extensPi \s -> 
            (m >>C (lift mzero)) s              =<>
            (m s >>= \_ -> (mzero >>= _) >>= _) =< (\_ -> left-absorb) |pi (\h -> m s >>= \{(s , p , x) -> h (s , p , x) >>= \{(s' , p' , x') -> return (s' , transitive p p' , x')}}) >
            (m s >>= \_ -> mzero >>= _)         =< (\_ -> left-absorb) |pi (\h -> m s >>= h) >
            (m s >>= \_ -> mzero)               =< right-absorb >
            mzero                               =< sym left-absorb >
            (lift mzero) s                      qed  

        monadPlus : MonadPlus {i ~U~ u ~U~ c} (CStateT S _P_ M)
        MonadPlus.rawMonadPlus monadPlus = rawMonadPlus
        MonadPlus.isMonadPlus monadPlus = isMonadPlus

module CStateTMonadError
    (S : Set u)
    {_P_ : S -> S -> Set c}
    (po : IsPreOrder _P_)
    {M : Set (i ~U~ u ~U~ c) -> Set j}
    {Err : Set e} 
    {mon : Monad M}
    (me : MonadErrorOver mon Err) where 
    private
        rawMonadC = CStateTMonad.rawMonad {i = i} S po mon

    module _ where
        open MonadErrorOver me hiding (rawMonadErrorOver)
        open RawMonadT (CStateTMonadT.rawMonadT {i = i} S po mon) using (lift)

        rawMonadErrorOver : RawMonadErrorOver {i = i} rawMonadC Err
        RawMonadErrorOver.throw rawMonadErrorOver err s = throw err
        RawMonadErrorOver.catch rawMonadErrorOver ma ema s = catch (ma s) (flip ema s) -- warning: state gets lost!

        throwStatePreserving : {A : Set i} -> (S -> Err) -> CStateT S _P_ M A
        throwStatePreserving f s = throw (f s)

    module _ (isIMonoid : IsIMonoid (IsPreOrder.rawIMonoid po)) where 
        open MonadErrorOver me hiding (rawMonadErrorOver; isMonadErrorOver)
        open RawMonadErrorOver rawMonadErrorOver
        private
            isMonadC    = CStateTMonad.isMonad {i = i} S po mon isIMonoid
            monadC      = CStateTMonad.monad   {i = i} S po mon isIMonoid

        isMonadErrorOver : IsMonadErrorOver isMonadC rawMonadErrorOver
        IsMonadErrorOver.left-absorb isMonadErrorOver = extensPi \s -> left-absorb
        IsMonadErrorOver.throw-catch isMonadErrorOver = extensPi \s -> throw-catch

        monadErrorOver : MonadErrorOver {i = i} monadC Err
        MonadErrorOver.rawMonadErrorOver monadErrorOver = rawMonadErrorOver
        MonadErrorOver.isMonadErrorOver  monadErrorOver = isMonadErrorOver