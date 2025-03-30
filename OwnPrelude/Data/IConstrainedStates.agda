{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.IConstrainedStates where

open import ASCIIPrelude.ASCIIPrelude
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.IPreOrders
-- open import OwnPrelude.Relation.Properties
open import OwnPrelude.Categorical.IMonads
open import OwnPrelude.Categorical.IMonadTs
open TupIdxIMonadT
open import OwnPrelude.Categorical.IMonoids
open import OwnPrelude.Categorical.Monoids
open import OwnPrelude.Categorical.MonadPlus
open import OwnPrelude.Categorical.Alternatives
open import OwnPrelude.Categorical.MonadFailAlternatives
open import OwnPrelude.Categorical.MonadErrors

open ExistsSyntax

private
    variable
        cl ul ul' ujl il jl ol : Level
        n n' : Nat
        A B C X Y Z L S : Set il
        F G M : Set il -> Set jl
        a b x y z m : A
        f g : A -> B
    


module ICBase
    {I : Set ul'}
    {S : I -> Set ul}
    (_P'_ : (i j : I) -> S i -> S j -> Set cl)
    {J : Set ujl}
    (M : J -> J -> Set (il ~U~ ul ~U~ cl) -> Set ol) where

    module _ where
        private
            _P_ : {i j : I} -> S i -> S j -> Set cl
            _P_ {i} {j} = _P'_ i j

        -- \tagcode{ICStateT}

        ICStateT : (I -x- J) -> (I -x- J) -> Set il -> Set (ol ~U~ ul)
        ICStateT (i , j) (i' , j') X = (s : S i) -> M j j' (exists[ s' of S i' ] (s P s') -x- X)

    private variable
        h i j k : I -x- J

    module StateActions
        (po : IsIPreOrder {A = S}  _P'_) 
        (mon : IMonad M)
        {X : Set il} where
        open IsIPreOrder po
        open IMonad mon 

        getS : (S (fst i) -> X) -> ICStateT i i X
        getS f s = return (s , reflexive , f s)

        local : ICStateT i i X -> ICStateT i i X
        local m s = do
            (_ , _ , x) <- m s
            return (s , reflexive , x)


module _
    {I : Set ul'}
    {S : I -> Set ul}
    (_P'_ : (i j : I) -> S i -> S j -> Set cl)
    {J : Set ujl}
    (M : J -> J -> Set (ul ~U~ cl) -> Set ol) where
    open ICBase {il = ul} _P'_ M
    
    private variable
        i i' : I
        j j' : J

    module GetAction 
        (po : IsIPreOrder {A = S}  _P'_) 
        (mon : IMonad M) where
        open IsIPreOrder po
        open IMonad mon
        
        get : ICStateT (i , j) (i , j) (S i)
        get s = return (s , reflexive , s)

module ICStateTMonad
    {I : Set ul'}
    {S : I -> Set ul}
    {_P'_ : (i j : I) -> S i -> S j -> Set cl}
    (po : IsIPreOrder {A = S}  _P'_)
    {J : Set ujl}
    {M : J -> J -> Set (il ~U~ ul ~U~ cl) -> Set ol}
    (mon : IMonad M) where
    open IsIPreOrder po
    open ICBase {il = il} _P'_ M

    private variable
        i i' i'' : I
        j j' j'' : J
    
    module _ where
        open IMonad mon hiding (rawIMonad)

        rawIMonad : RawIMonad {il = il} ICStateT
        RawIMonad.return rawIMonad x s = return (s , reflexive , x)
        RawIMonad._>>=_ rawIMonad mx fmy s = do
            (s'  , p  , a) <- mx s
            (s'' , p' , b) <- fmy a s'
            return 
                ( s''
                ,  (p  :T: s  P s'  [premise]
                    p' :T: s' P s'' [premise]
                    -----------------------------
                    transitive p p' :T: s P s'')
                , b)

        _>>P=_ : ICStateT (i , j) (i' , j') X -> 
            ((exists[ s of S i ] exists[ s' of S i' ] s P s') -> X -> ICStateT (i' , j') (i'' , j'') Y) ->
            ICStateT (i , j) (i'' , j'') Y
        (mx >>P= fmy) s = do
            (s'  , p  , x) <- mx s
            (s'' , p' , y) <- fmy (_ , _ , p) x s'
            return (s'' , transitive p p' , y)


    module _ 
        (isIMonoid : IsIMonoid (IsIPreOrder.rawIMonoid po)) where

        open RawIMonad rawIMonad renaming (return to returnS; _>>=_ to _>>=S_; _>=>_ to _>=>S_)
        open IMonad mon hiding (rawIMonad; isIMonad)
        open IsIMonoid isIMonoid renaming 
            ( left-identity to left-identity-P
            ; right-identity to right-identity-P
            ; associative to associative-P)
        
        isIMonad : IsIMonad rawIMonad
        -- return x >>= f === f x
        IsIMonad.left-identity isIMonad {x} {f} = extensPi \s ->
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
        IsIMonad.right-identity isIMonad {m} = extensPi \s ->
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
        IsIMonad.associative isIMonad {m} {f} {g} = extensPi \s -> 
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
                (s''' , p'''' , c) <- return (s''' , transitive p'' p''' , c :T: exists[ s''' of S _ ] s' P s''' -x- _)
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
 
        monad : IMonad {il = il} ICStateT
        IMonad.rawIMonad monad = rawIMonad
        IMonad.isIMonad  monad = isIMonad


module ICStateTMonadT 
    {I : Set ul'}
    {S : I -> Set ul}
    {_P'_ : (i j : I) -> S i -> S j -> Set cl}
    (po : IsIPreOrder {A = S}  _P'_)
    {J : Set ujl}
    {M : J -> J -> Set (il ~U~ ul ~U~ cl) -> Set ol}
    (mon : IMonad M) where
    open IsIPreOrder po
    open ICBase {il = ul ~U~ cl ~U~ il} _P'_ M
    
    private variable
        ij ij' : I -x- J
        i i' i'' : I
        j j' j'' : J

    module _ where
        open IMonad mon        
        
        rawIMonadT : RawIMonadT M ICStateT
        RawIMonadT.rawInnerIMonad rawIMonadT = IMonad.rawIMonad mon
        RawIMonadT.rawOuterIMonad rawIMonadT = ICStateTMonad.rawIMonad po mon
        RawIMonadT.lift rawIMonadT m s = do
            x <- m
            return (s , reflexive , x)

    module IMonadTProp (isIMonoid : IsIMonoid (IsIPreOrder.rawIMonoid po)) where

        open RawIMonadT rawIMonadT
        open RawIMonad rawOuterIMonad renaming (_>>=_ to _>>=C_ ; return to returnC)
        open IMonad mon
        open IsIMonoid isIMonoid renaming 
            ( left-identity to left-identity-P
            ; right-identity to right-identity-P
            ; associative to associative-P)

        isIMonadT : IsIMonadT rawIMonadT
        IsIMonadT.isInnerIMonad isIMonadT = IMonad.isIMonad mon
        IsIMonadT.isOuterIMonad isIMonadT = ICStateTMonad.isIMonad po mon isIMonoid
        -- lift-return  : lift o returnM  === returnT {A = A}
        IsIMonadT.lift-return isIMonadT = extensPi \x -> extensPi \s ->
            (lift (return x)) s                                =<>
            return x >>= (\ x' -> return (s , reflexive , x')) =< left-identity >
            return (s , reflexive , x)                         =<>
            returnC x s                                        qed
        -- lift (m >>=M f) === (lift m) >>=T (lift o f)
        IsIMonadT.lift-bind isIMonadT {m} {f} = extensPi \s ->
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

        monadT : IMonadT M ICStateT
        IMonadT.rawIMonadT monadT = rawIMonadT
        IMonadT.isIMonadT  monadT = isIMonadT

        module _ where
            open IsIMonadT isIMonadT

            liftErr : 
                (empty : {A : Set (il ~U~ ul ~U~ cl)}{j j' : J} -> M j j' A) ->
                ICStateT ij ij' A
            liftErr empty s = empty 

            preserves-left-absorb : {empty : {A : Set (il ~U~ ul ~U~ cl)}{j j' : J} -> M j j' A}{m' : A -> (ICStateT ij ij' B)} ->
                ({A B : Set (il ~U~ ul ~U~ cl)}{j j' : J} {m' : A -> M j j' B} -> empty >>= m' === empty {j = j}) ->
                (liftErr {ij = ij} empty) >>=C m' === (liftErr empty)
            preserves-left-absorb {empty} {m'} left-absorb = extensPi \s -> 
                (liftErr empty >>=C m') s =<>

                (do
                    (s1 , p1 , a) <- liftErr empty s
                    (s2 , p2 , b) <- m' a s1
                    return (s2 , transitive p1 p2 , b)
                ) =<>

                (do
                    (s1 , p1 , a) <- empty
                    (s2 , p2 , b) <- m' a s1
                    return (s2 , transitive p1 p2 , b)
                ) =< left-absorb >

                empty =<>

                (liftErr empty) s qed

            preserves-left-absorb-inside : {empty : {A : Set (il ~U~ ul ~U~ cl)}{j j' : J} -> M j j' A} ->
                ({A B : Set (il ~U~ ul ~U~ cl)}{j j' j'' : J}{m : A -> M j' j'' B} -> empty {j = j} >>= m === empty) ->
                {s : S i} -> {m' : (exists[ s' of S i ] s P s' and A) -> M j j' (exists[ s' of S i' ] s P s' and B)} ->
                (liftErr {ij = (i , j)} empty s) >>= m' === (liftErr empty s)
            preserves-left-absorb-inside {empty} left-absorb {s} {m'} = 
                liftErr empty s >>= m' =<>
                empty >>= m'           =< left-absorb >
                empty                  =<>
                liftErr empty s        qed