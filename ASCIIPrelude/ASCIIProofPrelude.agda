{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module ASCIIPrelude.ASCIIProofPrelude where

open import ASCIIPrelude.ASCIIPrelude
open PolyUnit
open PolyZero
open PolyFin
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monads

open ExistsSyntax

private
    variable
        i j k l : Level
        n n' n'' n1 n2 n3 : Nat
        ST : Set i
        a b c v x y z fx T mes g f p q fa fv h A B C X Y Z vec : ST
        M F G : Set i -> Set j

module NatProp where
    open NatOp hiding (_leq_)
    module _ where
        CoverNat : Nat -> Nat -> Set
        CoverNat 0 0 = Unit
        CoverNat (1+ x) (1+ y) = x === y
        CoverNat _ _           = Zero

        encodeReflNat : CoverNat a a
        encodeReflNat {a = 0} = unit
        encodeReflNat {a = 1+ x}      = refl

        encodeNat : {a b : Nat} -> a === b -> CoverNat a b
        encodeNat {a} = J (\b _ -> CoverNat a b) encodeReflNat


    0-left-identity : x === x + 0
    0-left-identity {x = 0} = refl
    0-left-identity {x = 1+ x} = 0-left-identity || 1+_

    right-step-+ : x + (1+ y) === 1+ (x + y)
    right-step-+ {x = 0} {(y)} = refl
    right-step-+ {x = 1+ x} {(y)} = right-step-+ || 1+_

    comm-+ : x + y === y + x
    comm-+ {x = 0} {(y)} = 0-left-identity
    comm-+ {x = 1+ x} {y = 0} = comm-+ {x} {0} || 1+_
    comm-+ {x = 1+ x} {y = 1+ y} = x + (1+ y) =< right-step-+ > 1+ (x + y) =< comm-+ {x} {y} || 1+_ > 1+ (y + x) =< sym right-step-+ > y + (1+ x) qed || 1+_

    assoc-+ : x + (y + z) === (x + y) + z
    assoc-+ {(zero)} {(y)} {(z)} = refl
    assoc-+ {1+_ x} {(y)} {(z)} = assoc-+ {x} {y} {z} || 1+_

    0-absorb-left : x + y === 0 -> x === 0
    0-absorb-left {x = 0} {(y)} x+y=0 = refl
    0-absorb-left {x = 1+ x} {(y)} x+y=0 = absurd (encodeNat x+y=0)

    0-absorb-right : x + y === 0 -> y === 0
    0-absorb-right {x} {y} x+y=0 = coerce (0-absorb-left x+y=0 || (\x -> x + y === 0)) x+y=0


    _leq_ : Nat -> Nat -> Set
    x leq y = exists[ n ] (x + n === y)

    leq-0' : (1+ n) leq 0 -> Zero {lzero}
    leq-0' (n , eq) = encodeNat eq

    leq-0 : y leq 0 -> y === 0
    leq-0 (n , eq) = 0-absorb-left eq

    leq-zero : 0 leq n
    leq-zero {n} = n , refl

    leq-refl : x leq x
    leq-refl {x} = 0 , sym 0-left-identity

    leq-trans : a leq b -> b leq c -> a leq c
    leq-trans {a} {b} {c} (n , alb) (n' , blc) = n + n' , (
        a + (n + n') =< assoc-+ {a} {n} {n'} >
        (a + n) + n' =< alb || _+ n' >
        b + n' =< blc >
        c qed )

    leq-pres-+ : x leq y -> x leq (y + n)
    leq-pres-+ {x} {y} {n} (n' , eq) = (n + n') , (
        x + (n + n') =< comm-+ {n} {n'} || x +_ >
        x + (n' + n) =< assoc-+ {x} {n'} {n} >
        (x + n') + n =< eq || _+ n >
        y + n qed
        )

    pred-eq : 1+ n === 1+ n' -> n === n'
    pred-eq {n = 0} {n' = 0} eq = refl
    pred-eq {n = 0} {n' = 1+ n'} eq = absurd (encodeNat (encodeNat eq))
    pred-eq {n = 1+ n} {(n')} eq = encodeNat eq

    leq-pred : (1+ n) leq (1+ n') -> n leq n'
    leq-pred (n'' , eq) = n'' , pred-eq eq

    leq-suc : n leq n' -> (1+ n) leq (1+ n')
    leq-suc (n'' , eq) = n'' , (eq || 1+_)

    leq-suc' : n leq n' -> n leq (1+ n')
    leq-suc' {n} {n'} (n'' , eq) = 1+ n'' , trans (right-step-+ {x = n} {y = n''}) (eq || 1+_) 


    comm-max : max x y === max y x
    comm-max {x = 0}    {y = 0}    = refl
    comm-max {x = 0}    {y = 1+ y} = refl
    comm-max {x = 1+ x} {y = 0}    = refl 
    comm-max {x = 1+ x} {y = 1+ y} = comm-max {x} {y} || 1+_

    assoc-max : max x (max y z) === max (max x y) z
    assoc-max {x = 0}                          = refl
    assoc-max {x = 1+ x} {y = 0}               = refl
    assoc-max {x = 1+ x} {y = 1+ y} {z = 0}    = refl
    assoc-max {x = 1+ x} {y = 1+ y} {z = 1+ z} = assoc-max {x} {y} {z} || 1+_

    idem-max : max x x === x
    idem-max {x = 0}    = refl 
    idem-max {x = 1+ x} = idem-max {x} || 1+_

    max-suc-left : max (1+ n) n === 1+ n
    max-suc-left {0}    = refl
    max-suc-left {1+ n} = max-suc-left {n = n} || 1+_

    left-leq-max : {x y : Nat} -> x leq (max x y)
    left-leq-max {x = zero} {y} = y , refl
    left-leq-max {x = 1+ x} {y = zero} = leq-refl 
    left-leq-max {x = 1+ x} {y = 1+ y} = leq-suc left-leq-max

    right-leq-max : {x y : Nat} -> y leq (max x y)
    right-leq-max {x = zero} {y} = leq-refl 
    right-leq-max {x = 1+ x} {y = zero} = (1+ x) , refl
    right-leq-max {x = 1+ x} {y = 1+ y} = leq-suc right-leq-max

module FinProp where

    open import Data.Fin.Properties using () renaming (
        toℕ-fromℕ to finToNat-o-maxFinFromNat'
        )
    finToNat-o-maxFinFromNat = propToPath o finToNat-o-maxFinFromNat'

    finToNat-o-injectFin1 : forall {n} -> (finToNat o injectFin1 {i} {n'}) n === finToNat n
    finToNat-o-injectFin1 {i} {n = liftL f0'} = refl
    finToNat-o-injectFin1 {i} {n = liftL (f1+' n)} = finToNat-o-injectFin1 {i} || 1+_

    module _ {i} {B : Nat -> Set j} where
        foldFinNat : ({n : Nat} -> Fin {i} n' -> B n -> B (1+ n)) -> B 0 -> B n'
        foldFinNat {n'} f b = coerce (finToNat-o-maxFinFromNat n' || B) 
            (foldFin' (B o finToNat) 
                (\i' b -> f {finToNat i'} i' (coerce (finToNat-o-injectFin1 {i} || B) b)) 
                b 
                (maxFinFromNat n'))
    
    module _ where
        ¬Fin0 : Fin {i} 0 -> Zero {i}
        ¬Fin0 ()

    module _ {i} where
        CoverFin : Fin {i} n -> Fin {i} n -> Set i
        CoverFin {n = 0} x y = Unit
        CoverFin {n = 1+ n} x y = foldFin' (\_ -> Set i) 
            (\x' _ -> foldFin' (\_ -> Set i) (\y' _ -> x' === y') Zero y) 
            (foldFin' (\_ -> Set i) (\_ _ -> Zero) Unit y) 
            x

        encodeReflFin : {a : Fin {i} n} -> CoverFin a a
        encodeReflFin {n = 0}    {a} = unit
        encodeReflFin {n = 1+ 0} {a} = foldFin' (\a -> CoverFin a a) (\i eq -> absurd (¬Fin0 i)) unit a
        encodeReflFin {n = 1+ (1+ n)} {a} = foldFin' (\a -> CoverFin a a) (\i eq -> refl) unit a

        encodeFin : {a b : Fin {i} n} -> a === b -> CoverFin a b
        encodeFin {a} = J (\b _ -> CoverFin a b) (encodeReflFin {a = a})

    Vec : {j i : Level} -> Set i -> Nat -> Set (j ~U~ i)
    Vec {j} A n = Fin {j} n -> A

    module _ {A : Set i} where
        open ListOp
        
        []v : Vec {j} A 0
        []v ()

        vec0-eq : {v1 v2 : Vec {j} A 0} -> v1 === v2
        vec0-eq {v1} {v2} = extens (absurd o ¬Fin0)

        fin1-eq : {v1 v2 : Fin {j} 1} -> v1 === v2
        fin1-eq {v1} {v2} = foldFin' (\j -> j === v2) (\j eq -> absurd (¬Fin0 j)) (foldFin' (\j -> f0 === j) (\j eq -> absurd (¬Fin0 j)) refl v2) v1

        infixr 20 _::v_
        _::v_ : A -> Vec {j} A n -> Vec A (1+ n)
        (a ::v vec) fin = foldFin' (\_ -> A) (\i _ -> vec i) a fin 

        drop1 : Vec {j} A (1+ n) -> Vec A n
        drop1 vec = vec o f1+_
        
        cons-drop-prop : {vec : Vec {j} A n} -> drop1 (a ::v vec) === vec
        cons-drop-prop {n = 0} = extens (absurd o ¬Fin0)
        cons-drop-prop {n = 1+ n} {a} {vec} = extens $ foldFin' 
            (\i ->  drop1 (a ::v vec) i === vec i) 
            (\i eq -> refl) 
            refl

        unconsVec : Vec {j} A (1+ n) -> A -x- Vec A n
        unconsVec {n} vec = vec f0 , drop1 vec

        uncons-cons-vec-prop : forall {n a} {vec : Vec {j} A n} -> unconsVec {n = n} (a ::v vec) === (a , vec)
        uncons-cons-vec-prop {n} {a} {vec} = 
            unconsVec {n = n} (a ::v vec)        =<>
            ((a ::v vec) f0 , drop1 (a ::v vec)) =< cons-drop-prop || (a ::v vec) f0 ,_ >
            (a , vec)                            qed

        uncons-uncons : {vec : Vec {j} A (1+ n)} -> (vec f0 ::v drop1 vec) === vec
        uncons-uncons {j} {n = 0} {vec} = extens \fin ->
            (vec f0 ::v drop1 vec) fin =< fin1-eq {j} {fin} {f0} || (vec f0 ::v drop1 vec) >
            (vec f0 ::v drop1 vec) f0  =<>
            vec f0                     =< sym (fin1-eq {j} {fin} {f0}) || vec >
            vec fin                    qed
        uncons-uncons {n = 1+ n} {vec} = extens (foldFin' (\i -> (vec f0 ::v drop1 vec) i === vec i) (\i eq -> refl) refl)

        vecToList : Vec {j} A n -> List A
        vecToList {n} vec = reverse (foldFin' (\_ -> List A) (\i lst -> vec i :: lst) [] (maxFinFromNat n))

    mapVec : (A -> B) -> Vec {j} A n -> Vec {j} B n
    mapVec f vec = f o vec

    module _ {A : Set i} {B : Set j} {f : A -> B} where
        mapVec-cons : mapVec {n = 1+ n} f (a ::v vec) === f a ::v mapVec f vec
        mapVec-cons {n = 0} {a} {vec} = extens \fin -> trans (fin1-eq {i = i} {A = A} {v1 = fin} {v2 = f0} || mapVec f (a ::v vec)) (fin1-eq {i = i} {A = A} {v1 = f0} {v2 = fin} || (f a ::v mapVec f vec))
        mapVec-cons {n = 1+ n} {a} {vec} = extens (foldFin' (\i -> mapVec f (a ::v vec) i === (f a ::v mapVec f vec) i) 
            (\i eq -> refl) 
            refl)

    -- testVec : List Nat
    -- testVec = vecToList (1 ::v 2 ::v 3 ::v []v)

    module MonadSwitch {M : Set i -> Set i} (mon : Monad M) (lcmon : LocallyCommutativeMonad mon) where
        open EndoMonad mon
        open LocallyCommutativeMonad lcmon
        
        switch : Vec {i} (M A) n -> M (Vec {i} A n)
        switch {A} {n = 0} vec = return []v
        switch {A} {n = 1+ n} vec = (| (vec f0) ::v (switch (drop1 vec)) |)

        switch-return : switch {n = n} o mapVec {A = A} return === return
        switch-return {n = 0} = extens \_ -> vec0-eq || return
        switch-return {n = 1+ n} = extens \vec -> 
            (switch o mapVec return) vec                                  =<>
            switch (return o vec)                                         =<>
            (| ((return o vec) f0) ::v (switch (drop1 (return o vec))) |) =<>
            (| (return (vec f0)) ::v (switch (drop1 (return o vec))) |)   =<>
            (| (return (vec f0)) ::v (switch (return o drop1 vec)) |)     =< (switch-return || (_$ drop1 vec)) || (\h -> (| (return (vec f0)) ::v h |)) >
            (| (return (vec f0)) ::v (return (drop1 vec)) |)              =< homomorphism || (\h -> h <*> return (drop1 vec)) >
            (| (vec f0 ::v_) (return (drop1 vec)) |)                      =< homomorphism >
            return (vec f0 ::v drop1 vec)                                 =< uncons-uncons || return >
            return vec                                                    qed

        switch-fmap-fmap : switch o (mapVec {n = n} o fmap) f === (fmap o mapVec) f o switch
        switch-fmap-fmap {n = 0} {f} = extens \_ -> 
            return []v =< vec0-eq || return >
            return (mapVec f []v) =< sym left-identity >
            return []v >>= return o mapVec f =< sym fmap-simplified || (_$ return []v) >
            (fmap o mapVec) f (return []v) qed
        switch-fmap-fmap {n = 1+ n} {f} = extens \vec ->
            (switch o (mapVec o fmap) f) vec =<>
            switch (mapVec (fmap f) vec) =<>

            (| ((mapVec (fmap f) vec) f0) ::v (switch (drop1 (mapVec (fmap f) vec))) |) =< binOp-simplified >

            (do
                v0 <- (mapVec (fmap f) vec) f0
                lst <- switch (drop1 (mapVec (fmap f) vec))
                return (v0 ::v lst)
            ) =<>

            (do
                v0 <- (mapVec (fmap f) vec) f0
                lst <- switch (mapVec (fmap f) (drop1 vec))
                return (v0 ::v lst)
            ) =< (\_ -> switch-fmap-fmap || (_$ drop1 vec)) |f (\h -> (mapVec (fmap f) vec) f0 >>= \v0 -> h v0 >>= return o (v0 ::v_)) >

            (do
                v0  <- fmap f (vec f0)
                lst <- fmap (mapVec f) (switch (drop1 vec))
                return (v0 ::v lst)
            ) =< fmap-bind || (_$ vec f0) >

            (do
                v0  <- vec f0
                lst <- fmap (mapVec f) (switch (drop1 vec))
                return (f v0 ::v lst)
            ) =< (\_ -> fmap-bind || (_$ switch (drop1 vec))) |f (vec f0 >>=_) >

            (do
                v0 <- vec f0
                lst <- switch (drop1 vec)
                return (f v0 ::v mapVec f lst)
            ) =< (\_ _ -> sym (mapVec-cons {f = f})) |f2 (\h -> vec f0 >>= \v0 -> switch (drop1 vec) >>= \lst -> return (h v0 lst)) >

            (do
                v0 <- vec f0
                lst <- switch (drop1 vec)
                return (mapVec f (v0 ::v lst))
            ) =< (\_ _ -> sym left-identity) |f2 (\h -> vec f0 >>= \v0 -> switch (drop1 vec) >>= h v0) >

            (do
                v0 <- vec f0
                lst <- switch (drop1 vec)
                res <- return (v0 ::v lst)
                return (mapVec f res)
            ) =< (\_ -> sym associative) |f vec f0 >>=_ >

            (do
                v0 <- vec f0
                res <- (do
                    lst <- switch (drop1 vec)
                    return (v0 ::v lst))
                return (mapVec f res)
            ) =< sym associative >

            (do
                res <- (do
                    v0 <- vec f0
                    lst <- switch (drop1 vec)
                    return (v0 ::v lst))
                return (mapVec f res)
            ) =< (sym fmap-simplified || (_$ do
                    v0 <- vec f0
                    lst <- switch (drop1 vec)
                    return (v0 ::v lst))) >

            (do
                fmap (mapVec f) (do
                    v0 <- vec f0
                    lst <- switch (drop1 vec)
                    return (v0 ::v lst))
            ) =< sym binOp-simplified || fmap (mapVec f) >

            fmap (mapVec f) (switch vec) =<>
            ((fmap o mapVec) f o switch) vec qed

        switch-join : forall {A} -> switch {A = A} o mapVec {n = n} join === switch >=> switch
        switch-join {n = 0} = extens \_ -> sym left-identity 
        switch-join {n = 1+ n} = extens \vec -> 
            switch (join o vec) =<>
            (| ((join o vec) f0) ::v (switch (drop1 (join o vec))) |) =<>
            (| ((join o vec) f0) ::v (switch (join o drop1 vec)) |) =< (switch-join || (_$ drop1 vec))|| (\h -> (| ((join o vec) f0) ::v h |)) >
            (| ((join o vec) f0) ::v ((switch >=> switch) (drop1 vec)) |) =< binOp-simplified >

            (do
                v0 <- join (vec f0)
                lst <- (switch >=> switch) (drop1 vec)
                return (v0 ::v lst)
            ) =<>

            (do
                v0 <- join (vec f0)
                lst <- switch (drop1 vec) >>= switch 
                return (v0 ::v lst)
            ) =< (\_ -> associative) |f (join (vec f0)) >>=_ >

            (do
                v0 <- join (vec f0)
                lst' <- switch (drop1 vec)
                lst <- switch lst'
                return (v0 ::v lst)
            ) =<>

            (do
                v0 <- (vec f0) >>= id
                lst' <- switch (drop1 vec)
                lst <- switch lst'
                return (v0 ::v lst)
            ) =< associative >

            (do
                v0' <- vec f0
                v0 <- v0'
                lst' <- switch (drop1 vec)
                lst <- switch lst'
                return (v0 ::v lst)
            ) =< (\_ -> commute) |f (vec f0 >>=_) > 
            -- This is where commutativity is needed!

            (do
                v0' <- vec f0
                lst' <- switch (drop1 vec)
                v0 <- v0'
                lst <- switch lst'
                return (v0 ::v lst)
            ) =< (\_ _ _ -> sym cons-drop-prop) |pi3 (\h -> do
                                                            v0' <- vec f0
                                                            lst' <- switch (drop1 vec)
                                                            v0 <- v0'
                                                            lst <- switch (h v0' lst' v0)
                                                            return (v0 ::v lst)
                                                        ) >

            (do
                v0' <- vec f0
                lst' <- switch (drop1 vec)
                v0 <- (v0' ::v lst') f0
                lst <- switch (drop1 (v0' ::v lst'))
                return (v0 ::v lst)
            ) =< (\_ _ -> sym left-identity) |f2 (\h -> vec f0 >>= \v0' -> switch (drop1 vec) >>= h v0') >

            (do
                v0' <- vec f0
                lst' <- switch (drop1 vec)
                vec' <- return (v0' ::v lst')
                v0 <- vec' f0
                lst <- switch (drop1 vec')
                return (v0 ::v lst)
            ) =< (\_ -> sym associative) |f vec f0 >>=_ >

            (do
                v0' <- vec f0
                vec' <- do
                    lst' <- switch (drop1 vec)
                    return (v0' ::v lst')
                v0 <- vec' f0
                lst <- switch (drop1 vec')
                return (v0 ::v lst)
            ) =< sym associative >

            (do
                vec' <- do
                    v0' <- vec f0
                    lst' <- switch (drop1 vec)
                    return (v0' ::v lst')
                v0 <- vec' f0
                lst <- switch (drop1 vec')
                return (v0 ::v lst)
            ) =< sym binOp-simplified || (_>>= \vec' -> vec' f0 >>= \v0 -> switch (drop1 vec') >>= _) > 

            (do
                vec' <- (| (vec f0) ::v (switch (drop1 vec)) |)
                v0 <- vec' f0
                lst <- switch (drop1 vec')
                return (v0 ::v lst)
            ) =< (\_ -> sym binOp-simplified) |f (| (vec f0) ::v (switch (drop1 vec)) |) >>=_ > 

            (do
                vec' <- (| (vec f0) ::v (switch (drop1 vec)) |)
                (| (vec' f0) ::v (switch (drop1 vec')) |)
            ) =<> 

            ((| (vec f0) ::v (switch (drop1 vec)) |) >>= switch) =< _||_ {a = vec} (sym uncons-uncons) (\h -> switch h >>= switch) >
            (switch (vec f0 ::v drop1 vec) >>= switch) =<>
            (switch >=> switch) (vec f0 ::v drop1 vec) =< _||_ {b = vec} uncons-uncons (switch >=> switch) > 
            (switch >=> switch) vec qed

module SigmaProp where

    module _ {i j} {A : Set i} {B : A -> Set j} where
        CoverSig : Sigma A B -> Sigma A B -> Set (i ~U~ j)
        CoverSig (a1 , b1) (a2 , b2) = Sigma (a1 === a2) (\ a1=a2 -> b1 === (coerce (sym a1=a2 || B) b2))

        encodeReflSig : CoverSig a a
        encodeReflSig {a = a , b} = refl , \i -> transp (\j -> B a) (~ i) b

        encodeSig : {a b : Sigma A B} -> a === b -> CoverSig a b
        encodeSig {a} = J (\b _ -> CoverSig a b) encodeReflSig