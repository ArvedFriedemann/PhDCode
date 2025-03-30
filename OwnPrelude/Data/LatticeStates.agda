{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
-- {-# OPTIONS --safe #-} -- currently not safe due to indexed monoid postulate of lattice pre-order
module OwnPrelude.Data.LatticeStates where

open import ASCIIPrelude.ASCIIPrelude 
open PolyZero
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Data.ConstrainedStates
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.MonadicVariables
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadTs
open import OwnPrelude.Categorical.MonadErrors
open import OwnPrelude.Categorical.MonadFailAlternatives

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u e : Level
        n n' : Nat
        A B C X Y Z L S : Set i
        F G M : Set i -> Set j
        a b x y z m : A
        f g : A -> B

-- \tagcode{LatticeState}

module LatticeState
    {S : Set u}
    (bsl : BoundedSemilattice S) 
    {M : Set (i ~U~ u) -> Set (j ~U~ u)} 
    (monadM : Monad M) where
    open BoundedSemilattice bsl hiding (associative; e)
    -- open IsPreOrder isPreOrder
    open Monad monadM
    postulate isIMonoid : POMonoidType
    
    monadC = CStateTMonad.monad {i = i ~U~ u} S isPreOrder monadM isIMonoid
    open Monad monadC
        hiding (left-identity)
        renaming (_>>=_ to _>>=C_ ; return to returnC ; _>>_ to _>>C_ ; _<<*_ to _<<*C_; void to voidC)
    open StateActions {u = i ~U~ u} isPreOrder monadM
    open LBVar renaming (read to readL; write to writeL)
    open PolyUnit

    module Exports where
        open CStateTMonadT.MonadTProp {i = i ~U~ u} S isPreOrder monadM isIMonoid
        open MonadT monadT public
        open Monad monadC public

    module ExportMonadFailAlternative
        {Err : Set e}
        (mfa : MonadFailAlternativeOver monadM) where
        open CStateTMonadFailAlternative {i = i ~U~ u} S isPreOrder mfa
        open MonadFailAlternativeOver (monadFailAlternativeOver isIMonoid) public

    module ExportMonadError
        {Err : Set e}
        (me  : MonadErrorOver monadM Err) where
        open CStateTMonadError {i = i ~U~ u} S isPreOrder me
        open MonadErrorOver (monadErrorOver isIMonoid) public
        


    LState : Set (i ~U~ u) -> Set (u ~U~ j)
    LState = CStateT S _P_ M

    V : Set (i ~U~ u) -> Set (i ~U~ u)
    V = LBVar S bsl

    module NaiveOps 
        (fail : forall {A} -> LState A) where

        -- \tagcode{ReadWriteOps}

        read : V X -> LState X
        read v = getS (readL v) >>=C
            unas: fail 
            conf: fail 
            asm: returnC

        -- \tagcode{WRITE_DIRECTIONAL}

        write : V X -> X -> LState Unit
        write v x s = return (s <> writeL v x , directional , unit)

    module VarAccess {X : Set (i ~U~ u)}
        (readUnas : {A : Set (i ~U~ u)} -> V X -> S -> M A)
        (readConf : {A : Set (i ~U~ u)} -> V X -> S -> M A)
        (left-absorb-readUnas : forall {A B : Set (i ~U~ u)} {m : A -> M B} {v s} -> 
            readUnas v s >>= m === readUnas v s)
        (left-absorb-readConf : forall {A B : Set (i ~U~ u)} {m : A -> M B} {v s} -> 
            readConf v s >>= m === readConf v s) where
        open CStateTMonadT.MonadTProp {i = i ~U~ u} S isPreOrder monadM isIMonoid using (preserves-left-absorb; preserves-left-absorb-inside; monadT)
        open MonadT monadT

        read : V X -> LState X
        read v s = 
            unas: lift (readUnas v s) s
            conf: lift (readConf v s) s
            asm: (flip returnC s)
            (readL v s)
        -- read v = getS (readL v) >>=C 
        --     unas: lift (readUnas v s)
        --     conf: lift (readConf v s)
        --     asm: returnC

        write : V X -> X -> LState Unit
        write v x s = return (s <> writeL v x , directional , unit)

        module _ {v : V X} where
            open MonadicVariables monadC
            open IncreaseAssignmentProperty
            
            monadicVariable : MonadicVariable X
            MonadicVariables.MonadicVariable.read monadicVariable = read v
            MonadicVariables.MonadicVariable.write monadicVariable = write v
            -- commutative : forall {m' : M Y}{f : Y -> X -> M Z} ->
            --     (read >>= \_ -> m' >>= \y -> read >>= \x2 -> f y x2) === (read >>= \x1 -> m' >>= \y -> read >>= \_ -> f y x1)
            MonadicVariables.MonadicVariable.commutative monadicVariable {m'} {f} = extensPi lemma1
                where 
                    lemma1 : (s : S) -> (read v >>=C \_  -> m' >>=C \y -> read v >>=C \x2 -> f y x2) s === (read v >>=C \x1 -> m' >>=C \y -> read v >>=C \_  -> f y x1) s
                    lemma1 s with readL v s in readLvsEq
                    ...| unassigned = 
                        (lift (readUnas v s) >>=C _) s =< preserves-left-absorb left-absorb-readUnas || (\h -> h s) >
                        (lift (readUnas v s))        s =< sym (preserves-left-absorb left-absorb-readUnas) || (\h -> h s) >
                        (lift (readUnas v s) >>=C _) s qed
                    ...| conflict   = 
                        (lift (readConf v s) >>=C _) s =< preserves-left-absorb left-absorb-readConf || (\h -> h s) >
                        (lift (readConf v s))        s =< sym (preserves-left-absorb left-absorb-readConf) || (\h -> h s) >
                        (lift (readConf v s) >>=C _) s qed
                    ...| (asm x1)  =
                        (do
                            (s  , p  , x1) <- returnC x1 s 
                            (s4 , p4 , z) <- (m' >>=C \y -> read v >>=C \x2 -> f y x2) s
                            return (s4 , transitive p p4 , z)
                        ) =< left-identity >

                        (do
                            (s4 , p4 , z) <- (m' >>=C \y -> read v >>=C \x2 -> f y x2) s
                            return (s4 , transitive reflexive p4 , z)
                        ) =<>

                        (do
                            (s4 , p4 , z) <- do 
                                (s2 , p2 , y) <- m' s
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x2) <- read v s2
                                    (s4 , p4 , z) <- f y x2 s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            return (s4 , transitive reflexive p4 , z)
                        ) =<>

                        (do
                            (s4 , p4 , z) <- do 
                                (s2 , p2 , y) <- m' s
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x2) <- 
                                        unas: lift (readUnas v s2) s2
                                        conf: lift (readConf v s2) s2
                                        asm: (flip returnC s2)
                                        (readL v s2)
                                    (s4 , p4 , z) <- f y x2 s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            return (s4 , transitive reflexive p4 , z)
                        ) =< (\{(s2 , p2 , y) -> case (isBiThresholdRead v s s2 p2) of 
                                \{ (unas-to-anything readLvs=unas) -> absurd $ encodeVarAsm $
                                        unassigned =< sym readLvs=unas > 
                                        readL v s =< propToPath readLvsEq > 
                                        asm x1 qed
                                 ; (asm-eq readLvs=asmx2 readLvs2=asmx2) -> 
                                        (do 
                                            (s4 , p4 , z) <- do
                                                (s3 , p3 , x2) <- 
                                                    unas: lift (readUnas v s2) s2
                                                    conf: lift (readConf v s2) s2
                                                    asm: (flip returnC s2)
                                                    (readL v s2)
                                                (s4 , p4 , z) <- f y x2 s3
                                                return (s4 , transitive p3 p4 , z)
                                            return (s4 , transitive p2 p4 , z)
                                        ) =< (
                                            readL v s2 =< trans readLvs2=asmx2 (sym readLvs=asmx2) > 
                                            readL v s  =< propToPath readLvsEq >
                                            asm x1 qed
                                            || (\h -> do
                                                (s4 , p4 , z) <- do
                                                    (s3 , p3 , x2) <- 
                                                        unas: lift (readUnas v s2) s2
                                                        conf: lift (readConf v s2) s2
                                                        asm: (flip returnC s2)
                                                        h
                                                    (s4 , p4 , z) <- f y x2 s3
                                                    return (s4 , transitive p3 p4 , z)
                                                return (s4 , transitive p2 p4 , z))) >

                                        (do 
                                            (s4 , p4 , z) <- do
                                                (s3 , p3 , x2) <- returnC x1 s2
                                                (s4 , p4 , z) <- f y x2 s3
                                                return (s4 , transitive p3 p4 , z)
                                            return (s4 , transitive p2 p4 , z)
                                        ) =< (left-identity || _>>= _) >

                                        (do 
                                            (s4 , p4 , z) <- do
                                                (s4 , p4 , z) <- f y x1 s2
                                                return (s4 , transitive reflexive p4 , z)
                                            return (s4 , transitive p2 p4 , z)
                                        ) =< (sym left-identity || _>>= _) >

                                        (do 
                                            (s4 , p4 , z) <- do
                                                (s3 , p3 , x2) <- returnC x1 s2
                                                (s4 , p4 , z) <- f y x1 s3
                                                return (s4 , transitive p3 p4 , z)
                                            return (s4 , transitive p2 p4 , z)
                                        ) =< (
                                            returnC x1 s2 =< (asm x1 =< sym (propToPath readLvsEq) > 
                                                              readL v s =< trans readLvs=asmx2 (sym readLvs2=asmx2) >
                                                              readL v s2 qed 
                                                            ||  (\h -> 
                                                                unas: lift (readUnas v s2) s2
                                                                conf: lift (readConf v s2) s2
                                                                asm: (flip returnC s2)
                                                                h)) >
                                            unas: lift (readUnas v s2) s2
                                            conf: lift (readConf v s2) s2
                                            asm: (flip returnC s2)
                                            (readL v s2) qed
                                            || (\h -> (h >>= \{(s3 , p3 , x2) -> f y x1 s3 >>= _}) >>= _)) >
                                        (do 
                                            (s4 , p4 , z) <- do
                                                (s3 , p3 , x2) <- 
                                                    unas: lift (readUnas v s2) s2
                                                    conf: lift (readConf v s2) s2
                                                    asm: (flip returnC s2)
                                                    (readL v s2)
                                                (s4 , p4 , z) <- f y x1 s3
                                                return (s4 , transitive p3 p4 , z)
                                            return (s4 , transitive p2 p4 , z)
                                        ) qed

                                 ; (asm-conf readLvs=asmx2 readLvs2=conf) -> 
                                   (do 
                                        (s4 , p4 , z) <- do
                                            (s3 , p3 , x2) <- 
                                                unas: lift (readUnas v s2) s2
                                                conf: lift (readConf v s2) s2
                                                asm: (flip returnC s2)
                                                (readL v s2)
                                            (s4 , p4 , z) <- f y x2 s3
                                            return (s4 , transitive p3 p4 , z)
                                        return (s4 , transitive p2 p4 , z)
                                    ) =< (readLvs2=conf 
                                        || (\h -> (
                                                unas: lift (readUnas v s2) s2
                                                conf: lift (readConf v s2) s2
                                                asm: (flip returnC s2)
                                                h >>= \{(s3 , p3 , x2) -> f y x2 s3 >>= _}) >>= _)) >

                                    (do 
                                        (s4 , p4 , z) <- do
                                            (s3 , p3 , x2) <- lift (readConf v s2) s2
                                            (s4 , p4 , z) <- f y x2 s3
                                            return (s4 , transitive p3 p4 , z)
                                        return (s4 , transitive p2 p4 , z)
                                    ) =< preserves-left-absorb-inside left-absorb-readConf || _>>= _ >

                                    (do
                                        (s4 , p4 , z) <- lift (readConf v s2) s2
                                        return (s4 , transitive p2 p4 , z)
                                    ) =< sym (preserves-left-absorb-inside left-absorb-readConf) || _>>= _ >

                                    (do 
                                        (s4 , p4 , z) <- do
                                            (s3 , p3 , x2) <- lift (readConf v s2) s2
                                            (s4 , p4 , z) <- f y x1 s3
                                            return (s4 , transitive p3 p4 , z)
                                        return (s4 , transitive p2 p4 , z)
                                    ) =< 
                                        (sym $
                                            unas: lift (readUnas v s2) s2
                                            conf: lift (readConf v s2) s2
                                            asm: (flip returnC s2)
                                            (readL v s2) =< readLvs2=conf || (unas: _ conf: lift (readConf v s2) s2 asm: _) > 
                                            lift (readConf v s2) s2         qed
                                        )
                                        || (\h -> (h >>= \{(s3 , p3 , x2) -> f y x1 s3 >>= _}) >>= _) >

                                    (do 
                                        (s4 , p4 , z) <- do
                                            (s3 , p3 , x2) <- 
                                                unas: lift (readUnas v s2) s2
                                                conf: lift (readConf v s2) s2
                                                asm: (flip returnC s2)
                                                (readL v s2)
                                            (s4 , p4 , z) <- f y x1 s3
                                            return (s4 , transitive p3 p4 , z)
                                        return (s4 , transitive p2 p4 , z)
                                    ) qed
                                 ; (conf-conf readLvs=conf _)     -> absurd $ encodeVarAsm $
                                        conflict  =< sym readLvs=conf >
                                        readL v s =< propToPath readLvsEq >
                                        asm x1    qed
                                }
                                -- case (coerce (propToPath eq || _=incAsm= (readL v s2)) (isBiThresholdRead v s s2 p2) :T: (asm x1) =incAsm= (readL v s2)) of
                                --     \{ r -> {! r  !} }
                                
                            }) 
                            |pi (\h -> (m' s >>= h) >>= \{(s4 , p4 , z) -> return (s4 , transitive reflexive p4 , z)}) >

                        (do
                            (s4 , p4 , z) <- do 
                                (s2 , p2 , y) <- m' s
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x2) <- 
                                        unas: lift (readUnas v s2) s2
                                        conf: lift (readConf v s2) s2
                                        asm: (flip returnC s2)
                                        (readL v s2)
                                    (s4 , p4 , z) <- f y x1 s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            return (s4 , transitive reflexive p4 , z)
                        ) =<>

                        (do
                            (s4 , p4 , z) <- (m' >>=C \y -> read v >>=C \x2 -> f y x1) s
                            return (s4 , transitive reflexive p4 , z)
                        ) =< sym left-identity >

                        (do
                            (s  , p  , x1) <- returnC x1 s 
                            (s4 , p4 , z) <- (m' >>=C \y -> read v >>=C \x2 -> f y x1) s
                            return (s4 , transitive p p4 , z)
                        ) qed


            -- read-write : forall {x : X}{m' : M Y}{f : Y -> X -> M Z} ->
            -- (write x >> (m' >>= \y -> read >>= \x' -> f y x')) === (write x >> (m' >>= \y -> read >>= \_ -> f y x))
            MonadicVariables.MonadicVariable.read-write monadicVariable {x} {m'} {f} = extensPi \s ->
                (write v x >>C (m' >>=C \y -> read v >>=C \x' -> f y x')) s =<>
                
                (do
                    (s1 , p1 , _) <- write v x s
                    (s4 , p4 , z) <- do
                        (s2 , p2 , y) <- m' s1
                        (s4 , p4 , z) <- do
                            (s3 , p3 , x') <- 
                                unas: lift (readUnas v s2) s2
                                conf: lift (readConf v s2) s2
                                asm: (flip returnC s2)
                                (readL v s2)
                            (s4 , p4 , z ) <- f y x' s3
                            return (s4 , transitive p3 p4 , z)
                        return (s4 , transitive p2 p4 , z)
                    return (s4 , transitive p1 p4 , z)
                ) =< left-identity >

                (do
                    (s4 , p4 , z) <- do
                        (s2 , p2 , y) <- m' (s <> writeL v x)
                        (s4 , p4 , z) <- do
                            (s3 , p3 , x') <- 
                                unas: lift (readUnas v s2) s2
                                conf: lift (readConf v s2) s2
                                asm: (flip returnC s2)
                                (readL v s2)
                            (s4 , p4 , z ) <- f y x' s3
                            return (s4 , transitive p3 p4 , z)
                        return (s4 , transitive p2 p4 , z)
                    return (s4 , transitive directional p4 , z)
                ) =< ((\{(s2 , p2 , y) -> case write-persist v (transitive directional' p2) of
                        \{(left readLvs2=asm)   -> 
                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- 
                                        unas: lift (readUnas v s2) s2
                                        conf: lift (readConf v s2) s2
                                        asm: (flip returnC s2)
                                        (readL v s2)
                                    (s4 , p4 , z ) <- f y x' s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< readLvs2=asm || (\h -> ((unas: lift (readUnas v s2) s2 conf: lift (readConf v s2) s2 asm: _ h) >>= \{(s3 , p3 , x') -> f y x' s3 >>= _} ) >>= _) >

                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- returnC x s2
                                    (s4 , p4 , z ) <- f y x' s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< left-identity || _>>= _ >

                            (do
                                (s4 , p4 , z) <- do
                                    (s4 , p4 , z ) <- f y x s2
                                    return (s4 , transitive reflexive p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< sym left-identity || _>>= _ >

                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- returnC x s2
                                    (s4 , p4 , z ) <- f y x s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< (sym $ readLvs2=asm || (\h -> (unas: (lift (readUnas v s2) s2) conf: lift (readConf v s2) s2 asm: (flip returnC s2) h))) || (\h -> (h >>= \{(s3 , p3 , x') -> f y x s3 >>= _} ) >>= _) >

                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- 
                                        unas: lift (readUnas v s2) s2
                                        conf: lift (readConf v s2) s2
                                        asm: (flip returnC s2)
                                        (readL v s2)
                                    (s4 , p4 , z ) <- f y x s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) qed
                            
                        ; (right readLvs2=conf) -> 
                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- 
                                        unas: lift (readUnas v s2) s2
                                        conf: lift (readConf v s2) s2
                                        asm: (flip returnC s2)
                                        (readL v s2)
                                    (s4 , p4 , z ) <- f y x' s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< readLvs2=conf || (\h -> do
                                                            (s4 , p4 , z) <- do
                                                                (s3 , p3 , x') <- 
                                                                    unas: lift (readUnas v s2) s2
                                                                    conf: lift (readConf v s2) s2
                                                                    asm: (flip returnC s2)
                                                                    h
                                                                (s4 , p4 , z ) <- f y x' s3
                                                                return (s4 , transitive p3 p4 , z)
                                                            return (s4 , transitive p2 p4 , z)) >

                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- lift (readConf v s2) s2
                                    (s4 , p4 , z ) <- f y x' s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< preserves-left-absorb-inside left-absorb-readConf || _>>= _ >

                            (do
                                (s4 , p4 , z) <- lift (readConf v s2) s2
                                return (s4 , transitive p2 p4 , z)
                            ) =< sym (preserves-left-absorb-inside left-absorb-readConf) || _>>= _ >

                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- lift (readConf v s2) s2
                                    (s4 , p4 , z ) <- f y x s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) =< sym $ readLvs2=conf || (\h -> do
                                                    (s4 , p4 , z) <- do
                                                        (s3 , p3 , x') <- 
                                                            unas: lift (readUnas v s2) s2
                                                            conf: lift (readConf v s2) s2
                                                            asm: (flip returnC s2)
                                                            h
                                                        (s4 , p4 , z ) <- f y x s3
                                                        return (s4 , transitive p3 p4 , z)
                                                    return (s4 , transitive p2 p4 , z)) >

                            (do
                                (s4 , p4 , z) <- do
                                    (s3 , p3 , x') <- 
                                        unas: lift (readUnas v s2) s2
                                        conf: lift (readConf v s2) s2
                                        asm: (flip returnC s2)
                                        (readL v s2)
                                    (s4 , p4 , z ) <- f y x s3
                                    return (s4 , transitive p3 p4 , z)
                                return (s4 , transitive p2 p4 , z)
                            ) qed
                        }
                    })                    
                    |pi (\h -> (m' (s <> writeL v x) >>= h) >>= \{(s4 , p4 , z) -> return (s4 , transitive directional p4 , z)})) >

                (do
                    (s4 , p4 , z) <- do
                        (s2 , p2 , y) <- m' (s <> writeL v x)
                        (s4 , p4 , z) <- do
                            (s3 , p3 , x') <- 
                                unas: lift (readUnas v s2) s2
                                conf: lift (readConf v s2) s2
                                asm: (flip returnC s2)
                                (readL v s2)
                            (s4 , p4 , z ) <- f y x s3
                            return (s4 , transitive p3 p4 , z)
                        return (s4 , transitive p2 p4 , z)
                    return (s4 , transitive directional p4 , z)
                ) =< sym left-identity >

                (do
                    (s1 , p1 , _) <- write v x s
                    (s4 , p4 , z) <- do
                        (s2 , p2 , y) <- m' s1
                        (s4 , p4 , z) <- do
                            (s3 , p3 , x') <- 
                                unas: lift (readUnas v s2) s2
                                conf: lift (readConf v s2) s2
                                asm: (flip returnC s2)
                                (readL v s2)
                            (s4 , p4 , z ) <- f y x s3
                            return (s4 , transitive p3 p4 , z)
                        return (s4 , transitive p2 p4 , z)
                    return (s4 , transitive p1 p4 , z)
                ) =<>

                (write v x >>C (m' >>=C \y -> read v >>=C \_ -> f y x)) s qed