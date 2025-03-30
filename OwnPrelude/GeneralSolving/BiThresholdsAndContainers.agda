{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.BiThresholdsAndContainers where

open import ASCIIPrelude.ASCIIPrelude 
open NatOp renaming (_leq_ to _leqb_)
open PolyUnit
open PolyZero
open import ASCIIPrelude.ASCIIProofPrelude 
open import OwnPrelude.Equality
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.VarAsms renaming (module MonadNames to VarAsmsMonadNames)
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Data.Containers

open ExistsSyntax

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d e f g h i j k l m n p q r s t u v w x y z fm i' j' k' l' A B C X Y K M F alg  : ST

open Container using ([[_]])
open ContainerClosures
open ContainerCategorical
open RecursiveFixpoints
open CorecursiveFixpoints

-- data VW (C : Container i i) (V : Set i -> Set i) : Set i where
--     InVW : ([[ C ]] o V) (VW C V) -> VW C V
-- VW : Container 

-- \tagcode{BiThresholdsAndContainersPtI}
-- \tagcode{VWFixpoint}

VW : (C : Container i j) (V : Container i' j') -> Set (i ~U~ i' ~U~ j ~U~ j')
VW C V = W (C :o: V)

CoVW : (C : Container i j) (V : Container i' j') -> Set (i ~U~ i' ~U~ j ~U~ j')
CoVW C V = CoW (C :o: V)

module _ {C : Container i j} where
    open Container hiding ([[_]])
    PositionallyConstrainedBy : (M : A -> Set k) -> [[ C ]] A -> Set (j ~U~ k)
    PositionallyConstrainedBy M (s , p) = forall (p' : P C s) -> M (p p')

module _ {C : Container i j} {V : Container i' j'} where
    module _ {A : Set l} where
        InnerConstrainedFunctor : (M : [[ V ]] A -> Set k) -> ([[ C :o: V ]]) A -> Set (j ~U~ k)
        InnerConstrainedFunctor {k} M = coerce (sym (container-comp-interp {C = C} {D = V} {A = A}) || \h -> (h -> Set (j ~U~ k))) (PositionallyConstrainedBy M)

    module _ where
        open Container hiding ([[_]])
        InnerConstrainedFixpoint : (M : [[ V ]] (VW C V) -> Set k) -> VW C V -> Set (j ~U~ j' ~U~ k)
        InnerConstrainedFixpoint M (In (s , p)) = InnerConstrainedFunctor M (s , p) and (forall (p' : P (C :o: V) s) -> InnerConstrainedFixpoint M (p p'))

        open CoW renaming (Out to CoOut)

        record InnerConstrainedCoFixpoint (M : [[ V ]] (CoVW C V) -> Set k) (cvw : CoVW C V) : Set (i ~U~ i' ~U~ j ~U~ j' ~U~ k) where
            coinductive
            field
                innerConstrainedFunctor : InnerConstrainedFunctor M (CoOut cvw)
                recursivePreservation : let (s , p) = CoOut f in
                    forall (p' : P (C :o: V) s) -> InnerConstrainedCoFixpoint M (p p')

VarAsmC : Container i j
VarAsmC {i} = UnitC {i} :+: IC {i} :+: UnitC {i}

VarAsmC=VarAsm : {A : Set i} -> [[ VarAsmC {i} {i} ]] A === VarAsm A
VarAsmC=VarAsm = Iso->=== (record { 
    to = \{(left x , p) -> unassigned
            ; (right (left x) , p) -> asm (p unit)
            ; (right (right y) , p) -> conflict} ; 
    from = \{unassigned -> (left unit , \())
            ; (asm x) -> (right (left unit) , \_ -> x)
            ; conflict -> (right (right unit) , \())} ; 
    isIsomorphism = record { 
        to-o-from=id = extens \{unassigned -> refl
                                ; (asm x) -> refl
                                ; conflict -> refl} ; 
        from-o-to=id = extens \{(left unit , p) -> (extens \()) || left unit ,_
                                ; (right (left x) , snd1) -> refl
                                ; (right (right y) , snd1) -> (extens \()) || right (right y) ,_} } })

module VariableContainer i j (S : Set k) where  
    VC : Container (i ~U~ k) (j ~U~ k)  
    VC = PiC {j = j} S (\_ -> VarAsmC {i})

module _ {l} {S : Set k} where
    open VariableContainer l l S
    VC=S->VarAsmX : {A : Set l} -> [[ VC ]] A === (S -> VarAsm A)
    VC=S->VarAsmX {A} = 
        [[ VC ]] A                    =<>
        [[ PiC S (\_ -> VarAsmC) ]] A =< container-pi-interp >
        (S -> [[ VarAsmC ]] A)        =< VarAsmC=VarAsm || (\h -> S -> h) >
        (S -> VarAsm A)               qed

module _ (S : Set k) where
    
    module _ {A : Set i} {C : Container j k} (bsl : BoundedSemilattice S) where
        open VariableContainer i i S

        LBVarPreserving : [[ C :o: VC ]] A -> Set (i ~U~ k)
        LBVarPreserving = InnerConstrainedFunctor (\v -> HasLBVar (coerce VC=S->VarAsmX v) bsl)

    module _ {C : Container j k} (bsl : BoundedSemilattice S) where
        open VariableContainer (j ~U~ k) (j ~U~ k) S
        LBVarFixpoint : VW C VC -> Set (j ~U~ k)
        LBVarFixpoint = InnerConstrainedFixpoint (\v -> HasLBVar (coerce VC=S->VarAsmX v) bsl)

        LBVarCoFixpoint : CoVW C VC -> Set (j ~U~ k)
        LBVarCoFixpoint = InnerConstrainedCoFixpoint (\v -> HasLBVar (coerce VC=S->VarAsmX v) bsl)

module CommutableContexts where
    module _ (F : Set i -> Set i) (M : Set i -> Set i) (mon : Monad M) (func : Functor F) where
        open EndoMonad mon hiding (_<$>_ ; fmap)
        module F' = Functor func
        module M' = Functor (Monad.functor mon)
        module FM = Functor (FunctorComposition func (Monad.functor mon))
        module MF = Functor (FunctorComposition (Monad.functor mon) func)

        BindPropFromJoinFmapProp : 
            {switch : forall {A} -> (F o M) A -> (M o F) A} -> 
            (forall {A} -> switch {A = A} o F'.fmap join === switch >=> switch) -> 
            (forall {A}{B} {f : A -> B} -> switch {A = B} o F'.fmap (M'.fmap f) === M'.fmap (F'.fmap f) o switch) -> 
            {fm : (F o M) A} -> {f : A -> M B} ->
            switch ((_>>= f) F'.<$> fm) === (switch fm >>= switch o F'.fmap f)
        BindPropFromJoinFmapProp {switch} switch>=>switch-eq fmap-o-fmap-eq {fm} {f} =
            switch ((_>>= f) F'.<$> fm) =< sym join-bind || (\h -> switch (h F'.<$> fm)) >
            switch ((join o M'.fmap f) F'.<$> fm) =<>
            switch (F'.fmap (join o M'.fmap f) fm) =< F'.fmap-comp || (\h -> switch (h fm)) >
            switch ((F'.fmap join o F'.fmap (M'.fmap f)) fm) =<>
            ((switch o F'.fmap join) o F'.fmap (M'.fmap f)) fm =< switch>=>switch-eq || (\h -> (h o F'.fmap (M'.fmap f)) fm) >
            (switch >=> switch) (F'.fmap (M'.fmap f) fm) =<>
            (switch (F'.fmap (M'.fmap f) fm) >>= switch)  =< fmap-o-fmap-eq || (\h -> h fm >>= switch) >
            (M'.fmap (F'.fmap f) (switch fm) >>= switch)  =< fmap-simplified || (\h -> h (switch fm) >>= switch) >
            ((switch fm) >>= return o F'.fmap f >>= switch) =< associative >      
            ((switch fm) >>= \sfm -> return (F'.fmap f sfm) >>= switch) =< (\_ -> left-identity) |f (\h -> (switch fm) >>= h) > 
            ((switch fm) >>= \sfm -> switch (F'.fmap f sfm)) =<>   
            switch fm >>= switch o F'.fmap f qed

        BindPropFromJoinReformulation : 
            {switch : forall {A} -> (F o M) A -> (M o F) A} -> 
            (forall {A}{B}{f : A -> M B} -> switch o F'.fmap join o FM.fmap f === switch >=> switch o F'.fmap f) -> 
            {fm : (F o M) A} -> {f : A -> M B} ->
            switch ((_>>= f) F'.<$> fm) === (switch fm >>= switch o F'.fmap f)
        BindPropFromJoinReformulation {switch} bind-prop' {fm} {f} =
            switch ((_>>= f) F'.<$> fm) =< sym join-bind || (\h -> switch (h F'.<$> fm)) >
            (switch o F'.fmap (join o M'.fmap f)) fm =< F'.fmap-comp || (\h -> (switch o h) fm) >
            (switch o F'.fmap join o FM.fmap f) fm =< bind-prop' || (_$ fm) >
            switch fm >>= switch o F'.fmap f qed

        -- \tagcode{CommutableContexts}

        record CommutableContexts : Set (lsuc i) where
            field
                switch : (F o M) A -> (M o F) A
                -- purely monadic set of axioms
                return-prop : {fa : F A} ->
                    switch (return F'.<$> fa) === return fa
                bind-prop : {fm : (F o M) A} -> {f : A -> M B} ->
                    switch ((_>>= f) F'.<$> fm) === (switch fm >>= switch o F'.fmap f) --TODO: rewrite thie pointfree

            bind-prop' : switch o F'.fmap join o FM.fmap f === switch >=> switch o F'.fmap f
            bind-prop' {f} = extens \fm ->
                (switch o F'.fmap join o FM.fmap f) fm =<>
                (switch o F'.fmap join o F'.fmap (M'.fmap f)) fm =< sym F'.fmap-comp || (\h -> switch (h fm)) >
                (switch o F'.fmap (join o M'.fmap f)) fm =< join-bind || (\h -> (switch o F'.fmap h) fm) >
                (switch o F'.fmap (_>>= f)) fm =< bind-prop >
                (switch >=> switch o F'.fmap f) fm qed

            join-prop' :
                    switch {A = A} o F'.fmap join === join o M'.fmap switch o switch --< switch >=> switch
            join-prop' = 
                switch o F'.fmap join          =<>
                switch o F'.fmap (_>>= id)     =< extens (\_ -> bind-prop) >
                switch >=> switch o F'.fmap id =< F'.fmap-id || (\h -> switch >=> switch o h) >
                switch >=> switch              =<>
                (\a -> switch a >>= switch)    =< extens (\a -> sym (join-bind || (_$ switch a))) >
                join o M'.fmap switch o switch qed

            join-prop :
                    switch {A = A} o F'.fmap join === switch >=> switch
            join-prop = 
                switch o F'.fmap join          =<>
                switch o F'.fmap (_>>= id)     =< extens (\_ -> bind-prop) >
                switch >=> switch o F'.fmap id =< F'.fmap-id || (\h -> switch >=> switch o h) >
                switch >=> switch              qed


            -- more categorical view
            applyMorph : (F A -> B) -> (F o M) A -> M B
            applyMorph f = M'.fmap f o switch

            applyMorph-prop : forall {f : F A -> B} -> applyMorph f o F'.fmap return === M'.fmap f o return
            applyMorph-prop {f} = extens \fa -> return-prop || M'.fmap f

            applyMorph-return-prop : applyMorph f o F'.fmap return === return o f
            applyMorph-return-prop {f} = 
                applyMorph f o F'.fmap return       =<>
                M'.fmap f o switch o F'.fmap return =< (extens \_ -> return-prop) || M'.fmap f o_ >
                M'.fmap f o return                  =< fmap-return >
                return o f                          qed

            applyMorph-bind-prop : {fm : (F o M) A} {f : F B -> C} {g : A -> M B} -> 
                applyMorph f ((_>>= g) F'.<$> fm) === f M'.<$> (switch fm >>= switch o F'.fmap g)
            applyMorph-bind-prop {f} = bind-prop || M'.fmap f

            applyMorph-bind-prop' : {fm : (F o M) A} {f : F B -> C} {g : A -> M B} -> 
                applyMorph f o F'.fmap join o FM.fmap g === M'.fmap f o (switch >=> switch o F'.fmap g)
            applyMorph-bind-prop' {f} = bind-prop' || M'.fmap f o_

            applyMorph-join-prop : {fm : (F o M o M) A} {f : F A -> B} -> 
                applyMorph f o F'.fmap join === M'.fmap f o (switch >=> switch)
            applyMorph-join-prop {f} = join-prop || M'.fmap f o_

            switch-fmap-fmap : switch o FM.fmap f === MF.fmap f o switch
            switch-fmap-fmap {f} = extens \fm -> 
                switch (FM.fmap f fm)                               =<>
                switch ((F'.fmap o M'.fmap) f fm)                   =<>
                switch (F'.fmap (M'.fmap f) fm)                     =< fmap-simplified || (\h -> switch (F'.fmap h fm)) >
                switch (F'.fmap (_>>= return o f) fm)               =< bind-prop {fm = fm} {f = return o f} >
                switch fm >>= switch o F'.fmap (return o f)         =< F'.fmap-comp || (\h -> switch fm >>= switch o h) >
                switch fm >>= switch o (F'.fmap return o F'.fmap f) =<>
                switch fm >>= (switch o F'.fmap return) o F'.fmap f =< (\fa -> return-prop {fa = fa}) |f (\h -> switch fm >>= h o F'.fmap f) >
                switch fm >>= return o (F'.fmap f)                  =< sym fmap-simplified || (_$ (switch fm)) >
                M'.fmap (F'.fmap f) (switch fm)                     =<>
                (M'.fmap o F'.fmap) f (switch fm)                   =<>
                MF.fmap f (switch fm)                               qed

    module _ 
        {M : Container i i}
        {C : Container i i}
        (mon : Monad [[ M ]])
        (comc : CommutableContexts {i = i} [[ C ]] [[ M ]] mon containerFunctor) 
        (map=fmap : forall {A B}{f : A -> B} -> ContainerOps.map f === Monad.fmap mon f) -- this does hold over all categories, but to prove that, we need a free category! Or prove uniqueness of fmap
        where
        open CommutableContexts comc
        open ContainerOps
        open EndoMonad mon
        open Functor (containerFunctor{i} {C = C}) renaming (_<$>_ to _<$>C_ ; fmap to fmapC)

        -- \tagcode{CommutableContextsWrapping}

        private
            switch' : {A : Set i} -> [[ C :o: M ]] A -> ([[ M ]] o [[ C ]]) A
            switch' {A} = switch o compd

        unwrapAlg : ([[ C ]] o [[ M ]]) ([[ M ]] (W C)) -> [[ M ]] (W C)
        unwrapAlg = fmap In o (switch >=> switch)

        unwrapAlg' : [[ C :o: M ]] ([[ M ]] (W C)) -> [[ M ]] (W C)
        unwrapAlg' = unwrapAlg o compd
        
        unwrap : VW C M -> [[ M ]] (W C)
        unwrap = foldC unwrapAlg'
        
        wrapAlg : [[ C ]] (VW C M) -> VW C M
        wrapAlg = In o' compc o map return

        wrap : W C -> VW C M
        wrap = foldC wrapAlg

        Out' : VW C M -> ([[ C ]] o [[ M ]]) (VW C M)
        Out' = compd o Out

        -- \tagcode{unwrap-wrap}

        unwrap-o-wrap : unwrap o wrap === return
        unwrap-o-wrap = extens \wc -> flip (foldPi {A = \wc -> (unwrap o wrap) wc === return wc}) wc (
            \{(s , p) -> 
                unwrap (wrap (In (s , fst o p)))                                                                =<>
                unwrap (wrapAlg (s , wrap o fst o p))                                                           =<>
                unwrap ((In o' compc o' map return) (s , wrap o fst o p))                                       =<>
                unwrapAlg' ((map unwrap o compc o' map return) (s , wrap o fst o p))                            =<>
                unwrapAlg' ((map unwrap o compc) (s , return o wrap o fst o p))                                 =<>
                fmap In (switch ((compd o map unwrap o compc) (s , return o wrap o fst o p)) >>= switch)        =<>
                fmap In (switch (s , map unwrap o return o wrap o fst o p) >>= switch)                          =< map=fmap || (\h -> fmap In (switch (s , h o return o wrap o fst o p) >>= switch)) >
                fmap In (switch (s , (fmap unwrap o return) o wrap o fst o p) >>= switch)                       =< fmap-return || (\h -> fmap In (switch (s , h o wrap o fst o p) >>= switch)) >
                fmap In (switch (s , return o unwrap o wrap o fst o p) >>= switch)                              =< (\p' -> snd (p p') || return) |pi  (\h -> fmap In (switch (s , h) >>= switch)) >
                fmap In (switch (s , return o return o fst o p) >>= switch)                                     =< return-prop || fmap In o (_>>= switch) > 
                fmap In (return (s , return o fst o p) >>= switch)                                              =< left-identity || fmap In > 
                fmap In (switch (s , return o fst o p))                                                         =< return-prop || fmap In > 
                fmap In (return (s , fst o p))                                                                  =< fmap-simplified || (_$ (return (s , fst o p))) > 
                return (s , fst o p) >>= return o In                                                            =< left-identity >
                return (In (s , fst o p))                                                                       qed }) 

        module _ {A : Set i} where

            -- \tagcode{CommutableContextsFoldS}
            foldS : ([[ C ]] A -> A) -> VW C M -> [[ M ]] A
            foldS alg = foldC (switch' >=> applyMorph alg)

            -- \tagcode{CommutableContextsFoldSUnwrap}
            foldS-unwrap : fmap (foldC alg) o unwrap === foldS alg
            foldS-unwrap {alg} = extens $ foldPi \((s , f) , p) ->
                fmap (foldC alg) (unwrap (In ((s , f) , fst o p)))                                                                          =<>
                fmap (foldC alg) ((unwrapAlg' o map unwrap) ((s , f) , fst o p))                                                            =<>
                (fmap (foldC alg) o unwrapAlg' o map unwrap) ((s , f) , fst o p)                                                            =<>
                (fmap (foldC alg) o fmap In o (switch >=> switch) o compd o map unwrap) ((s , f) , fst o p)                                 =< sym join-prop || (\h -> (fmap (foldC alg) o fmap In o h o compd o map unwrap) ((s , f) , fst o p)) >
                (fmap (foldC alg) o fmap In o switch o map join o compd o map unwrap) ((s , f) , fst o p)                                   =<>
                (fmap (foldC alg) o fmap In o switch o map join o compd) ((s , f) , unwrap o fst o p)                                       =<>
                (fmap (foldC alg) o fmap In o switch o map join) (s , \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))         =< sym (Monad.fmap-comp mon) || (\h -> (h o switch o map join) (s , \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))) >
                (fmap (foldC alg o In) o switch o map join) (s , \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))              =<>
                (fmap (foldC alg o In) o switch) (s , join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))                  =<>
                (fmap (alg o map (foldC alg)) o switch) (s , join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))           =< Monad.fmap-comp mon ||  (\h -> (h o switch) (s , join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))) >
                (fmap alg o fmap (map (foldC alg)) o switch) (s , join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))      =< sym switch-fmap-fmap || (\h -> (fmap alg o h) (s , join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))) >
                (fmap alg o switch o map (fmap (foldC alg))) (s , join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))      =<>
                (fmap alg o switch) (s , (fmap (foldC alg)) o join o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))          =< join-fmap || (\h -> (fmap alg o switch) (s , (h o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs)))) >
                (fmap alg o switch) (s , join o ((fmap o fmap) (foldC alg)) o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs)) =< sym map=fmap || (\h -> (fmap alg o switch) (s , join o h o \pcs -> f pcs , \pdfpcs -> (unwrap o fst o p) (pcs , pdfpcs))) >
                (fmap alg o switch) (s , join o \pcs -> f pcs , \pdfpcs -> (fmap (foldC alg) o unwrap o fst o p) (pcs , pdfpcs))            =< (\p' -> snd (p p')) |pi (\h -> (fmap alg o switch) (s , join o \pcs -> f pcs , \pdfpcs -> h (pcs , pdfpcs))) >
                (fmap alg o switch) (s , join o \pcs -> f pcs , \pdfpcs -> (foldS alg o fst o p) (pcs , pdfpcs))                            =<>
                (fmap alg o switch o map join) (s , \pcs -> f pcs , \pdfpcs -> (foldS alg o fst o p) (pcs , pdfpcs))                        =<>
                (fmap alg o switch o map join o compd) ((s , f) , foldS alg o fst o p)                                                      =< join-prop ||  (\h -> (fmap alg o h o compd) ((s , f) , foldS alg o fst o p)) >
                (fmap alg o (switch >=> switch) o compd) ((s , f) , foldS alg o fst o p)                                                    =< fmap-kleisli-switch {g = switch} || (\h -> (h o compd) ((s , f) , foldS alg o fst o p)) >
                ((switch >=> fmap alg o switch) o compd) ((s , f) , foldS alg o fst o p)                                                    =<>
                (switch' >=> fmap alg o switch) ((s , f) , foldS alg o fst o p)                                                             =<>
                (switch' >=> applyMorph alg) ((s , f) , foldS alg o fst o p)                                                                =<>
                foldS alg (In ((s , f) , fst o p))                                                                                          qed

            foldS-return : return o foldC alg === foldS alg o wrap
            foldS-return {alg} = 
                return o foldC alg               =< sym fmap-return >
                fmap (foldC alg) o return        =< sym unwrap-o-wrap || fmap (foldC alg) o_ >
                fmap (foldC alg) o unwrap o wrap =< foldS-unwrap || _o wrap >
                foldS alg o wrap                 qed


            -- \tagcode{CommutableContextsFoldM}

            foldM : (forall (M' : Set i -> Set i) -> Monad M' -> [[ C ]] (M' A) -> M' A) -> VW C M -> [[ M ]] A
            -- foldM alg = foldC (switch' >=> alg [[ M ]] mon)
            foldM alg = foldC (alg [[ M ]] mon o map join o compd) 

            --TODO: correctness properties (fold over id on original should yield same result)
            -- also: unused monadic values do not change monad state!
            -- maybe just describe this without additional proofs... 
    

    module Fkt {A : Set i} where
        open Monad {i} (functionMonad {A = A}) public
        
    module CommutableExamples where
        module _ 
            (C : Container i i) 
            (M : Set i -> Set i)
            (mon : Monad {i} M) where

            module InterpretationSwitch 
                (interp : forall {A} -> M A -> A) where
                open Monad mon
                
                switch : ([[ C ]] o M) A -> (M o [[ C ]]) A
                switch (s , p) = return (s , interp o p)

            record PositionCommuteContainer : Set (lsuc i) where
                open Container C hiding ([[_]])
                open ContainerOps
                open Monad mon
                open CommutableContexts
                open FinProp.MonadSwitch mon  using (switch-fmap-fmap ; switch-join)
                field
                    positionSwitch : forall {s : S} -> CommutableContexts (\A -> P s -> A) M mon Fkt.functor

                switch' : {s : S} -> (P s -> M A) -> M (P s -> A)
                switch' =  switch positionSwitch

                -- bind-prop : {fm : (F o M) A} -> {f : A -> M B} ->
                --     switch ((_>>= f) F'.<$> fm) === (switch fm >>= switch o F'.fmap f)

                -- BindPropFromJoinFmapProp : 
                --     {switch : forall {A} -> (F o M) A -> (M o F) A} -> 
                --     (forall {A} -> switch {A = A} o F'.fmap join === switch >=> switch) -> 
                --     (forall {A}{B} {f : A -> B} -> switch {A = B} o F'.fmap (M'.fmap f) === M'.fmap (F'.fmap f) o switch) -> 
                --     {fm : (F o M) A} -> {f : A -> M B} ->
                --     switch ((_>>= f) F'.<$> fm) === (switch fm >>= switch o F'.fmap f)

                -- \tagcode{ShapelyCommutableContexts}

                commutableContexts : CommutableContexts [[ C ]] M mon containerFunctor
                commutableContexts .CommutableContexts.switch (s , p) = (| (s ,_) (switch' p) |)
                commutableContexts .CommutableContexts.return-prop {fa = (s , p)} =
                    (| (s ,_) (switch' (return o p)) |) =< return-prop (positionSwitch {s}) || (\h -> (| (s ,_) h |)) >
                    (| (s ,_) (| p |) |) =< homomorphism >
                    return (s , p) qed
                commutableContexts .CommutableContexts.bind-prop {fm = (s , p)} {f} =
                    (| (s ,_) (switch' ((_>>= f) o p)) |) =< bind-prop (positionSwitch {s}) || (\h -> (| (s ,_) h |)) >
                    (| (s ,_) (switch' p >>= switch' o Fkt.fmap f) |) =< fmap-simplified || (_$ (switch' p >>= switch' o (f o_))) >
                    
                    (do
                        p'' <- do
                            p' <- switch' p
                            switch' (f o p')
                        return (s , p'')
                    ) =< associative >

                    (do
                        p' <- switch' p
                        p'' <- switch' (f o p')
                        return (s , p'')
                    ) =< (\p' -> sym fmap-simplified || (_$ switch' (f o p'))) |f switch' p >>=_ >

                    (do
                        p' <- switch' p
                        (| (s ,_) (switch' (f o p')) |)
                    ) =< (\_ -> sym left-identity) |f switch' p >>=_ >

                    (do
                        p'' <- switch' p
                        (s' , p') <- return (s , p'')
                        (| (s' ,_) (switch' (f o p')) |)
                    ) =< sym associative >
                    
                    (do
                        (s' , p') <- switch' p >>= return o (s ,_)
                        (| (s' ,_) (switch' (f o p')) |)
                    ) =< (sym fmap-simplified || (_$ switch' p)) || _>>= (\{(s' , p') -> (| (s' ,_) (switch' (f o p')) |)}) >
                    
                    (| (s ,_) (switch' p) |) >>= (\{(s' , p') -> (| (s' ,_) (switch' (f o p')) |)}) qed

        module MonadicSwitch {C : Container i i} (shapely : ShapelyContainer C) {M : Set i -> Set i} (mon : Monad M) (lcmon : LocallyCommutativeMonad mon) where
            open ShapelyContainer shapely
            open Monad mon
            open FinProp
            open MonadSwitch mon lcmon
            open PositionCommuteContainer
            open Finite

            positionCommCont' : PositionCommuteContainer vectorContainer M mon
            positionCommCont' .positionSwitch {s} .CommutableContexts.switch {A} = switch
            positionCommCont' .positionSwitch {s} .CommutableContexts.return-prop {A} {fa} = switch-return || (_$ fa)
            positionCommCont' .positionSwitch {s} .CommutableContexts.bind-prop = 
                BindPropFromJoinFmapProp _ _ mon Fkt.functor switch-join switch-fmap-fmap

            positionCommCont : PositionCommuteContainer C M mon
            positionCommCont = coerce (sym vecContainerEq || (\h -> PositionCommuteContainer h M mon)) positionCommCont'

                --TODO: question is here: for which functions A -> M B can we get an M (A -> B)
                -- works for finite A obviously. But what about the rest? Can we build a lazy function where the value is 
                -- only computed when actually needed? What about closed categories? Having a representation of a function should 
                -- make it be bakeable...
                -- maybe make easy case first and then use type of type theory to go full on meta 
                    
