{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.BiThresholdVariables where

open import ASCIIPrelude.ASCIIPrelude
open PolyUnit
open PolyZero 
open import OwnPrelude.Equality hiding (trans-refl-left; trans-refl-right)
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.LatticeConstructions
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.TrivialLattices
open import OwnPrelude.Data.NTuples
private
    _^_ = NTup
{-# DISPLAY _`$\back^_$` A n = A ^ n #-}

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L S S1 S2 : Set i
        F G M : Set i -> Set j
        a b x y z m s : A
        f g : A -> B

-- \tagcode{BiThresholdVariables}

module IncreaseAssignmentProperty {X : Set u} where

    data _=incAsm=_ (a b : VarAsm X) : Set u where
        unas-to-anything :  a === unassigned ->                   a =incAsm= b
        asm-eq           :  a === asm x      -> b === asm x    -> a =incAsm= b
        asm-conf         :  a === asm x      -> b === conflict -> a =incAsm= b
        conf-conf        :  a === conflict   -> b === conflict -> a =incAsm= b

    increase-asm : (asm x) =incAsm= unassigned -> Zero {u}
    increase-asm {x} (unas-to-anything a=unas) = encodeVarAsm a=unas
    increase-asm {x} (asm-eq a=asm b=asm)      = encodeVarAsm b=asm
    increase-asm {x} (asm-conf a=asm b=conf)   = encodeVarAsm b=conf
    increase-asm {x} (conf-conf a=conf b=conf) = encodeVarAsm b=conf

    asm-stays-eq : (asm x) =incAsm= (asm y) -> x === y
    asm-stays-eq (unas-to-anything eq) = absurd (encodeVarAsm eq)
    asm-stays-eq (asm-eq a=asm b=asm)  = encodeVarAsm (trans a=asm (sym b=asm))
    asm-stays-eq (asm-conf _ eq)       = absurd (encodeVarAsm eq)
    asm-stays-eq (conf-conf eq _)      = absurd (encodeVarAsm eq)

    asm-asm-+-conf : (asm x) =incAsm= a -> (a === asm x) or (a === conflict)
    asm-asm-+-conf (unas-to-anything x) = absurd (encodeVarAsm x)
    asm-asm-+-conf (asm-eq x x1)        = left (trans x1 (sym x))
    asm-asm-+-conf (asm-conf x x1)      = right x1
    asm-asm-+-conf (conf-conf x x1)     = absurd (encodeVarAsm x)

    asm-stays-conf : conflict =incAsm= a -> (a === conflict)
    asm-stays-conf (unas-to-anything x) = absurd (encodeVarAsm x)
    asm-stays-conf (asm-eq x x1)        = absurd (encodeVarAsm x)
    asm-stays-conf (asm-conf x x1)      = x1
    asm-stays-conf (conf-conf x x1)     = x1


module BiThresholds {S : Set i} {_P_ : S -> S -> Set j} 
    (isPreOrder : IsPreOrder _P_) where
    open IsPreOrder isPreOrder

    module _ {X : Set u} where
        open IncreaseAssignmentProperty

        -- \tagcode{IsBiThresholdRead}

        IsBiThresholdRead : (f : S -> VarAsm X) -> Set (i ~U~ j ~U~ u)
        IsBiThresholdRead f = forall s s' -> s P s' -> f s =incAsm= f s'

record RawLBVar 
    (S : Set i)
    (X : Set u) : Set (i ~U~ u) where  
    field
        read : S -> VarAsm X
        write : X -> S

module _ {S : Set i} {X : Set j} where
    -- \tagcode{IsLBVar}

    record IsLBVar
        (rawLBVar : RawLBVar S X)
        (lat : BoundedSemilattice S) : Set (i ~U~ j) where 
        open BoundedSemilattice lat
        open BiThresholds isPreOrder
        open RawLBVar rawLBVar
        open OwnPrelude.Data.VarAsms using () 
            renaming (asm to pure; _>>=VarAsm_ to _>>=_; _<*>VarAsm_ to _<*>_) -- needs to be done like this for universe level polymorphism
        field
            isBiThresholdRead : IsBiThresholdRead read
            write-read : read (write x) === asm x
            read-write-read : (| write (read s) |) >>= read === read s

        write-persist : (write x) P s -> (read s === asm x) or (read s === conflict)
        write-persist {x} {s} wPs with isBiThresholdRead _ _ wPs 
        ... | IncreaseAssignmentProperty.unas-to-anything readwritex=unas = absurd $ encodeVarAsm $ 
                unassigned     =< sym readwritex=unas >
                read (write x) =< write-read >
                asm x          qed
        ... | IncreaseAssignmentProperty.asm-eq readwritex=asmx1 reads=asmx1 = left $
                read s         =< trans reads=asmx1 (sym readwritex=asmx1) >
                read (write x) =< write-read >
                asm x          qed
        ... | IncreaseAssignmentProperty.asm-conf readwritex=asmx1 reads=conflict = right reads=conflict
        ... | IncreaseAssignmentProperty.conf-conf readwritex=conflict reads=conflict = absurd $ encodeVarAsm $ 
                conflict =< sym readwritex=conflict >
                read (write x) =< write-read >
                asm x qed

record LBVar
    (S : Set i)
    (lat : BoundedSemilattice S)
    (X : Set j) : Set (i ~U~ j) where 
    field
        rawLBVar : RawLBVar S X
        isLBVar : IsLBVar rawLBVar lat
    open RawLBVar rawLBVar public
    open IsLBVar  isLBVar  public

module _ {S : Set i} {X : Set j} where
    record HasLBVar (read : S -> VarAsm X) (lat : BoundedSemilattice S) : Set (i ~U~ j) where
        field
            write : X -> S
        rawLBVar : RawLBVar S X
        rawLBVar = record { read = read ; write = write }
        field
            isLBVar : IsLBVar rawLBVar lat
        lbVar : LBVar S lat X
        lbVar .LBVar.rawLBVar = rawLBVar
        lbVar .LBVar.isLBVar  = isLBVar
        
        open LBVar lbVar public hiding (write; rawLBVar)



module _ {X : Set i} (decEq : DecEq X) where
    rawTrivLBVar : RawLBVar (TB X) X
    RawLBVar.read rawTrivLBVar topTB = unassigned
    RawLBVar.read rawTrivLBVar botTB = conflict
    RawLBVar.read rawTrivLBVar (valTB x) = asm x
    RawLBVar.write rawTrivLBVar x = valTB x

    open TrivialLattice decEq

    module _ where
        open DecEq decEq
        open RawLBVar rawTrivLBVar
        open BoundedMeetSemilattice trivialBoundedMeetSemilattice
        open IncreaseAssignmentProperty
        
        isTrivLBVar : IsLBVar rawTrivLBVar trivialBoundedMeetSemilattice
        IsLBVar.isBiThresholdRead isTrivLBVar topTB  s' sPs' = unas-to-anything refl
        IsLBVar.isBiThresholdRead isTrivLBVar botTB topTB sPs' = absurd $ encodeTB sPs'
        IsLBVar.isBiThresholdRead isTrivLBVar botTB botTB sPs' = conf-conf refl refl
        IsLBVar.isBiThresholdRead isTrivLBVar botTB (valTB x) sPs' = absurd $ encodeTB sPs'
        IsLBVar.isBiThresholdRead isTrivLBVar (valTB x) topTB sPs' = absurd $ encodeTB sPs'
        IsLBVar.isBiThresholdRead isTrivLBVar (valTB x) botTB sPs' = asm-conf refl refl
        IsLBVar.isBiThresholdRead isTrivLBVar (valTB x) (valTB y) sPs' with x == y
        ... | yes x=y = asm-eq refl (sym x=y || asm)
        ... | no ¬x=y = absurd $ encodeTB sPs'
        IsLBVar.write-read isTrivLBVar = refl
        IsLBVar.read-write-read isTrivLBVar {s = topTB}   = refl
        IsLBVar.read-write-read isTrivLBVar {s = botTB}   = refl
        IsLBVar.read-write-read isTrivLBVar {s = valTB x} = refl

        TrivLBVar : LBVar (TB X) trivialBoundedMeetSemilattice X
        TrivLBVar .LBVar.rawLBVar = rawTrivLBVar
        TrivLBVar .LBVar.isLBVar = isTrivLBVar

module _ {S : Set i} {bsl : BoundedSemilattice S} {X : Set j} {Y : Set k} where
    open LBVar
    open BoundedSemilattice bsl
    record LBVarIndependence (v1 : LBVar S bsl X) (v2 : LBVar S bsl Y) : Set (i ~U~ j ~U~ k) where
        field
            independence : Independence (read v1) (read v2)
            writev1 : read v2 s === read v2 (s <> write v1 x)
            writev2 : read v1 s === read v1 (s <> write v2 x)
            -- TODO: independence is not implied until we get special variables that can return the smallest input to create the desired output!


module _ 
    {S1 S2 : Set j}
    {X Y : Set i}
    {L1 : BoundedSemilattice S1} 
    {L2 : BoundedSemilattice S2} where
    
    open BoundedSemilattice L1 using () renaming
        (semilattice to semilattice1)
    open BoundedSemilattice L2 using () renaming
        (semilattice to semilattice2)
    open ProductSemilatticeProperties semilattice1 semilattice2
    open BoundedSemilattice (L1 -xBSLx- L2)
    open BoundedSemilattice L1 using () renaming (e to e1 ; _<>_ to _<>1_ ; identity-right to identity-right1)
    open BoundedSemilattice L2 using () renaming (e to e2 ; _<>_ to _<>2_ ; identity-right to identity-right2)
    open BiThresholds isPreOrder  
    
    module _ where
        open LBVar
        module _ (v1 : LBVar S1 L1 X) where
            rawLBVarFst : RawLBVar (S1 -x- S2) X
            RawLBVar.read rawLBVarFst = read v1 o fst
            RawLBVar.write rawLBVarFst s = write v1 s , e2

        module _ (v2 : LBVar S2 L2 Y) where
            rawLBVarSnd : RawLBVar (S1 -x- S2) Y
            RawLBVar.read rawLBVarSnd = read v2 o snd
            RawLBVar.write rawLBVarSnd s = e1 , write v2 s

    module _ where
        open PolyUnit
        open LBVar using (read; write) renaming 
            ( isBiThresholdRead to isBiThresholdRead'
            ; write-read to write-read'
            ; read-write-read to read-write-read')

        module _ 
            (v1 : LBVar S1 L1 X) 
            (v2 : LBVar S2 L2 Y) 
            where

            LBVarProductFst : LBVar (S1 -x- S2) (L1 -xBSLx- L2) X
            LBVar.rawLBVar LBVarProductFst = rawLBVarFst v1
            LBVar.isLBVar LBVarProductFst .IsLBVar.isBiThresholdRead (s1 , _) (s1' , _) sPs' = isBiThresholdRead' v1 s1 s1' (relatesProductFst sPs')
            LBVar.isLBVar LBVarProductFst .IsLBVar.write-read = write-read' v1
            LBVar.isLBVar LBVarProductFst .IsLBVar.read-write-read {s} with read v1 (fst s) 
            ...| unassigned  = refl
            ...| (asm x) = write-read' LBVarProductFst
            ...| conflict  = refl

            LBVarProductSnd : LBVar (S1 -x- S2) (L1 -xBSLx- L2) Y
            LBVar.rawLBVar LBVarProductSnd = rawLBVarSnd v2
            LBVar.isLBVar LBVarProductSnd .IsLBVar.isBiThresholdRead (_ , s2) (_ , s2') sPs' = isBiThresholdRead' v2 s2 s2' (relatesProductSnd sPs')
            LBVar.isLBVar LBVarProductSnd .IsLBVar.write-read = write-read' v2
            LBVar.isLBVar LBVarProductSnd .IsLBVar.read-write-read {s} with read v2 (snd s) 
            ...| unassigned  = refl
            ...| (asm x) = write-read' LBVarProductSnd
            ...| conflict  = refl

            <_-x-_>LBVar : LBVar (S1 -x- S2) (L1 -xBSLx- L2) X -x- LBVar (S1 -x- S2) (L1 -xBSLx- L2) Y
            <_-x-_>LBVar = LBVarProductFst , LBVarProductSnd

            LBVarProductIndependence : LBVarIndependence LBVarProductFst LBVarProductSnd
            LBVarIndependence.independence LBVarProductIndependence = functionProductIndependence
            LBVarIndependence.writev1 LBVarProductIndependence {s = (x , y)} =
                read v2 y           =< sym identity-right2 || read v2 >
                read v2 (y <>2 e2)  qed
            LBVarIndependence.writev2 LBVarProductIndependence {s = (x , y)} =
                read v1 x           =< sym identity-right1 || read v1 >
                read v1 (x <>1 e1)  qed

module _ {S : Set i} {bsl : BoundedSemilattice S} {X : Set j} where
    RaiseLBVarHomProductContext : LBVar S bsl X -> 
        (LBVar (S `$\back^ n $`) (bsl BSL^ n) X) `$\back^ n $` -> 
        (LBVar (S `$\back^ (1+ n) $`) (bsl BSL^ (1+ n)) X) `$\back^ n $`
    RaiseLBVarHomProductContext {0}    v t = unit
    RaiseLBVarHomProductContext {1+ n} v t = mapNTup (LBVarProductSnd v) t

    LBVarHomProduct : {n : Nat} -> LBVar S bsl X -> (LBVar (S `$\back^ n $`) (bsl BSL^ n) X) `$\back^ n $`
    LBVarHomProduct {n = 0} v = unit
    LBVarHomProduct {n = 1} v = v
    LBVarHomProduct {n = 2} v = LBVarProductFst v v , LBVarProductSnd v v
    LBVarHomProduct {n = 1+ 1+ 1+ n} v with LBVarHomProduct {n = 1+ 1+ n} v
    ...| (v' , vr) = LBVarProductFst v v' , RaiseLBVarHomProductContext {n = 1+ 1+ n} v (v' , vr)


module _ 
    {L1 L2 : Set i}
    {bslL1 : BoundedSemilattice L1}
    {bslL2 : BoundedSemilattice L2}
    (seminj : BoundedSemilatticeInjection bslL1 bslL2) 
    {X : Set k} where
    open BoundedSemilatticeInjection seminj
    open LBVar
    open OwnPrelude.Data.VarAsms using () 
        renaming (asm to pure; _>>=VarAsm_ to _>>=_; _<*>VarAsm_ to _<*>_)

    rawLiftLBVar : LBVar L1 bslL1 X -> RawLBVar L2 X
    RawLBVar.read  (rawLiftLBVar v) = read v o outf
    RawLBVar.write (rawLiftLBVar v) = inf o write v
    
    liftLBVar : LBVar L1 bslL1 X -> LBVar L2 bslL2 X
    rawLBVar (liftLBVar v) = rawLiftLBVar v
    isLBVar (liftLBVar v) .IsLBVar.isBiThresholdRead s s' sPs' = isBiThresholdRead v (outf s) (outf s') (pres-outf-rel sPs')
    isLBVar (liftLBVar v) .IsLBVar.write-read {x} = 
        read v (outf (inf (write v x)))   =<>
        read v ((outf o inf) (write v x)) =< outfoinf-id || (\h -> read v (h (write v x))) >
        read v (write v x)                =< write-read v >
        asm x qed
    isLBVar (liftLBVar v) .IsLBVar.read-write-read {s} with read v (outf s)  
    ...| unassigned  = refl
    ...| (asm x)     = write-read (liftLBVar v)
    ...| conflict    = refl

module _ 
    {S S' : Set i}
    {bslS : BoundedSemilattice S}
    {bslS' : BoundedSemilattice S'}
    (seminj : BoundedSemilatticeInjection bslS bslS')
    (v1 : LBVar S bslS X)
    (v2 : LBVar S bslS Y)
    where
    open BoundedSemilatticeInjection seminj
    open LBVar
    open BoundedSemilattice bslS using () renaming (_<>_ to _<>1_)
    open BoundedSemilattice bslS' using () renaming (_<>_ to _<>2_)

    module _ (indep : LBVarIndependence v1 v2) where
        open LBVarIndependence indep
        liftIndependence : LBVarIndependence (liftLBVar seminj v1) (liftLBVar seminj v2)
        LBVarIndependence.independence liftIndependence x y imgx imgy with independence x y (injection preservesImageOut imgx) (injection preservesImageOut imgy)
        ...| (s , readv1s=x , readv2s=y) = inf s , (
                readv1s=x :T: (read v1 s === x) [premise]
                (read v1 o outf) (inf s)   =<>
                (read v1 o (outf o inf)) s =< outfoinf-id || (\h -> (read v1 o h) s) >
                read v1 s                  =< readv1s=x >
                x                          qed
            ) , (
                readv2s=y :T: (read v2 s === y) [premise]
                (read v2 o outf) (inf s)   =<>
                (read v2 o (outf o inf)) s =< outfoinf-id || (\h -> (read v2 o h) s) >
                read v2 s                  =< readv2s=y >
                y                          qed
            )
        LBVarIndependence.writev1 liftIndependence {s} {x} =
            read v2 (outf s)                               =< writev1 >
            read v2 (outf s <>1 write v1 x)                =< sym outfoinf-id || (\h -> read v2 (outf s <>1 h (write v1 x))) >
            read v2 (outf s <>1 (outf o inf) (write v1 x)) =< sym pres-outf || read v2 >
            (read v2 o outf) (s <>2 (inf o write v1) x)    qed
        LBVarIndependence.writev2 liftIndependence {s} {x} =
            read v1 (outf s)                               =< writev2 >
            read v1 (outf s <>1 write v2 x)                =< sym outfoinf-id || (\h -> read v1 (outf s <>1 h (write v2 x))) >
            read v1 (outf s <>1 (outf o inf) (write v2 x)) =< sym pres-outf || read v1 >
            (read v1 o outf) (s <>2 (inf o write v2) x)    qed

module Bundles where
    module LBVarBundle where
        record LBVar' i j : Set (lsuc (i ~U~ j)) where
            field
                Carrier : Set i
                Aim     : Set j
                boundedSemilattice : BoundedSemilattice Carrier
                lbVar : LBVar Carrier boundedSemilattice Aim
            open LBVar lbVar

        toLBVarBundle : forall {S BSL X} -> LBVar {i} {j} S BSL X -> LBVar' i j
        toLBVarBundle {S} {BSL} {X} lbVar = 
            record { Carrier            = S 
                ; Aim                = X
                ; boundedSemilattice = BSL
                ; lbVar              = lbVar }

    module _ {i} {j} where
        open LBVarBundle -- using (module LBVar'; toLBVarBundle)
        open LBVar'

        LiftProdByVarCtx : LBVar' i j -> (LBVar' i j `$\back^ n $`) -> (LBVar' i j `$\back^ n $`)
        LiftProdByVarCtx {n = 0} v unit = unit
        LiftProdByVarCtx {n = 1} v v' = toLBVarBundle (LBVarProductSnd (lbVar v) (lbVar v'))
        LiftProdByVarCtx {n = 1+ 1+ n} v (v' , vars) = 
            ( toLBVarBundle (LBVarProductSnd (lbVar v) (lbVar v'))
            , LiftProdByVarCtx v vars )

        LBVarProductSpace : (LBVar' i j `$\back^ n $`) -> (LBVar' i j `$\back^ n $`)
        LBVarProductSpace {n = 0} _        = unit
        LBVarProductSpace {n = 1} v        = v
        LBVarProductSpace {n = 2} (v , v') = 
            ( toLBVarBundle (LBVarProductFst (lbVar v) (lbVar v'))
            , toLBVarBundle (LBVarProductSnd (lbVar v) (lbVar v')))
        LBVarProductSpace {n = 1+ 1+ 1+ n} (v , v' , vars) = 
            ( toLBVarBundle (LBVarProductFst (lbVar v) (lbVar v'))
            , LiftProdByVarCtx {n = 1+ 1+ n} v (v' , vars) ) 