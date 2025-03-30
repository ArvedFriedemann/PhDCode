{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.GeneralSolving.BiThresholdsAndContainersPartIII where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open PropositionalEq using () renaming (_===_ to _=P=_ ; _=/=_ to _=/P/=_ ; refl to reflP)
module PEq = PropositionalEq
open import OwnPrelude.Data.BiThresholdVariables
open import OwnPrelude.Data.VarAsms renaming (module MonadNames to VarAsmsMonadNames; monad to monadVarAsm)
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.TrivialLattices
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.ILattices
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Data.Containers
open ContainerCategorical
open import OwnPrelude.Data.BiThresholdVariables


open import OwnPrelude.GeneralSolving.BiThresholdsAndContainers
open import OwnPrelude.GeneralSolving.BiThresholdsAndContainersPartII

{-# DISPLAY LiftL j Zero = PolyZero.Zero #-}

open ExistsSyntax

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d e f g h i j k l m n p p1 p2 p3 p' q r s s' s1 s2 s3 t u v w x y z fm i' j' k' l' A B C X Y K M F alg px py pz pm x=y y=z x=z mon Qx Qy Qz : ST

-- \tagcode{BiThresholdsAndContainersPtIII}

module TrivialContainerVariable {C : Container i j} (decEq : DecEq (Container.S C)) {A : Set k} (LatA : Lattice A) where
    open TrivialContainerLattice {i = i} {j = j} {C = C} decEq LatA
    open Container C hiding ([[_]])
    open Container using ([[_]])
    open IncreaseAssignmentProperty
    open DecEq decEq
    open VarAsmsMonadNames

    trivialVariable : forall {l} -> LBVar ([[ latticedContainer ]] A) (Lattice.boundedMeetSemilattice latticedContainerLattice) ([[ C ]] (Unit {l}))
    trivialVariable .LBVar.rawLBVar .RawLBVar.read (topTB , p) = unassigned
    trivialVariable .LBVar.rawLBVar .RawLBVar.read (botTB , p) = conflict
    trivialVariable .LBVar.rawLBVar .RawLBVar.read (valTB s , p) = asm (s , \_ -> unit)
    trivialVariable .LBVar.rawLBVar .RawLBVar.write (s , p) = (valTB s , \_ -> LatA.top)
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (topTB , p1) (s2 , p2) 1P2 = unas-to-anything refl
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (botTB , p1) (topTB , p2) 1P2 = absurd $ encodeTB (1P2 || fst)
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (botTB , p1) (botTB , p2) 1P2 = conf-conf refl refl
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (botTB , p1) (valTB x , p2) 1P2 = absurd $ encodeTB (1P2 || fst)
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (topTB , p2) 1P2 = absurd $ encodeTB (1P2 || fst)
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (botTB , p2) 1P2 = asm-conf refl refl
    trivialVariable .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (valTB y , p2) 1P2 with x == y
    ... | yes x=y = asm-eq refl \i -> asm (x=y (~ i) , \_ -> unit)
    ... | no ¬x=y = absurd $ encodeTB (1P2 || fst)
    trivialVariable .LBVar.isLBVar .IsLBVar.write-read = refl
    trivialVariable .LBVar.isLBVar .IsLBVar.read-write-read {s = topTB , p} = refl
    trivialVariable .LBVar.isLBVar .IsLBVar.read-write-read {s = botTB , p} = refl
    trivialVariable .LBVar.isLBVar .IsLBVar.read-write-read {s = valTB x , p} = refl

    module PositionVariables {B : Set l} 
        (decEqPos : forall {s} -> DecEq (Container.P C s))
        (varB : LBVar A (Lattice.boundedMeetSemilattice LatA) B) 
        (decEqAxiom : forall {x y : S} {x=y : x === y} -> (lq : valTB x LatS.leq valTB y) -> (x==y=yes : x == y === yes x=y) -> (coerce (\i -> x==y=yes i <?dec>[ valTB x ][ botTB ] === valTB y) lq) === (x=y || valTB) ) where
        
        open VarAsmsMonadNames

        -- \tagcode{subvariables}

        subvariables : [[ C ]] (Unit {k}) -> [[ C ]] (LBVar ([[ latticedContainer ]] A) (Lattice.boundedMeetSemilattice latticedContainerLattice) B)
        subvariables (s , p) = (s , subvar)
            where
                subvar : P s -> LBVar ([[ latticedContainer ]] A) (Lattice.boundedMeetSemilattice latticedContainerLattice) B
                subvar pm .LBVar.rawLBVar .RawLBVar.read (topTB , p)   = unassigned
                subvar pm .LBVar.rawLBVar .RawLBVar.read (botTB , p)   = conflict
                subvar pm .LBVar.rawLBVar .RawLBVar.read (valTB s' , p') with s == s' 
                ... | yes s=s' = LBVar.read varB (p' (coerce (s=s' || P) pm))
                ... | no ¬s=s' = unassigned
                subvar pm .LBVar.rawLBVar .RawLBVar.write b = (valTB s , \pm' -> (DecEq._==_ decEqPos pm pm') <?dec>[ LBVar.write varB b ][ LatA.top ]) 
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (topTB , p1)   (s2 , p2) 1P2 = unas-to-anything refl
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (botTB , p1) (topTB , p2) 1P2 = absurd $ encodeTB (1P2 || fst)
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (botTB , p1) (botTB , p2) 1P2 = conf-conf refl refl
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (botTB , p1) (valTB x , p2) 1P2 = absurd $ encodeTB (1P2 || fst)
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (topTB , p2) 1P2 = absurd $ encodeTB (1P2 || fst)
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (botTB , p2) 1P2 with s == x
                ... | no ¬s=x = unas-to-anything refl
                ... | yes s=x with LBVar.read varB (p1 (coerce (s=x || P) pm)) 
                ...     | unassigned = unas-to-anything refl
                ...     | asm b' = asm-conf refl refl
                ...     | conflict = conf-conf refl refl
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (valTB y , p2) 1P2 with s == x in s==x-eq | s == y in s==y-eq
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (valTB y , p2) 1P2 | yes s=x | yes s=y with x == y in x==y-eq
                ... | yes x=y = LBVar.isBiThresholdRead varB (p1 (coerce (s=x || P) pm)) (p2 (coerce (s=y || P) pm))
                    ( p1 (coerce (s=x || P) pm) LatA./\ p2 (coerce (s=y || P) pm)                                                 =< encodeDec (trans (sym (propToPath s==y-eq)) (decEq-trans (propToPath s==x-eq) (propToPath x==y-eq))) || (\h -> p1 (coerce (s=x || P) pm) LatA./\ p2 (coerce (h || P) pm)) >
                      
                      p1 (coerce (s=x || P) pm) LatA./\ p2 (coerce (trans s=x x=y || P) pm)                                       =< sym (coerce-trans-subst P s=x x=y ) || (_$ pm) || (\h -> p1 (coerce (s=x || P) pm) LatA./\ p2 h) >
                      p1 (coerce (s=x || P) pm) LatA./\ p2 (coerce (x=y || P) (coerce (s=x || P) pm))                             =<  (\i -> p1 (coerce-refl {x = (coerce (s=x || P) pm)} (~ i)) LatA./\ p2 (coerce (x=y || P) (coerce-refl {x = coerce (s=x || P) pm} (~ i)))) >
                      p1 (coerce refl (coerce (s=x || P) pm)) LatA./\ p2 (coerce (x=y || P) (coerce refl (coerce (s=x || P) pm))) =< (\i -> snd (1P2 i) (coerce (\j -> P``tb (transFill (s=x || valTB) (1P2 || fst) i j)) pm)) >
                      p2 (coerce (trans (s=x || valTB) (1P2 || fst) || P``tb) pm)                                                 =< ( (coerce (
                            (coerce (\i -> (propToPath x==y-eq) i <?dec>[ valTB x ][ botTB ] === valTB y) (coerce (\i -> (propToPath x==y-eq) (~ i) <?dec>[ valTB x ][ botTB ] === valTB y) (1P2 || fst)) === (x=y || valTB)) =< (coerce-sym-subst id (path-to-eq (\i -> (propToPath x==y-eq) i <?dec>[ valTB x ][ botTB ] === valTB y)) || (_$ (1P2 || fst))  || (_=== (x=y || valTB))) >
                            ((1P2 || fst) === (x=y || valTB)) qed) 
                            (decEqAxiom (coerce (\i -> (propToPath x==y-eq) (~ i) <?dec>[ valTB x ][ botTB ] === valTB y) (1P2 || fst)) (propToPath x==y-eq)))) || (\h -> p2 (coerce (trans (s=x || valTB) h || P``tb) pm)) > 
                      p2 (coerce (trans (s=x || valTB) (x=y || valTB) || P``tb) pm)                                               =< trans-cong {f = valTB} || (\h -> p2 (coerce (h || P``tb) pm)) >
                      p2 (coerce (trans s=x x=y || valTB || P``tb) pm)                                                            =< sym (encodeDec (trans (sym (propToPath s==y-eq)) (decEq-trans (propToPath s==x-eq) (propToPath x==y-eq)))) || (\h -> p2 (coerce (h || valTB || P``tb) pm)) >

                      p2 (coerce (s=y || P) pm)                                                                                   qed )
                ... | no ¬x=y = absurd (¬x=y (trans (sym s=x) s=y))
                
                
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (valTB y , p2) 1P2 | yes s=x | no ¬s=y with x == y 
                ... | yes x=y = absurd (¬s=y (trans s=x x=y))
                ... | no ¬x=y = absurd (encodeTB (1P2 || fst))
                subvar pm .LBVar.isLBVar .IsLBVar.isBiThresholdRead (valTB x , p1) (valTB y , p2) 1P2 | no ¬s=x | r = unas-to-anything refl
                subvar pm .LBVar.isLBVar .IsLBVar.write-read {x} with s == s in s==s-eq
                ... | no ¬s=s = absurd (¬s=s refl)
                ... | yes s=s =
                        LBVar.read varB (DecEq._==_ decEqPos pm (coerce (s=s  || P) pm) <?dec>[ LBVar.write varB x ][ LatA.top ]) =< encodeDec (trans (sym (propToPath s==s-eq)) decEq-refl) || (\h -> LBVar.read varB (DecEq._==_ decEqPos pm (coerce (h || P) pm) <?dec>[ LBVar.write varB x ][ LatA.top ])) >
                        LBVar.read varB (DecEq._==_ decEqPos pm (coerce (refl || P) pm) <?dec>[ LBVar.write varB x ][ LatA.top ]) =< coerce-refl || (\h -> LBVar.read varB (DecEq._==_ decEqPos pm h <?dec>[ LBVar.write varB x ][ LatA.top ])) >
                        LBVar.read varB (DecEq._==_ decEqPos pm pm <?dec>[ LBVar.write varB x ][ LatA.top ]) =< DecEq.decEq-refl decEqPos || (\h -> LBVar.read varB (h <?dec>[ LBVar.write varB x ][ LatA.top ])) >
                        LBVar.read varB (LBVar.write varB x) =< LBVar.write-read varB >
                        asm x qed
                subvar pm .LBVar.isLBVar .IsLBVar.read-write-read {s = topTB , p} = refl
                subvar pm .LBVar.isLBVar .IsLBVar.read-write-read {s = botTB , p} = refl
                subvar pm .LBVar.isLBVar .IsLBVar.read-write-read {s = valTB s' , p'} with s == s' 
                ... | no ¬s=s' = refl {a = unassigned}
                ... | yes s=s' with LBVar.read varB (p' (coerce (s=s' || P) pm))
                ... | unassigned = refl {a = unassigned}
                ... | conflict   = refl {a = conflict}
                ... | asm s'' with s == s in s==s-eq
                ... | no ¬s=s = absurd (¬s=s refl)
                ... | yes s=s = 
                    LBVar.read varB (DecEq._==_ decEqPos pm (coerce (s=s || P) pm) <?dec>[ LBVar.write varB s'' ][ LatA.top ]) =< encodeDec (trans (sym (propToPath s==s-eq)) decEq-refl) ||  (\h -> LBVar.read varB (DecEq._==_ decEqPos pm (coerce (h || P) pm) <?dec>[ LBVar.write varB s'' ][ LatA.top ])) >
                    LBVar.read varB (DecEq._==_ decEqPos pm (coerce (refl || P) pm) <?dec>[ LBVar.write varB s'' ][ LatA.top ]) =< coerce-refl || (\h -> LBVar.read varB (DecEq._==_ decEqPos pm h <?dec>[ LBVar.write varB s'' ][ LatA.top ])) >
                    LBVar.read varB (DecEq._==_ decEqPos pm pm <?dec>[ LBVar.write varB s'' ][ LatA.top ]) =< DecEq.decEq-refl decEqPos || (\h -> LBVar.read varB (h <?dec>[ LBVar.write varB s'' ][ LatA.top ])) >
                    LBVar.read varB (yes (refl {a = s''}) <?dec>[ LBVar.write varB s'' ][ LatA.top ]) =< LBVar.write-read varB {x = s''} >
                    asm s'' qed