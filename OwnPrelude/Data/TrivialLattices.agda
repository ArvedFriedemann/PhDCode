{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.TrivialLattices where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open import OwnPrelude.Equality
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Categorical.Monads

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L L1 L2 S S1 S2 : Set i
        F G M : Set i -> Set j
        a b x y z m x1 x2 y1 y2 z1 z2 tp bt lf rg bth : A
        f g : A -> B

data TB (A : Set i) : Set i where
    topTB : TB A
    botTB : TB A
    valTB : A -> TB A

_tb = TB

top:_bot:_val:_ : B -> B -> (A -> B) -> TB A -> B
top:_bot:_val:_ tp bt vl topTB = tp
top:_bot:_val:_ tp bt vl botTB = bt
top:_bot:_val:_ tp bt vl (valTB x) = vl x

monadTB : Monad {i} TB
monadTB .Monad.rawMonad .RawMonad.return = valTB
(monadTB .Monad.rawMonad RawMonad.>>= topTB) f = topTB
(monadTB .Monad.rawMonad RawMonad.>>= botTB) f = botTB
(monadTB .Monad.rawMonad RawMonad.>>= valTB x) f = f x
monadTB .Monad.isMonad .IsMonad.left-identity = refl
monadTB .Monad.isMonad .IsMonad.right-identity {m = topTB} = refl
monadTB .Monad.isMonad .IsMonad.right-identity {m = botTB} = refl
monadTB .Monad.isMonad .IsMonad.right-identity {m = valTB x} = refl
monadTB .Monad.isMonad .IsMonad.associative {m = topTB} = refl
monadTB .Monad.isMonad .IsMonad.associative {m = botTB} = refl
monadTB .Monad.isMonad .IsMonad.associative {m = valTB x} = refl

module _ {A : Set i} where
    CoverTB : TB A -> TB A -> Set i
    CoverTB topTB topTB = Unit
    CoverTB botTB botTB = Unit
    CoverTB (valTB a) (valTB b) = a === b
    CoverTB _ _ = Zero

    encodeReflTB : CoverTB a a
    encodeReflTB {a = topTB}   = unit
    encodeReflTB {a = botTB}   = unit
    encodeReflTB {a = valTB x} = refl

    encodeTB : {a b : TB A} -> a === b -> CoverTB a b
    encodeTB {a} = J (\b _ -> CoverTB a b) encodeReflTB

module TrivialLattice {X : Set i} (decEq : DecEq X) where
    open DecEq decEq

    private
        -- order is so that it computes better 
        
        meet : TB X -> TB X -> TB X
        meet topTB x   = x
        meet botTB _   = botTB
        meet x   topTB = x
        meet _   botTB = botTB
        meet (valTB x) (valTB y) = x == y <?dec>[ valTB x ][ botTB ]

        join : TB X -> TB X -> TB X
        join topTB _   = topTB
        join botTB x   = x
        join _   topTB = topTB
        join x   botTB = x
        join (valTB x) (valTB y) = x == y <?dec>[ valTB x ][ topTB ]

    module _ {P : X tb -> Set j} where
        meetDestr : 
            (P topTB -> A) -> 
            (P botTB -> A) -> 
            (P a -> A) -> 
            (P b -> A) ->
            (P a -> P b -> A) ->
            P (meet a b) -> A
        meetDestr {a = topTB}   {b = topTB}   tp bt lf rg bth pm = tp pm
        meetDestr {a = topTB}   {b = botTB}   tp bt lf rg bth pm = bt pm
        meetDestr {a = topTB}   {b = valTB x} tp bt lf rg bth pm = rg pm
        meetDestr {a = botTB}   {b}           tp bt lf rg bth pm = bt pm
        meetDestr {a = valTB x} {b = topTB}   tp bt lf rg bth pm = lf pm
        meetDestr {a = valTB x} {b = botTB}   tp bt lf rg bth pm = bt pm
        meetDestr {a = valTB x} {b = valTB y} tp bt lf rg bth pm with x == y
        ... | yes x=y = bth pm (coerce (x=y || P o valTB) pm)
        ... | no  _ = bt pm
            -- ifDec x == y
            -- then (\x=y -> bth (coerce (applyEq-<?dec> x=y || P) pm) (coerce (P (x == y <?dec>[ valTB x ][ botTB ]) =< applyEq-<?dec> x=y || P > P (valTB x) =< x=y || P o valTB > P (valTB y) qed) pm))
            -- else \ ¬x=y -> bt (coerce (applyNEq-<?dec> ¬x=y || P) pm)

        

    meetVal : x === y -> meet (valTB x) (valTB y) === valTB x
    meetVal {x} {y} x=y = 
        ifDec (x == y)
        then (\  x=y -> applyEq-<?dec> x=y)
        else (\ ¬x=y -> absurd (¬x=y x=y) )

    joinVal : x === y -> join (valTB x) (valTB y) === valTB x
    joinVal {x} {y} x=y = 
        ifDec (x == y)
        then (\  x=y -> applyEq-<?dec> x=y)
        else (\ ¬x=y -> absurd (¬x=y x=y) )

    meetBot : x =/= y -> meet (valTB x) (valTB y) === botTB
    meetBot {x} {y} ¬x=y = 
        ifDec (x == y)
        then (\  x=y -> absurd (¬x=y x=y))
        else (\ ¬x=y -> applyNEq-<?dec> ¬x=y)

    joinTop : x =/= y -> join (valTB x) (valTB y) === topTB
    joinTop {x} {y} ¬x=y = 
        ifDec (x == y)
        then (\  x=y -> absurd (¬x=y x=y))
        else (\ ¬x=y -> applyNEq-<?dec> ¬x=y)

    trivialMeetSemilattice : Semilattice (TB X)
    RawSemilattice._<>_ (Semilattice.rawSemilattice trivialMeetSemilattice) = meet
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = topTB} {y} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = botTB} {y} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = topTB} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = botTB} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = valTB y} {z = topTB} with x == y 
    ... | yes x=y = refl
    ... | no ¬x=y = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = valTB y} {z = botTB} with x == y 
    ... | yes x=y = refl
    ... | no ¬x=y = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = valTB y} {z = valTB z} = 
        ifDec x == y
        then ifDec y == z
            then ifDec x == z
                then (\ x=z y=z x=y ->
                    meet (valTB x) (meet (valTB y) (valTB z)) =< meetVal y=z || meet (valTB x) > 
                    meet (valTB x) (valTB y)                  =< meetVal x=y > 
                    (valTB x)                                 =< sym (meetVal x=z) > 
                    meet (valTB x) (valTB z)                  =< sym (meetVal x=y) || (\h -> meet h (valTB z)) > 
                    meet (meet (valTB x) (valTB y)) (valTB z) qed )
                else (\ ¬x=z y=z x=y -> absurd (¬x=z (trans x=y y=z)) )
            else ifDec x == z
                then (\ x=z ¬y=z x=y -> absurd (¬y=z (trans (sym x=y) x=z)))
                else (\ ¬x=z ¬y=z x=y -> 
                    meet (valTB x) (meet (valTB y) (valTB z)) =< meetBot ¬y=z || meet (valTB x) > 
                    botTB                                     =< sym (meetBot ¬x=z) > 
                    meet (valTB x) (valTB z)                  =< sym (meetVal x=y) || (\h -> meet h (valTB z)) > 
                    meet (meet (valTB x) (valTB y)) (valTB z) qed)
        else ifDec y == z
            then (\ y=z ¬x=y -> 
                meet (valTB x) (meet (valTB y) (valTB z)) =< meetVal y=z || meet (valTB x) > 
                meet (valTB x) (valTB y)                  =< meetBot ¬x=y > 
                meet botTB (valTB z)                       =< sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) > 
                meet (meet (valTB x) (valTB y)) (valTB z) qed)
            else (\ ¬y=z ¬x=y -> 
                meet (valTB x) (meet (valTB y) (valTB z)) =< meetBot ¬y=z || meet (valTB x) > 
                meet (valTB x) botTB                      =< sym (meetBot ¬x=y) || (\h -> meet h (valTB z)) > 
                meet (meet (valTB x) (valTB y)) (valTB z) qed)

    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = topTB} {y = topTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = topTB} {y = botTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = topTB} {y = valTB x} = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = botTB} {y = topTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = botTB} {y = botTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = botTB} {y = valTB x} = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = topTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = botTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} {y = valTB y} = 
        ifDec x == y
        then (\  x=y -> 
            meet (valTB x) (valTB y) =< meetVal x=y > 
            valTB x                  =< x=y || valTB > 
            valTB y                  =< sym (meetVal (sym x=y)) >
            meet (valTB y) (valTB x) qed)
        else \ ¬x=y -> 
            meet (valTB x) (valTB y) =< meetBot ¬x=y > 
            botTB                    =< sym (meetBot (¬x=y o sym)) > 
            meet (valTB y) (valTB x) qed

    IsSemilattice.idempotent (Semilattice.isSemilattice trivialMeetSemilattice) {x = topTB}   = refl
    IsSemilattice.idempotent (Semilattice.isSemilattice trivialMeetSemilattice) {x = botTB}   = refl
    IsSemilattice.idempotent (Semilattice.isSemilattice trivialMeetSemilattice) {x = valTB x} =
        ifDec x == x
        then (\ x=x -> meetVal x=x)
        else (\ ¬x=x -> absurd (¬x=x refl))

    trivialJoinSemilattice : JoinSemilattice (TB X)
    RawSemilattice._<>_ (Semilattice.rawSemilattice trivialJoinSemilattice) = join
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = topTB} {y} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = botTB} {y} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = topTB} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = botTB} {z} = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = valTB y} {z = topTB} with x == y 
    ... | yes _ = refl
    ... | no  _ = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = valTB y} {z = botTB} with x == y 
    ... | yes _ = refl
    ... | no  _ = refl
    IsSemilattice.associative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = valTB y} {z = valTB z} = 
        ifDec x == y
        then ifDec y == z
            then ifDec x == z
                then (\ x=z y=z x=y ->
                    join (valTB x) (join (valTB y) (valTB z)) =< joinVal y=z || join (valTB x) > 
                    join (valTB x) (valTB y)                  =< joinVal x=y > 
                    (valTB x)                                 =< sym (joinVal x=z) > 
                    join (valTB x) (valTB z)                  =< sym (joinVal x=y) || (\h -> join h (valTB z)) > 
                    join (join (valTB x) (valTB y)) (valTB z) qed )
                else (\ ¬x=z y=z x=y -> absurd (¬x=z (trans x=y y=z)) )
            else ifDec x == z
                then (\ x=z ¬y=z x=y -> absurd (¬y=z (trans (sym x=y) x=z)))
                else (\ ¬x=z ¬y=z x=y -> 
                    join (valTB x) (join (valTB y) (valTB z)) =< joinTop ¬y=z || join (valTB x) > 
                    topTB                                     =< sym (joinTop ¬x=z) > 
                    join (valTB x) (valTB z)                  =< sym (joinVal x=y) || (\h -> join h (valTB z)) > 
                    join (join (valTB x) (valTB y)) (valTB z) qed)
        else ifDec y == z
            then (\ y=z ¬x=y -> 
                join (valTB x) (join (valTB y) (valTB z)) =< joinVal y=z || join (valTB x) > 
                join (valTB x) (valTB y)                  =< joinTop ¬x=y > 
                join topTB (valTB z)                       =< sym (joinTop ¬x=y) || (\h -> join h (valTB z)) > 
                join (join (valTB x) (valTB y)) (valTB z) qed)
            else (\ ¬y=z ¬x=y -> 
                join (valTB x) (join (valTB y) (valTB z)) =< joinTop ¬y=z || join (valTB x) > 
                join (valTB x) topTB                      =< sym (joinTop ¬x=y) || (\h -> join h (valTB z)) > 
                join (join (valTB x) (valTB y)) (valTB z) qed)

    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = topTB} {y = topTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = topTB} {y = botTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = topTB} {y = valTB x} = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = botTB} {y = topTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = botTB} {y = botTB}   = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = botTB} {y = valTB x} = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = topTB} = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = botTB} = refl
    IsSemilattice.commutative (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} {y = valTB y} =
        ifDec x == y
        then (\  x=y -> 
            join (valTB x) (valTB y) =< joinVal x=y > 
            valTB x                  =< x=y || valTB > 
            valTB y                  =< sym (joinVal (sym x=y)) >
            join (valTB y) (valTB x) qed)
        else \ ¬x=y -> 
            join (valTB x) (valTB y) =< joinTop ¬x=y > 
            topTB                    =< sym (joinTop (¬x=y o sym)) > 
            join (valTB y) (valTB x) qed

    IsSemilattice.idempotent (Semilattice.isSemilattice trivialJoinSemilattice) {x = topTB}   = refl
    IsSemilattice.idempotent (Semilattice.isSemilattice trivialJoinSemilattice) {x = botTB}   = refl
    IsSemilattice.idempotent (Semilattice.isSemilattice trivialJoinSemilattice) {x = valTB x} = 
        ifDec x == x
        then (\ x=x -> joinVal x=x)
        else (\ ¬x=x -> absurd (¬x=x refl))

    trivialBoundedMeetSemilattice : BoundedMeetSemilattice (TB X)
    BoundedSemilattice.e trivialBoundedMeetSemilattice = topTB
    BoundedSemilattice.semilattice trivialBoundedMeetSemilattice = trivialMeetSemilattice
    BoundedSemilattice.identity-left trivialBoundedMeetSemilattice = refl

    trivialBoundedJoinSemilattice : BoundedJoinSemilattice (TB X)
    BoundedSemilattice.e trivialBoundedJoinSemilattice = botTB
    BoundedSemilattice.semilattice trivialBoundedJoinSemilattice = trivialJoinSemilattice
    BoundedSemilattice.identity-left trivialBoundedJoinSemilattice = refl

    trivialLattice : Lattice (TB X)
    Lattice.boundedMeetSemilattice trivialLattice = trivialBoundedMeetSemilattice
    Lattice.boundedJoinSemilattice trivialLattice = trivialBoundedJoinSemilattice
    Lattice.absorb-/\ trivialLattice {a = topTB} {b} = refl
    Lattice.absorb-/\ trivialLattice {a = botTB} {b} = refl
    Lattice.absorb-/\ trivialLattice {a = valTB x} {b = topTB} = refl
    Lattice.absorb-/\ trivialLattice {a = valTB x} {b = botTB} with x == x 
    ...| yes x=x = refl
    ...| no ¬x=x = absurd $ ¬x=x refl
    Lattice.absorb-/\ trivialLattice {a = valTB x} {b = valTB y} =
        ifDec x == y
        then (\ x=y -> 
            meet (valTB x) (join (valTB x) (valTB y)) =< joinVal x=y || meet (valTB x) > 
            meet (valTB x) (valTB x) =< meetVal refl >
            valTB x qed)
        else \ ¬x=y -> 
            meet (valTB x) (join (valTB x) (valTB y)) =< joinTop ¬x=y || meet (valTB x) > 
            valTB x qed
    
    Lattice.absorb-\/ trivialLattice {a = topTB} {b} = refl
    Lattice.absorb-\/ trivialLattice {a = botTB} {b} = refl
    Lattice.absorb-\/ trivialLattice {a = valTB x} {b = topTB} with x == x 
    ...| yes x=x = refl
    ...| no ¬x=x = absurd $ ¬x=x refl
    Lattice.absorb-\/ trivialLattice {a = valTB x} {b = botTB} = refl
    Lattice.absorb-\/ trivialLattice {a = valTB x} {b = valTB y} =
        ifDec x == y
        then (\ x=y -> 
            join (valTB x) (meet (valTB x) (valTB y)) =< meetVal x=y || join (valTB x) > 
            join (valTB x) (valTB x) =< joinVal refl >
            valTB x qed)
        else \ ¬x=y -> 
            join (valTB x) (meet (valTB x) (valTB y)) =< meetBot ¬x=y || join (valTB x) > 
            valTB x qed

module PropTrivialLattice {X : Set i} (propDecEq : PropDecEq X) where
    open PropDecEq propDecEq

    private
        -- order is so that it computes better 
        
        meet : TB X -> TB X -> TB X
        meet topTB x   = x
        meet botTB _   = botTB
        meet x   topTB = x
        meet _   botTB = botTB
        meet (valTB x) (valTB y) = x == y <?dec>[ valTB x ][ botTB ]

        join : TB X -> TB X -> TB X
        join topTB _   = topTB
        join botTB x   = x
        join _   topTB = topTB
        join x   botTB = x
        join (valTB x) (valTB y) = x == y <?dec>[ valTB x ][ topTB ]

    trivialLattice : Lattice (X tb)
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.e = topTB
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.rawSemilattice .RawSemilattice._<>_ = meet
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {(topTB)} {(y)} {(z)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {(botTB)} {(y)} {(z)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {(topTB)} {(z)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {(botTB)} {(z)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {(topTB)} with x == y
    ... | yes PropositionalEq.refl = refl
    ... | no  _ = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {(botTB)} with x == y 
    ... | yes PropositionalEq.refl = refl
    ... | no _ = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} with x == y | x == z | y == z
    ... | yes PropositionalEq.refl | yes PropositionalEq.refl | yes _ = refl
    ... | yes PropositionalEq.refl | yes PropositionalEq.refl | no ¬y=z = absurd (¬y=z PropositionalEq.refl)
    ... | yes PropositionalEq.refl | no ¬x=z | yes PropositionalEq.refl = absurd (¬x=z PropositionalEq.refl)
    ... | yes PropositionalEq.refl | no ¬x=z | no _ with x == z 
    ... | yes PropositionalEq.refl = absurd (¬x=z PropositionalEq.refl)
    ... | no _ = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no ¬x=y | yes PropositionalEq.refl | yes PropositionalEq.refl = absurd (¬x=y PropositionalEq.refl)
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no _ | yes PropositionalEq.refl | no x2 = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no _ | no ¬x=z | yes PropositionalEq.refl with x == y 
    ... | yes PropositionalEq.refl = absurd (¬x=z PropositionalEq.refl)
    ... | no _ = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no x1 | no x2 | no x3 = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(topTB)} {(topTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(topTB)} {(botTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(topTB)} {valTB x} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(botTB)} {(topTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(botTB)} {(botTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(botTB)} {valTB x} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {(topTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {(botTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {valTB y} with x == y 
    ... | yes PropositionalEq.refl with x == x
    ... | yes _ = refl
    ... | no  ¬x=y = absurd (¬x=y PropositionalEq.refl)
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {valTB y} | no ¬x=y with y == x
    ... | yes PropositionalEq.refl = absurd (¬x=y PropositionalEq.refl)
    ... | no _ = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent {(topTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent {(botTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent {valTB x} with x == x
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.identity-left {(topTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.identity-left {(botTB)} = refl
    trivialLattice .Lattice.boundedMeetSemilattice .BoundedSemilattice.identity-left {valTB x} with x == x 
    ... | yes _ = refl
    ... | no  _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.e = botTB
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.rawSemilattice .RawSemilattice._<>_ = join
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {(topTB)} {(y)} {(z)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {(botTB)} {(y)} {(z)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {(topTB)} {(z)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {(botTB)} {(z)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {(topTB)} with x == y
    ... | yes _ = refl
    ... | no  _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {(botTB)} with x == y 
    ... | yes _ = refl
    ... | no  _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} with x == y | x == z | y == z 
    ... | yes PropositionalEq.refl | yes PropositionalEq.refl | yes _   = refl
    ... | yes PropositionalEq.refl | yes PropositionalEq.refl | no ¬y=z = absurd (¬y=z PropositionalEq.refl)
    ... | yes PropositionalEq.refl | no _ | yes PropositionalEq.refl    = refl
    ... | yes PropositionalEq.refl | no ¬x=z | no x1 with x == z
    ... | yes PropositionalEq.refl = absurd (¬x=z PropositionalEq.refl)
    ... | no _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no ¬x=y | yes PropositionalEq.refl | yes PropositionalEq.refl with x == x
    ... | yes _ = absurd (¬x=y PropositionalEq.refl)
    ... | no  _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no _ | yes _ | no _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no ¬x=y | no _ | yes PropositionalEq.refl with x == y
    ... | yes PropositionalEq.refl = absurd (¬x=y PropositionalEq.refl)
    ... | no _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.associative {valTB x} {valTB y} {valTB z} | no x1 | no x2 | no x3 = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(topTB)} {(topTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(topTB)} {(botTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(topTB)} {valTB x} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(botTB)} {(topTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(botTB)} {(botTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {(botTB)} {valTB x} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {(topTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {(botTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {valTB y} with x == y
    ... | yes PropositionalEq.refl with x == x 
    ... | yes _ = refl
    ... | no  ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.commutative {valTB x} {valTB y} | no ¬x=y with y == x
    ... | yes PropositionalEq.refl = absurd (¬x=y PropositionalEq.refl)
    ... | no _ = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent {(topTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent {(botTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.semilattice .Semilattice.isSemilattice .IsSemilattice.idempotent {valTB x} with x == x
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.identity-left {(topTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.identity-left {(botTB)} = refl
    trivialLattice .Lattice.boundedJoinSemilattice .BoundedSemilattice.identity-left {valTB x} with x == x
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.absorb-/\ {(topTB)} {(b)} = refl
    trivialLattice .Lattice.absorb-/\ {(botTB)} {(b)} = refl
    trivialLattice .Lattice.absorb-/\ {valTB x} {(topTB)} = refl
    trivialLattice .Lattice.absorb-/\ {valTB x} {(botTB)} with x == x
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.absorb-/\ {valTB x} {valTB y} with x == y
    ... | yes PropositionalEq.refl with x == x
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.absorb-/\ {valTB x} {valTB y} | no _ = refl
    trivialLattice .Lattice.absorb-\/ {(topTB)} {(b)} = refl
    trivialLattice .Lattice.absorb-\/ {(botTB)} {(b)} = refl
    trivialLattice .Lattice.absorb-\/ {valTB x} {(topTB)} with x == x 
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.absorb-\/ {valTB x} {(botTB)} = refl
    trivialLattice .Lattice.absorb-\/ {valTB x} {valTB y} with x == y 
    ... | yes _ with x == x 
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x PropositionalEq.refl)
    trivialLattice .Lattice.absorb-\/ {valTB x} {valTB y} | no _ = refl



module _ {i} where
    rawUnitSemilattice : RawSemilattice {i} Unit
    RawSemilattice._<>_ rawUnitSemilattice _ _ = unit

    UnitSemilattice : Semilattice {i} Unit
    Semilattice.rawSemilattice UnitSemilattice = rawUnitSemilattice
    IsSemilattice.associative (Semilattice.isSemilattice UnitSemilattice) = refl
    IsSemilattice.commutative (Semilattice.isSemilattice UnitSemilattice) = refl
    IsSemilattice.idempotent (Semilattice.isSemilattice UnitSemilattice) = refl

    UnitBoundedSemilattice : BoundedSemilattice {i} Unit
    BoundedSemilattice.e UnitBoundedSemilattice = unit
    BoundedSemilattice.semilattice UnitBoundedSemilattice = UnitSemilattice
    BoundedSemilattice.identity-left UnitBoundedSemilattice = refl

    UnitLattice : Lattice {i} Unit
    Lattice.boundedMeetSemilattice UnitLattice = UnitBoundedSemilattice
    Lattice.boundedJoinSemilattice UnitLattice = UnitBoundedSemilattice
    Lattice.absorb-/\ UnitLattice = refl
    Lattice.absorb-\/ UnitLattice = refl