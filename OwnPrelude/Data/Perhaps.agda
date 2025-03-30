{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-postfix #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.Perhaps where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open PolyZero
open NatOp hiding (_leq_)
open ListOp hiding (and; or)
open import OwnPrelude.Equality
open import Level.Literals


open import ASCIIPrelude.ASCIIProofPrelude 
open NatProp
open import OwnPrelude.ASCIIPreludeProofs using (module CoverSumSameLevel; encodeMaybe)
open CoverSumSameLevel

open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Data.VarAsms
open import OwnPrelude.Data.BiThresholdVariables
open BiThresholds
open IncreaseAssignmentProperty

open ExistsSyntax

private
    variable
        -- n n' n'' n1 n2 n3 : Nat
        ST : Set _
        a b c d e f g h i j k l m n n' p q r s s' t u v w x x' y z fm i' j' k' l' A B C D E F G H K L M N O Q R S T V W X Y Z alg Ctx  : ST


-- \tagcode{Perhaps}

record Perhaps (A : Set i) : Set i where
    constructor PC
    coinductive
    field
        val? : A -+- Perhaps A

pattern val x = left x
pattern ctd x = right x
open Perhaps public

getVals : List (Perhaps A) -> List A
getVals = concatMap (fromSum [_] (const []) o val?)

getCtd : List (Perhaps A) -> List (Perhaps A)
getCtd = concatMap (fromSum (const []) [_] o val?) 

bisim : forall {ph ph' : Perhaps A} -> val? ph === val? ph' -> ph === ph'
val? (bisim eq i) = eq i

module _ {x : A} {a : Perhaps A} where
    valEq : val? a === val x -> a === PC (val x)
    valEq eq = bisim {ph = a} {ph' = PC (val x)} eq


module _ {a a' : Perhaps A} where
    ctdEq : val? a === ctd a' -> a === PC (ctd a')
    ctdEq eq = bisim {ph = a} {ph' = PC (ctd a')} eq

mapPerhaps : (A -> B) -> Perhaps A -> Perhaps B
val? (mapPerhaps f ph) with val? ph 
... | val x = val (f x)
... | ctd c = ctd (mapPerhaps f c)

mapDepPerhaps : ((a : A) -> B a) -> Perhaps A -> Perhaps (Sigma A B)
val? (mapDepPerhaps f ph) with val? ph 
... | val x = val (x , f x)
... | ctd c = ctd (mapDepPerhaps f c)

-- \tagcode{CoFoldPerhaps}

coFold : (A -> A -+- A) -> A -> Perhaps A
val? (coFold coalg a) with coalg a
... | val x  = val x
... | ctd a' = ctd (coFold coalg a')

joinPerhaps : Perhaps (Perhaps A) -> Perhaps A
val? (joinPerhaps pph) with val? pph 
... | ctd y = ctd (joinPerhaps y)
... | val ph with val? ph 
... | val x = val x
... | ctd y = ctd y

-- monad : Monad {i} Perhaps
-- monad .Monad.rawMonad .RawMonad.return = PC o val
-- monad .Monad.rawMonad .RawMonad._>>=_ pha phab = joinPerhaps (mapPerhaps phab pha)
-- monad .Monad.isMonad .IsMonad.left-identity {x} {f} = bisim eq
--     where
--         eq : val? (joinPerhaps (mapPerhaps f (PC (val x)))) === val? (f x)
--         eq with val? (f x)
--         ... | ctd y = refl
--         ... | val x = refl
-- monad .Monad.isMonad .IsMonad.right-identity {m} = eq {m = m}
--     where --basically unwrapping bisimilarity here
--         eq : forall {m} -> (joinPerhaps (mapPerhaps (PC o val) m)) === m
--         val? (eq {m} i) with val? m
--         ... | val x = val x
--         ... | ctd y = ctd (eq {m = y} i)
-- monad .Monad.isMonad .IsMonad.associative = {!   !} --TODO

extract : Nat -> Perhaps A -> Maybe A
extract 0 _      = nothing
extract (1+ n) p with val? p 
... | val  d = just d
... | ctd ph = extract n ph

noValue : Perhaps X 
val? noValue = ctd noValue

module _ {A : Set i} where
    eventually : (A -> Set j) -> Perhaps A -> Set (i ~U~ j)
    eventually P ph = exists[ n of Nat ] exists[ a of A ] ((extract n ph === just a) and P a)

    hasAnyVal : Perhaps A -> Set i
    hasAnyVal ph = exists[ n of Nat ] exists[ a of A ] (extract n ph === just a) -- eventually (\_ -> Unit {i})

    hasVal : A -> Perhaps A -> Set i
    hasVal a ph = exists[ n of Nat ] (extract n ph === just a) -- eventually (\_ -> Unit {i})

    _hasVal_at_ : Perhaps A -> A -> Nat -> Set i
    ph hasVal a at 0 = val? ph === val a
    ph hasVal a at (1+ n) = exists[ a' ] ((val? ph === ctd a') -x- (a' hasVal a at n))

    hasValPred : forall {a'} -> val? a === ctd a' -> hasAnyVal a -> hasAnyVal a'
    hasValPred {a} eq (n , x , eq') with val? a in eq-vala
    hasValPred {a} eq (n , x , eq') | val x' = absurd (encodeSum eq)
    hasValPred {a} eq (0 , x , eq') | ctd y  = absurd (encodeMaybe eq')
    hasValPred {a} {a'} eq (1+ n , x , eq') | ctd y  = n , x , \i -> coerce (\j -> extract (1+ n) (bisim {ph = a} {ph' = PC (ctd a')} (trans (propToPath eq-vala) eq) j) === just x) eq' i

    extract+1 : extract n a === just x -> extract (1+ n) a === just x
    extract+1 {0} {a = a} eq = absurd (encodeMaybe eq)
    extract+1 {1+ n} {a = a} {x = x} eq with val? a in eq-vala
    ... | val x = eq
    ... | ctd y = extract+1 {n = n} eq

    noValueNotHasValat : noValue hasVal x at n -> Zero {k}
    noValueNotHasValat {n = zero} nov = absurd (encodeSum nov)
    noValueNotHasValat {x} {n = 1+_ n} (a' , ctdNov=a' , a'hasVal) = noValueNotHasValat {n = n} (coerce (sym (encodeSum ctdNov=a') || _hasVal x at n) a'hasVal) 

    



module _ {A : Set i} where
    choose : Perhaps A -> Perhaps A -> Perhaps A
    val? (choose a b) with val? a 
    ... | val x  = val x 
    ... | ctd a' = ctd (choose b a')  

    chooseHasValSuc : choose a b hasVal x at n -> choose (PC (ctd a)) (PC (ctd b)) hasVal x at (1+ 1+ n)
    chooseHasValSuc {(a)} {(b)} {n = zero} eq with val? a in eq-vala
    ... | val x = choose (PC (ctd b)) a , refl , choose a b , refl , trans (\i -> val? (choose (bisim {ph = a} {ph' = PC (val x)} (propToPath eq-vala) i) b)) eq
    ... | ctd y = absurd (encodeSum eq)
    chooseHasValSuc {(a)} {(b)} {n = 1+ n} eq = choose (PC (ctd b)) a , refl , choose a b , refl , eq

    chooseVal : forall {n n' a b x y} -> a hasVal x at n -> b hasVal y at n' -> (choose a b hasVal x at (2 * min n n')) or (choose a b hasVal y at (1+ (2 * min n n')))
    chooseVal {n = zero} {(n')} {(a)} {(b)} a=x-at-n b=y-at-n' with val? a in eq-vala
    ... | val x = left a=x-at-n
    ... | ctd y = absurd (encodeSum a=x-at-n)
    chooseVal {n = 1+ n} {n' = zero } {(a)} {(b)} a=x-at-n b=y-at-n' with val? a in eq-vala | val? b in eq-valb
    ... | val xa | _ = absurd (encodeSum (fst (snd a=x-at-n)))
    ... | ctd a' | ctd b' = absurd (encodeSum b=y-at-n')
    ... | ctd a' | val xb = right (choose b a' , refl , trans (\i -> val? (choose (bisim {ph = b} {ph' = PC (val xb)} (propToPath eq-valb) i) a')) b=y-at-n') 
    chooseVal {n = 1+ n} {n' = 1+ n'} {(a)} {(b)} {x} {y} (a' , vala=ctda' , a=x-at-n) (b' , valb=ctdb' , b=y-at-n') = fromSum --this is the case where both values are a ctd
        (\even -> left 
            (coerce (\i -> choose a b hasVal x at ((right-step-+ {x = min n n'} {y = min n n' + zero} || 1+_) (~ i)) ) 
            (coerce (\i -> choose (bisim {ph = a} {ph' = PC (ctd a')} vala=ctda' (~ i)) (bisim {ph = b} {ph' = PC (ctd b')} valb=ctdb' (~ i)) hasVal x at (1+ 1+ (min n n' + (min n n' + zero)))) 
            (chooseHasValSuc even))))
        (\odd -> right (
            (coerce (\i -> choose a b hasVal y at (( (1+ (1+ (1+ (2 * min n n')))) =< (sym (right-step-+ {x = min n n'} {y = min n n' + zero}) || 1+_ o 1+_) > 1+ (2 * min (1+ n) (1+ n')) qed) i))  
            (coerce (\i -> choose (bisim {ph = a} {ph' = PC (ctd a')} vala=ctda' (~ i)) (bisim {ph = b} {ph' = PC (ctd b')} valb=ctdb' (~ i)) hasVal y at (1+ 1+ 1+ (2 * min n n')))
            (chooseHasValSuc odd)))) ) 
        (chooseVal {n = n} {n' = n'} {x = x} {y = y} (a=x-at-n) (b=y-at-n'))

-- \tagcode{PerhapsSLState}

record IsPerhapsSLState {S : Set i} (sl : Semilattice S) {X : Set j} (delta : S -> S) (read : S -> VarAsm X) : Set (i ~U~ j) where
    open Semilattice sl
    field 
        delta-dir : forall {s} -> s P delta s
        delta-pres-P : forall {s} {s'} -> s P s' -> delta s P delta s'
        read-threshold : IsBiThresholdRead (Semilattice.isPreOrder sl) read

        -- constraining delta to preserve <> completely is too strict because that would mean that we could not derive information from a conjunction of two values
        -- delta-pres : forall {s s'} -> delta (s <> s') === delta s <> delta s'

record PerhapsSLState (S : Set i) (sl : Semilattice S) {X : Set j} (read : S -> VarAsm X) : Set (i ~U~ j) where
    open Semilattice sl
    field
        delta : S -> S

        isPerhapsSLState : IsPerhapsSLState sl delta read
    open IsPerhapsSLState isPerhapsSLState public

    -- definition has issue. Value that once existed might become a conflict later...could maybe be fixed using two variables?
    toPerhaps : S -> Perhaps X
    val? (toPerhaps s) with read s
    ... | unassigned = ctd (toPerhaps (delta s))
    ... | asm x      = val x
    ... | conflict   = val? noValue

    extractAsm : Nat -> S -> VarAsm X
    extractAsm 0      s = read s
    extractAsm (1+ n) s = extractAsm n (delta s)

    --note: a more efficient implementation, stopping after a value is found or conflict is reached does not form a threshold read
    --because we loose the information on how it would operate on larger values in the recursion
    --especially stopping on asm value has this behaviour, because continuing to run it could form a conflict, but running it on a larger
    --start value could just yield another value. Stopping on conflict might be fine, but left out for brevity

    extractAsm-asm-inc : forall {s s' n x} -> s P s' -> extractAsm n s === asm x -> (extractAsm n s' === asm x) or (extractAsm n s' === conflict)
    extractAsm-asm-inc {s} {s'} {n = 0} sPs' eq = asm-asm-+-conf (coerce (\i -> eq i =incAsm= read s') (read-threshold _ _ sPs'))
    extractAsm-asm-inc {n = 1+ n}       sPs' eq = extractAsm-asm-inc {n = n} (delta-pres-P sPs') eq

    extractAsm-conf-conf : forall {s s' n} -> s P s' -> extractAsm n s === conflict -> extractAsm n s' === conflict
    extractAsm-conf-conf {(s)} {(s')} {n = 0}    sPs' eq = asm-stays-conf (coerce (\i -> eq i =incAsm= read s') (read-threshold _ _ sPs'))
    extractAsm-conf-conf {(s)} {(s')} {n = 1+ n} sPs' eq = extractAsm-conf-conf {n = n} (delta-pres-P sPs') eq

    extractAsmIsBiThresholdRead : forall {n} -> IsBiThresholdRead (Semilattice.isPreOrder sl) (extractAsm n)
    extractAsmIsBiThresholdRead {n} s s' sPs' with extractAsm n s in eq-ext
    ... | unassigned = unas-to-anything refl
    ... | conflict   = conf-conf refl (extractAsm-conf-conf {n = n} sPs' (propToPath eq-ext))
    ... | asm x      with extractAsm-asm-inc {n = n} sPs' (propToPath eq-ext)
    ... | left  eq = asm-eq refl eq
    ... | right eq = asm-conf refl eq

    extractAsm-asm-read : read s === asm x -> (extractAsm n s === asm x) or (extractAsm n s === conflict)
    extractAsm-asm-read {n = 0} eq = left eq
    extractAsm-asm-read {s} {n = 1+ n} eq with extractAsm-asm-read {n = n} eq
    ... | right y = right (extractAsm-conf-conf {s = s} {n = n} delta-dir y)
    ... | left  x = extractAsm-asm-inc {s = s} {n = n} delta-dir x

    extractAsm-conflict-read : read s === conflict -> extractAsm n s === conflict
    extractAsm-conflict-read {n = 0} eq = eq
    extractAsm-conflict-read {n = 1+ n} eq = extractAsm-conf-conf {n = n} delta-dir (extractAsm-conflict-read {n = n} eq)

    hasFirstAsmValue_at_on_ : X -> Nat -> S -> Set j
    hasFirstAsmValue x at 0 on s = extractAsm 0 s === asm x
    hasFirstAsmValue x at (1+ n) on s = (extractAsm n s === unassigned) and (extractAsm (1+ n) s === asm x)

    firstValPred : hasFirstAsmValue x at (1+ n) on s -> hasFirstAsmValue x at n on delta s
    firstValPred {n = zero} (exns=unas , exnds=asm) = exnds=asm
    firstValPred {n = 1+_ n} (exns=unas , exnds=asm) = exns=unas , exnds=asm

    firstValSucc : (read s === unassigned) -> hasFirstAsmValue x at n on (delta s) -> hasFirstAsmValue x at (1+ n) on s
    firstValSucc {n = zero} reads=unas hasV = reads=unas , hasV
    firstValSucc {n = 1+_ n} reads=unas hasV = hasV

    firstVal=>Perhaps : hasFirstAsmValue x at n on s -> toPerhaps s hasVal x at n
    firstVal=>Perhaps {(x)} {(zero)} {(s)} hasV with read s
    ... | unassigned = absurd (encodeVarAsm hasV)
    ... | asm x1     = encodeVarAsm hasV || val
    ... | conflict   = absurd (encodeVarAsm hasV)
    firstVal=>Perhaps {(x)} {1+ n} {(s)} (exns=unas , exnds=asm) with read s in eq-reads
    ... | unassigned = toPerhaps (delta s) , refl , firstVal=>Perhaps (firstValPred (exns=unas , exnds=asm))
    ... | conflict = absurd (encodeVarAsm (trans (sym exns=unas) (extractAsm-conflict-read {n = n} (propToPath eq-reads))))
    ... | asm x1 with extractAsm-asm-read {n = n} (propToPath eq-reads)
    ... | left x2 = absurd (encodeVarAsm (trans (sym x2) exns=unas))
    ... | right y = absurd (encodeVarAsm (trans (sym y) exns=unas))

    toPerhaps-conflict-read-noValue : read s === conflict -> toPerhaps s hasVal x at n -> Zero {k}
    toPerhaps-conflict-read-noValue {s} {n = zero} eq hasV with read s 
    ... | unassigned = absurd (encodeSum hasV)
    ... | asm x      = absurd (encodeVarAsm eq)
    ... | conflict   = absurd (encodeSum hasV)
    toPerhaps-conflict-read-noValue {s} {n = 1+_ n} eq hasV with read s 
    ... | unassigned = absurd (encodeVarAsm eq)
    ... | asm x      = absurd (encodeVarAsm eq)
    toPerhaps-conflict-read-noValue {(s)} {x} {1+_ n} eq (a' , ctdNov=a' , a'hasVal) | conflict = noValueNotHasValat (coerce (sym (encodeSum ctdNov=a') || _hasVal x at n) a'hasVal)

    toPerhaps-asm-read : read s === asm x -> val? (toPerhaps s) === val x
    toPerhaps-asm-read {s} eq with read s
    ... | unassigned = absurd (encodeVarAsm eq)
    ... | asm x      = encodeVarAsm eq || val
    ... | conflict   = absurd (encodeVarAsm eq)

    toPerhaps-unassigned-read : read s === unassigned -> val? (toPerhaps s) === ctd (toPerhaps (delta s))
    toPerhaps-unassigned-read {s} eq with read s
    ... | unassigned = refl
    ... | asm x      = absurd (encodeVarAsm eq)
    ... | conflict   = absurd (encodeVarAsm eq)

    toPerhaps-conflict-read : read s === conflict -> val? (toPerhaps s) === ctd noValue
    toPerhaps-conflict-read {s} eq with read s
    ... | unassigned = absurd (encodeVarAsm eq)
    ... | asm x      = absurd (encodeVarAsm eq)
    ... | conflict   = refl

    Perhaps=>firstVal : toPerhaps s hasVal x at n -> hasFirstAsmValue x at n on s
    Perhaps=>firstVal {(s)} {(x)} {(zero)} hasV with read s
    ... | unassigned = absurd (encodeSum hasV)
    ... | asm x1     = encodeSum hasV || asm
    ... | conflict   = absurd (encodeSum hasV)
    Perhaps=>firstVal {(s)} {(x)} {1+ n} hasV with read s in eq-reads
    ... | asm x1     = absurd (encodeSum ((fst o snd) hasV))
    Perhaps=>firstVal {(s)} {(x)} {1+_ n} (a' , ctdNov=a' , a'hasVal) | unassigned = firstValSucc {n = n} (propToPath eq-reads) $ Perhaps=>firstVal {n = n} (coerce (sym (encodeSum ctdNov=a') || _hasVal x at n) a'hasVal)
    Perhaps=>firstVal {(s)} {(x)} {1+_ n} (a' , ctdNov=a' , a'hasVal) | conflict = absurd {j = lzero} (noValueNotHasValat (coerce (sym (encodeSum ctdNov=a') || _hasVal x at n) a'hasVal))

    -- \tagcode{speedupTheorem}

    speedup : forall {n n' s s' x} -> hasFirstAsmValue x at n on s -> hasFirstAsmValue x at n' on s' -> s P s' -> n' leq n
    speedup {n = 0} {n' = 0}     hasVn hasVn' sPs' = leq-refl
    speedup {n = 0} {n' = 1+ n'} {s} {s'} hasVn (exn's'=unas , exn'ds'=asm) sPs' with extractAsm-asm-inc {n = 0} sPs' hasVn
    ... | right y = absurd (encodeVarAsm (trans (sym exn's'=unas) (extractAsm-conflict-read {n = n'} y))) 
    ... | left  x with extractAsm-asm-read {n = n'} x 
    ... | left x1 = absurd (encodeVarAsm (trans (sym x1) exn's'=unas))
    ... | right y = absurd (encodeVarAsm (trans (sym y) exn's'=unas))
    speedup {n = 1+_ n} {n' = 0}     hasVn hasVn' sPs' = leq-zero
    speedup {n = 1+_ n} {n' = 1+ n'} hasVn hasVn' sPs' = leq-suc (speedup {n = n} {n' = n'} (firstValPred hasVn) (firstValPred hasVn') (delta-pres-P sPs')) 

    -- obvious that we at least use the same time, but we might choose less. this proof is basically just refl
    -- speedup : hasAsmValue x after n on s -> hasAsmValue x after n on s' -> s P s' -> exists[ n' ] (n leq n' and hasAsmValue x after n' on s')
    -- speedup {n} hasVons hasVons' sPs' with extractAsm-asm-inc {n = n} sPs' hasVons
    -- ... | left  x = n , leq-refl , x
    -- ... | right y = n , leq-refl , hasVons'

    -- this does not work because the toPerhaps structure might not have a value when started on a bigger value, regardless of whether it had 
    -- one before
    -- speedup : toPerhaps s hasVal x at n -> s P s' -> exists[ n' ] (n leq n' and toPerhaps s' hasVal x at n')

module _ {S : Set i} {sl : Semilattice S} {X : Set j} {read : S -> VarAsm X} where
    open PerhapsSLState
    open IsPerhapsSLState
    open Semilattice sl
    
    merge : PerhapsSLState S sl read -> PerhapsSLState S sl read -> PerhapsSLState S sl read
    delta (merge p1 p2)        s = delta p1 s <> delta p2 s               
    delta-dir (isPerhapsSLState (merge p1 p2))     {s} = mergeP' (delta-dir p1) (delta-dir p2)
    delta-pres-P (isPerhapsSLState (merge p1 p2)) {s} {s'} sPs' = 
        ((delta p1 s <> delta p2 s) <> delta p1 s' <> delta p2 s') =< associative >
        ((delta p1 s <> delta p2 s) <> delta p1 s') <> delta p2 s' =< sym associative || _<> delta p2 s' >
        (delta p1 s <> delta p2 s <> delta p1 s') <> delta p2 s' =< commutative || (\h -> (delta p1 s <> h) <> delta p2 s') > 
        ((delta p1 s <> (delta p1 s' <> delta p2 s)) <> delta p2 s') =< associative || _<> delta p2 s' >
        ((delta p1 s <> delta p1 s') <> delta p2 s) <> delta p2 s' =< sym associative >
        (delta p1 s <> delta p1 s') <> (delta p2 s <> delta p2 s') =< (\i -> delta-pres-P p1 sPs' i <> delta-pres-P p2 sPs' i) >
        (delta p1 s' <> delta p2 s') qed
    read-threshold (isPerhapsSLState (merge p1 p2))    = read-threshold p1    
    