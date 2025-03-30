{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Data.Containers where

open import ASCIIPrelude.ASCIIPrelude 
open NatOp renaming (_leq_ to _leqb_)
open PolyUnit
open PolyZero
open PolyFin
open import ASCIIPrelude.ASCIIProofPrelude
open NatProp 
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Relation.Functions

open ExistsSyntax

private
    variable
        k l : Level
        n n' n'' n1 n2 n3 : Nat
        ST : Set k
        A B C D X Y Z : ST
        a b c w x y z fx T mes g f p q fa fv h alg i j i' j' fC : ST
        M F G : Set i -> Set j

-- \tagcode{Containers}

record Container i j : Set (lsuc i ~U~ lsuc j) where
    constructor _|>_
    field
        S : Set i
        P : S -> Set j
    [[_]] : Set k -> Set (i ~U~ j ~U~ k)
    [[_]] R = exists[ s of S ] (P s -> R)

-- [[_]] : Container i j -> Set k -> Set (i ~U~ j ~U~ k)
-- [[ S |> P ]] R = exists[ s of S ] (P s -> R)

module ContainerOps where
    open Container

    map : (A -> B) -> [[ C ]] A -> [[ C ]] B 
    map f (s , p) = s , f o p

    mapPi : ((a : A) -> B a) -> [[ C ]] A -> [[ C ]] (Sigma A B)
    mapPi f (s , p) = s , \p' -> p p' , f (p p')


module ContainerCategorical where
    open Container
    open ContainerOps
    
    containerFunctor : Functor {i} [[ C ]]
    containerFunctor .Functor.rawFunctor .RawFunctor._<$>_ = map
    containerFunctor .Functor.isFunctor .IsFunctor.fmap-id = extens \{(s , p) -> 
        map id (s , p) =<>
        (s , p o id )  =<>
        (s , p)        qed}
    containerFunctor .Functor.isFunctor .IsFunctor.fmap-comp {f} {g} = extens \{(s , p) -> 
        map (f o g) (s , p)     =<>
        (s , f o g o p)         =<>
        (map f o map g) (s , p) qed}

module ContainerClosures where
    open Container 
    
    ZeroC : Container i j
    ZeroC = Zero |> \()

    KC : Set i -> Container i j
    KC X = X |> (\_ -> Zero)

    kc : (x : X) -> [[ KC {j = j} X ]] A
    kc x = x , \()

    kd : [[ KC {j = j} X ]] A -> X
    kd (x , p) = x

    kc-eq-prop : {kx ky : [[ KC {j = j} X ]] A} -> kd kx === kd ky -> kx === ky
    kc-eq-prop {kx = sx , px} {ky = sy , py} kdeq = 
        (sx , px) =< kdeq || _, px >
        (sy , px) =< extens (\()) || sy ,_ >
        (sy , py) qed

    container-kc-interp : {X : Set i} {A : Set i} -> [[ KC {j = i} X ]] A === X
    container-kc-interp = Iso->=== (record { 
        to = kd ; 
        from = kc ; 
        isIsomorphism = record { 
            to-o-from=id = refl ; 
            from-o-to=id = extens (\{(x , p) -> (extens \()) || x ,_}) } })

    UnitC : Container i j
    UnitC = KC Unit

    unitc : [[ UnitC {i} {j} ]] A
    unitc = kc unit

    IC : Container i j
    IC = Unit |> (\_ -> Unit)

    ic : A -> [[ IC {i} {j} ]] A
    ic a = unit , \_ -> a

    idd : [[ IC {i} {j} ]] A -> A
    idd (s , p) = p unit

    container-ic-interp : {A : Set i} -> [[ IC {i} {i} ]] A === A
    container-ic-interp = Iso->=== (record { 
        to = idd ; 
        from = ic ; 
        isIsomorphism = record { 
            to-o-from=id = refl ; 
            from-o-to=id = refl } })

    infixr 21 _:x:_
    _:x:_ : Container i j -> Container i' j' -> Container (i ~U~ i') (j ~U~ j')
    (S1 |> P1) :x: (S2 |> P2) = (S1 -x- S2) |> \{(s1 , s2) -> P1 s1 or P2 s2}

    _:,:_ : [[ C ]] A -> [[ D ]] A -> [[ C :x: D ]] A
    (sc , pc) :,: (sd , pd) = (sc , sd) , fromSum pc pd

    prodd : [[ C :x: D ]] A -> [[ C ]] A -x- [[ D ]] A
    prodd ((sc , sd) , p) = (sc , p o left) , (sd , p o right)

    container-prod-interp : [[ C :x: D ]] A === [[ C ]] A -x- [[ D ]] A
    container-prod-interp = Iso->=== (record { 
        to = prodd ; 
        from = uncurry _:,:_ ; 
        isIsomorphism = record { 
            to-o-from=id = refl ; 
            from-o-to=id = extens \{((sc , sd) , p) -> 
                (sc , sd) , fromSum (p o left) (p o right) =< (extens 
                    \{(left x) -> refl
                    ; (right y) -> refl}) || (sc , sd) ,_ >
                ((sc , sd) , p) qed} } })

    infixr 20 _:+:_
    _:+:_ : Container i j -> Container i' j -> Container (i ~U~ i') j
    (S1 |> P1) :+: (S2 |> P2) = (S1 -+- S2) |> fromSum P1 P2

    leftc : [[ C ]] A -> [[ C :+: D ]] A
    leftc (s , p) = (left s) , p

    rightc : [[ D ]] A -> [[ C :+: D ]] A
    rightc (s , p) = (right s) , p

    sumd : [[ C :+: D ]] A -> [[ C ]] A or [[ D ]] A
    sumd (left  x , p) = left  (x , p)
    sumd (right y , p) = right (y , p)

    container-sum-interp : [[ C :+: D ]] A === [[ C ]] A -+- [[ D ]] A
    container-sum-interp = Iso->=== (record { 
        to = sumd ; 
        from = fromSum leftc rightc ; 
        isIsomorphism = record { 
            to-o-from=id = extens \{(left x) -> refl
                                  ; (right y) -> refl} ; 
            from-o-to=id = extensPi \{ (left x , p) -> refl
                                     ; (right y , p) -> refl} } })

    PiC : (A : Set k) -> (A -> Container i j) -> Container (k ~U~ i) (k ~U~ j)
    PiC A fC = ((a : A) -> S (fC a)) |> \f -> exists[ a of A ] P (fC a) (f a)

    pic : ((a : A) -> [[ fC a ]] B) -> [[ PiC A fC ]] B
    pic f = fst o f , \{(a , p) -> snd (f a) p}

    pid : [[ PiC A fC ]] B -> ((a : A) -> [[ fC a ]] B)
    pid (s , p) x = s x , p o (x ,_)


    module _ {A : Set k} {fC : A -> Container i j} where
        container-pi-interp : [[ PiC A fC ]] B === ((a : A) -> [[ fC a ]] B)
        container-pi-interp = Iso->=== (record { 
            to = pid ; 
            from = pic ; 
            isIsomorphism = record { 
                to-o-from=id = refl ; 
                from-o-to=id = refl } })

    SigC : (A : Set k) -> (A -> Container i j) -> Container (k ~U~ i) j
    SigC A fC = (Sigma A (S o fC)) |> \{(a , s) -> P (fC a) s}

    sigc : Sigma A (\a -> [[ fC a ]] B) -> [[ SigC A fC ]] B
    sigc (a , (s , p)) = (a , s) , p

    sigd : [[ SigC A fC ]] B -> Sigma A (\a -> [[ fC a ]] B)
    sigd ((x , s) , p) = x , (s , p)
    
    module _ {A : Set k} {fC : A -> Container i j} where
        container-sig-interp : [[ SigC A fC ]] B === (exists[ a of A ] [[ fC a ]] B)
        container-sig-interp = Iso->=== (record { 
            to = sigd ; 
            from = sigc ; 
            isIsomorphism = record { 
                to-o-from=id = refl ; 
                from-o-to=id = refl } })

    _:o:_ : Container i j -> Container i' j' -> Container (i ~U~ i' ~U~ j) (j ~U~ j')
    (S1 |> P1) :o: C2 = SigC S1 \s -> PiC (P1 s) \p -> C2

    compc : ([[ C ]] o [[ D ]]) A -> [[ C :o: D ]] A
    compc (s , f) = (s , fst o f) , \{(pcs , g) -> snd (f pcs) g}

    compd : [[ C :o: D ]] A -> ([[ C ]] o [[ D ]]) A
    compd ((s , f) , g) = s , \pcs -> f pcs , \pdfpcs -> g (pcs , pdfpcs)

    module _ {C : Container i j} {D : Container i' j'} {A : Set k} where
        container-comp-interp : [[ C :o: D ]] A === ([[ C ]] o [[ D ]]) A
        container-comp-interp = 
            [[ C :o: D ]] A =<>
            (exists[ s' of exists[ s of S C ] (P C s -> S D) ] ((exists[ p of P C (fst s') ] P D (snd s' p)) -> A)) =< Iso->=== (record { 
                to = compd ; 
                from = compc ; 
                isIsomorphism = record { 
                    to-o-from=id = refl ; 
                    from-o-to=id = refl } }) >
            (exists[ s  of S C ] (P C s -> exists[ s' of S D ] (P D s' -> A)) ) =<>
            ([[ C ]] o [[ D ]]) A qed

        
module RecursiveFixpoints where
    open Container
    open ContainerOps
    
    data W (C : Container i j) : Set (i ~U~ j) where
        In : [[ C ]] (W C) -> W C
    
    Out : W C -> [[ C ]] (W C)
    Out (In f) = f

    module _ {C : Container i j} {A : Set k} where
        foldC : ([[ C ]] A -> A) -> W C -> A
        -- foldC alg (In f) = alg (map (foldC alg) f)
        foldC alg (In (s , p)) = alg (s , foldC alg o p) 
        -- foldC alg o In === alg o map (foldC alg)

        foldC-pointless : foldC alg === alg o map (foldC alg) o Out
        foldC-pointless = extens \{(In f) -> refl}

        _^f_ : (X -> X) -> Nat -> (X -> X)
        (f ^f 0)      x = x
        (f ^f (1+ n)) x = f ((f ^f n) x)

        -- \tagcode{FoldExchangeAlg}

        foldCN : (n : Nat) -> ([[ C ]] A -> A) -> W C -> (([[ C ]] A -> A) -> A)
        foldCN 0      alg (In (s , p)) alg' = foldC alg' (In (s , p))
        foldCN (1+ n) alg (In (s , p)) alg' = alg (s , (\w -> foldCN n alg w alg') o p)

        foldCN-foldC : foldCN n alg w alg === foldC alg w
        foldCN-foldC {n = 0}    {w = In x} = refl
        foldCN-foldC {n = 1+ n} {alg = alg} {w = In (s , p)} = (\_ -> foldCN-foldC {n = n}) |f (\h -> alg (s , h))

    module _ {C : Container i j} {A : W C -> Set k} where
        foldPi : ((c : [[ C ]] (Sigma (W C) A)) -> A (In (map fst c))) -> (w : W C) -> A w
        foldPi alg (In (s , p)) = alg (s , \p' -> p p' , foldPi alg (p p'))

        foldPiN : (n : Nat) -> 
            ((c : [[ C ]] (Sigma (W C) A)) -> A (In (map fst c))) -> 
            (w : W C) -> 
            ((c : [[ C ]] (Sigma (W C) A)) -> A (In (map fst c))) -> A w
        foldPiN 0      alg w            alg' = foldPi alg' w
        foldPiN (1+ n) alg (In (s , p)) alg' = alg (s , \p' -> p p' , foldPiN n alg (p p') alg')

        foldPiN-foldPi : foldPiN n alg w alg === foldPi alg w
        foldPiN-foldPi {0} = refl
        foldPiN-foldPi {1+ n} {alg = alg} {w = In (s , p)} = (\_ -> foldPiN-foldPi {n = n}) |pi (\h -> alg (s , \p' -> p p' , h p'))


module CorecursiveFixpoints where
    open Container
    open ContainerOps
    record CoW (C : Container i j) : Set (i ~U~ j) where
        coinductive
        constructor In
        field
            Out : [[ C ]] (CoW C)
    open CoW

    cofold : (A -> [[ C ]] A) -> A -> CoW C
    -- cofold coAlg seed = < map (cofold coAlg) (coAlg seed) >co
    Out (cofold coAlg seed) with coAlg seed
    ... | (s , p) = s , (cofold coAlg o p)

    record CouldBe (A : Set i) : Set i where
        coinductive
        constructor couldBe
        field
            Is? : A or CouldBe A
    open CouldBe

    -- fold : ([[ C ]] (CouldBe A) -> CouldBe A) -> CoW C -> CouldBe A
    -- -- Is? (fold alg cowc) = Is? (alg (map (fold alg) (Out cowc)))
    -- fold alg cowc = {!  !}
    
     -- TODO: this is a longer chapter 


record ShapelyContainer (C : Container i j) : Set (i ~U~ j) where
    constructor SC
    open Container C
    open Finite
    field
        finP : forall (s : S) -> Finite (P s)

    vectorContainer : Container i j
    vectorContainer = S |> (Fin {j} o num o finP)

    vecContainerEq : C === vectorContainer
    vecContainerEq = (extens (finiteToEq o finP)) || S |>_

-- important: Those are NOT the containers for finite data types! Finite containers can still be recursive, but just don't contain functions with infinite input types in constructors.
-- Similar to shapely containers created by Jay and Cockett, but they do not require finite shapes
record FiniteContainer (C : Container i j) : Set (i ~U~ j) where
    open Container C
    field
        finS : Finite S
        shapely : ShapelyContainer C
    open ShapelyContainer shapely public


