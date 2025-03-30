{-# OPTIONS --cubical --guardedness --no-postfix --hidden-argument-puns #-}
module Preliminaries.Preliminaries where

open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _~U~_; lift to liftL; Lift to LiftL; Setω to Setw) public

private
    variable
        ST : Set _
        a b c d e f g h i j k l m n n' p q r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z : ST

open import OwnPrelude.Equality

-- \tagcode{PreliminariesPtI}

-- record Monoid {i : Level} : Set (lsuc i) where
--     field
--         A : Set i
--         epsilon : A
--         _`$\oplus$`_ : A -> A -> A

--         associative    : forall a b c -> a `$\oplus$` (b `$\oplus$` c) === (a `$\oplus$` b) `$\oplus$` c
--         left-identity  : forall a     -> epsilon `$\oplus$` a === a
--         right-identity : forall a     -> a `$\oplus$` epsilon === a

record Monoid {i : Level} (A : Set i) : Set i where
    field
        epsilon : A
        _`$\oplus$`_ : A -> A -> A

        associative    : forall a b c -> a `$\oplus$` (b `$\oplus$` c) === (a `$\oplus$` b) `$\oplus$` c
        left-identity  : forall a     -> epsilon `$\oplus$` a === a
        right-identity : forall a     -> a `$\oplus$` epsilon === a

id : {A : Set i} -> A -> A
id a = a

-- id : {A : Set i} -> A -> A
-- id = \a -> a

apply : (A -> B) -> A -> B
apply f a = f a

-- func : (a : A)(b : B) -> C
-- func = {!!}


data Bool : Set where
    true  : Bool
    false : Bool

not``Bool : Bool -> Bool
not``Bool true  = false 
not``Bool false = true


infixr 10 _::'_ 
data List``Bool : Set where
    []' : List``Bool
    _::'_ : Bool -> List``Bool -> List``Bool

concat2``Bool : List``Bool -> List``Bool -> List``Bool
concat2``Bool []' ys = ys
concat2``Bool (x ::' xs) ys = x  ::' (concat2``Bool xs ys)

concat2BoolTest = concat2``Bool (true ::' []') (false ::' true ::' []')


infixr 10 _::_ 
data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

concat2 : forall {A} -> List A -> List A -> List A
concat2 [] ys = ys
concat2 (x :: xs) ys = x  :: (concat2 xs ys)

_and``Bool_ : Bool -> Bool -> Bool
true and``Bool true = true
_    and``Bool _    = false


_or``Bool_ : Bool -> Bool -> Bool
false or``Bool false = false
_     or``Bool _     = true

-- _and``Bool_ : Bool -> Bool -> Bool
-- _and``Bool_ = \{ true true -> true
--               ;  _    _    -> false }


if_then_else_ : Bool -> A -> A -> A
if true  then y else n = y 
if false then y else n = n

_o_ : (B -> C) -> (A -> B) -> A -> C
(f o g) a = f (g a)

-- f' : {A B C : Set} -> A -> B -> C
-- f' a b = {!!}



-- data Nat : Set where
--     zero : Nat
--     1+_  : Nat -> Nat

-- {-# BUILTIN NATURAL Nat #-}

open import Data.Nat renaming (ℕ to Nat ; suc to 1+_) hiding (_+_ ; _*_)

infixr 20 _+_
_+_ : Nat -> Nat -> Nat
0      + y = y 
(1+ x) + y = 1+ (x + y)

{-# TERMINATING #-}
f' : A
f' = f'

bpred : Nat -> Nat
bpred zero   = zero 
bpred (1+ n) = n

{-# TERMINATING #-}
until0 : Nat -> Nat
until0 zero = zero
until0 (1+ n) = until0 (bpred (1+ n))

2nd``Nat : {a : Nat} {b : Nat} -> Nat
2nd``Nat {a} {b} = b

2nd``Nat-test : Nat -> Nat -> Nat
2nd``Nat-test a b = 2nd``Nat {a = a} {b = b}

_*``Nat_ : Nat -> Nat -> Nat
zero *``Nat y = zero
(1+ x) *``Nat y = (1+ x) + (x *``Nat y)

record Num (A : Set) : Set where
    field
        _*_ : A -> A -> A

instance
    num``Bool : Num Bool 
    num``Bool = record { _*_ = _and``Bool_ }

    num``Nat : Num Nat 
    num``Nat = record { _*_ = _*``Nat_ }

open Num {{...}}

square``Bool : Bool -> Bool
square``Bool x = x * x

square``Nat : Nat -> Nat
square``Nat x = x * x

squareNum : {{Num X}} -> X -> X
squareNum x = x * x


module M1 where
    a1 : Nat
    a1 = 5

module M2 where
    open M1
    a2 = a1
open M2

module M (A : Set) where
    f2 : A -> A
    f2 a = a

open M Nat

record Vec3 : Set where
    constructor <_,_,_>
    field
        valx : Nat
        valy : Nat
        valz : Nat

module _ where
    open Vec3

    addVecEntries : Vec3 -> Nat
    addVecEntries v = valx v + valy v + valz v

addVecEntries' : Vec3 -> Nat
addVecEntries' v = valx + valy + valz
    where open Vec3 v

vec1 : Vec3
vec1 = record { valx = 0 ; valy = 1 ; valz = 2 }

module _ where
    open Vec3
        
    vec2 : Vec3
    valx vec2 = 0
    valy vec2 = 1
    valz vec2 = 2

vec3 : Vec3
vec3 = < 0 , 1 , 2 >


record Stream (A : Set) : Set where
    coinductive
    field
        elem : A
        next : Stream A 

module _ where
    open Stream
    
    repeat : A -> Stream A
    elem (repeat a) = a
    next (repeat a) = repeat a

    prepend : A -> Stream A -> Stream A
    elem (prepend a s) = a
    next (prepend a s) = s

    -- repeat' : A -> Stream A
    -- repeat' a = prepend a (repeat' a)

    map : (A -> B) -> Stream A -> Stream B
    elem (map f s) = f (elem s)
    next (map f s) = map f (next s)

    interleave : Stream A -> Stream A -> Stream A
    elem (interleave a b) = elem a 
    next (interleave a b) = interleave b a

B' : Bool -> Set
B' true  = Bool 
B' false = Nat

f3 : (b : Bool) -> B' b
f3 true  = true 
f3 false = 1


data _===P_ {A : Set i} (a : A) : A -> Set i where
    reflP : a ===P a

1is1 : 1 === 1
1is1 = refl

1+1is2 : 1 + 1 === 2
1+1is2 = refl

symP : a ===P b -> b ===P a
symP reflP = reflP

transP : a ===P b -> b ===P c -> a ===P c
transP reflP reflP = reflP

congPP : a ===P b -> (f : A -> B) -> f a ===P f b
congPP reflP _ = reflP

_||PP_ = congPP

n+0isn : forall n -> (n + 0) ===P n
n+0isn 0      = reflP
n+0isn (1+ n) = n+0isn n ||PP 1+_


data Vec (A : Set i) : Nat -> Set i where
    []   : Vec A 0
    _::_ : A -> Vec A n -> Vec A (1+ n)


data Vec' (A : Set) (n : Nat) : Set where
    []   : n === 0 -> Vec' A n
    _::_ : A -> Vec' A n' -> 1+ n' === n -> Vec' A n


data Unit {i} : Set i where
    unit : Unit {i}


data Zero {i} : Set i where

absurd : Zero {i} -> A
absurd ()

module _ {i} where
    ¬_ : Set i -> Set i
    ¬ A = A -> Zero {i}

-- prove-by-contra : ¬ (¬ A) -> A
-- prove-by-contra ¬¬A = {!!}

-- data _-x-_ (A : Set i) (B : Set j) : Set (i ~U~ j) where
--     _,_ : A -> B -> A -x- B

record _-x-_ (A : Set i) (B : Set j) : Set (i ~U~ j) where
    constructor _,_
    field
        fst : A
        snd : B

data _-+-_ (A : Set i) (B : Set j) : Set (i ~U~ j) where
    left  : A -> A -+- B
    right : B -> A -+- B

fromSum : (A -> C) -> (B -> C) -> A -+- B -> C
fromSum fa fb (left  a) = fa a
fromSum fa fb (right b) = fb b

record Pi (A : Set i) (B : A -> Set j) : Set (i ~U~ j) where
    constructor lam
    field
        app : (a : A) -> B a

open Pi

_$_ : Pi A B -> (a : A) -> B a
f $ a = (app f) a

module _ {i} where
    _-xx-_ : (A : Set i) -> (B : Set i) -> Set i
    A -xx- B = (c : Bool) -> if c then A else B

    -- does not work for dependent tuples
    -- _-xx-_ : (A : Set i) -> (B : A -> Set i) -> Set i
    -- A -xx- B =  (a : A) -> (b : Bool) -> choose a b
    --     where
    --         choose : A -> Bool -> Set i
    --         choose a true  = A
    --         choose a false = {!   !}

_,,_ : A -> B -> A -xx- B
(a ,, b) true  = a
(a ,, b) false = b

record Sigma (A : Set i) (B : A -> Set j) : Set (i ~U~ j) where
    constructor _,_
    field
        fst : A
        snd : B fst

exists : {A : Set i} -> (B : A -> Set j) -> Set (i ~U~ j)
exists {A = A} = Sigma A


syntax exists (\a -> B) = exists[ a ] B
syntax Sigma A (\a -> B) = exists[ a of A ] B

module _ {i} where
    _-++-_ : (A : Set i) -> (B : Set i) -> Set i
    A -++- B = Sigma Bool \c -> if c then A else B

left' : A -> A -++- B
left' a = (true , a)


right' : B -> A -++- B
right' b = (false , b)

module _ {A : Set i} where

    revSig = Sigma

    syntax revSig A B = B proven-over A

    ex0 : (\n -> n === 0) proven-over Nat
    ex0 = 0 , refl

pattern fstConstr x = left x
pattern sndConstr x = right (left x)  
pattern thdConstr x = right (right x)  

Bool' : Set
Bool' = Unit -+- Unit

Fin' : Nat -> Set
Fin' 0      = Zero
Fin' (1+ n) = Fin' n -+- Unit

Vec'' : (A : Set i) -> Nat -> Set i
Vec'' A 0      = Unit
Vec'' A (1+ n) = A -x- Vec'' A n

-- Nat' : Set
-- Nat' = Unit -+- Nat'

_o'_ : forall {A : Set a} {B : A -> Set b} {C : {x : A} -> B x -> Set c} ->
    (forall {x} (y : B x) -> C y) -> (g : (x : A) -> B x) ->
    ((x : A) -> C (g x))
(f o' g) x = f (g x)

_$'_ : forall {A : Set} {B : A -> Set} ->
    ((x : A) -> B x) -> ((x : A) -> B x)
f $' x = f x

data Maybe (A : Set i) : Set i where
    nothing : Maybe A
    just    : A -> Maybe A

map' : (A -> B) -> List A -> List B
map' f []        = []
map' f (x :: xs) = f x :: map' f xs

maybeToList : Maybe A -> List A
maybeToList nothing  = []
maybeToList (just x) = x :: []

mapMaybe : (A -> Maybe B) -> List A -> List B
mapMaybe p []       = []
mapMaybe p (x :: xs) with p x
... | just y  = y :: mapMaybe p xs
... | nothing = mapMaybe p xs

catMaybes : List (Maybe A) -> List A
catMaybes = mapMaybe id

foldr : (A -> B -> B) -> B -> List A -> B
foldr c n []       = n
foldr c n (x :: xs) = c x (foldr c n xs)

_++_ : List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

concat : List (List A) -> List A
concat = foldr _++_ []

concatMap : (A -> List B) -> List A -> List B
concatMap f = concat o map' f

data Fin : Nat -> Set where
    f0   : Fin (1+ n)
    f1+_ : Fin n -> Fin (1+ n)


data Int : Set where
    pos : Nat -> Int
    neg : Nat -> Int
    +-=0 : pos 0 === neg 0