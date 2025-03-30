{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.IMonadTs where

open import ASCIIPrelude.ASCIIPrelude 
open import OwnPrelude.Equality hiding (i0; i1)
open import OwnPrelude.Categorical.IMonads

private
    variable
        hl il jl kl kl' ll il' jl' ul ul' : Level
        n n' : Nat
        A B C X Y Z L S : Set il
        F G : Set il -> Set jl
        a b c x y z m : A
        f g : A -> B

module SameIdxIMonadT {I : Set ul} where 
    private
        variable
            h i j k : I

    record RawIMonadT (M : I -> I -> Set il -> Set jl) (T : I -> I -> Set il -> Set kl) : Set (lsuc il ~U~ jl ~U~ kl ~U~ ul) where
        field
            rawInnerIMonad : RawIMonad M
            rawOuterIMonad : RawIMonad T
            lift : M i j A -> T i j A

    record IsIMonadT 
        {M : I -> I -> Set il -> Set jl} 
        {T : I -> I -> Set il -> Set kl}
        (rawIMonadT : RawIMonadT M T) 
        : Set (lsuc il ~U~ jl ~U~ kl ~U~ ul) where
        open RawIMonadT rawIMonadT
        open RawIMonad rawInnerIMonad renaming (return to returnM; _>>=_ to _>>=M_)
        open RawIMonad rawOuterIMonad renaming (return to returnT; _>>=_ to _>>=T_)
        field
            isInnerIMonad : IsIMonad rawInnerIMonad
            isOuterIMonad : IsIMonad rawOuterIMonad
            lift-return  : lift {i = i} o returnM  === returnT {A = A}
            lift-bind    : lift (m >>=M f) === (lift m) >>=T (lift o f)

    record IMonadT (M : I -> I -> Set il -> Set jl) (T : I -> I -> Set il -> Set kl) : Set (lsuc il ~U~ jl ~U~ kl ~U~ ul) where
        field
            rawIMonadT : RawIMonadT M T
            isIMonadT  : IsIMonadT rawIMonadT
        open RawIMonadT rawIMonadT public
        open IsIMonadT   isIMonadT  public 

        innerIMonad : IMonad M
        IMonad.rawIMonad innerIMonad = rawInnerIMonad
        IMonad.isIMonad  innerIMonad = isInnerIMonad

        outerIMonad : IMonad T
        IMonad.rawIMonad outerIMonad = rawOuterIMonad
        IMonad.isIMonad  outerIMonad = isOuterIMonad

module TupIdxIMonadT {I : Set ul} {J : Set ul'} where 
    private
        variable
            i i'  : I
            j j' : J

    record RawIMonadT (M : J -> J -> Set il -> Set jl) (T : (I -x- J) -> (I -x- J) -> Set il -> Set kl) : Set (lsuc il ~U~ jl ~U~ kl ~U~ ul ~U~ ul') where
        field
            rawInnerIMonad : RawIMonad M
            rawOuterIMonad : RawIMonad T
            lift : M j j' A -> T (i , j) (i , j') A

    record IsIMonadT 
        {M : J -> J -> Set il -> Set jl} 
        {T : (I -x- J) -> (I -x- J) -> Set il -> Set kl}
        (rawIMonadT : RawIMonadT M T) 
        : Set (lsuc il ~U~ jl ~U~ kl ~U~ ul ~U~ ul') where
        open RawIMonadT rawIMonadT
        open RawIMonad rawInnerIMonad renaming (return to returnM; _>>=_ to _>>=M_)
        open RawIMonad rawOuterIMonad renaming (return to returnT; _>>=_ to _>>=T_)
        field
            isInnerIMonad : IsIMonad rawInnerIMonad
            isOuterIMonad : IsIMonad rawOuterIMonad
            lift-return  : lift {j = j} {i = i} o returnM  === returnT {A = A}
            lift-bind    : lift {i = i} (m >>=M f) === (lift m) >>=T (lift o f)

    record IMonadT (M : J -> J -> Set il -> Set jl) (T : (I -x- J) -> (I -x- J) -> Set il -> Set kl) : Set (lsuc il ~U~ jl ~U~ kl ~U~ ul ~U~ ul') where
        field
            rawIMonadT : RawIMonadT M T
            isIMonadT  : IsIMonadT rawIMonadT
        open RawIMonadT rawIMonadT public
        open IsIMonadT   isIMonadT  public 

        innerIMonad : IMonad M
        IMonad.rawIMonad innerIMonad = rawInnerIMonad
        IMonad.isIMonad  innerIMonad = isInnerIMonad

        outerIMonad : IMonad T
        IMonad.rawIMonad outerIMonad = rawOuterIMonad
        IMonad.isIMonad  outerIMonad = isOuterIMonad

module _ {I : Set ul} {J : Set ul'} where 
    toITup : (M : I -> I -> Set il -> Set jl) -> (I -x- J) -> (I -x- J) -> Set il -> Set jl
    toITup M (i , _) (i' , _) = M i i'

    module _ {M : I -> I -> Set il -> Set jl} (mon : IMonad M) where
        open IMonad mon
        toTupMon : IMonad (toITup M)
        RawIMonad.return (IMonad.rawIMonad toTupMon) = return
        RawIMonad._>>=_  (IMonad.rawIMonad toTupMon) = _>>=_
        IsIMonad.left-identity  (IMonad.isIMonad toTupMon) = left-identity
        IsIMonad.right-identity (IMonad.isIMonad toTupMon) = right-identity
        IsIMonad.associative    (IMonad.isIMonad toTupMon) = associative