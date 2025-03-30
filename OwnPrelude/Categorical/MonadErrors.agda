{-# OPTIONS --cubical #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --no-unicode #-}
{-# OPTIONS --safe #-}
module OwnPrelude.Categorical.MonadErrors where

open import ASCIIPrelude.ASCIIPrelude 
open PolyUnit
open import OwnPrelude.Equality
open import OwnPrelude.Categorical.Monads

open ExistsSyntax

private
    variable
        h i j k k' l i' j' c u : Level
        n n' : Nat
        A B C X Y Z L S Err : Set i
        F G M : Set i -> Set j
        a b e x y z m : A
        f g : A -> B

module _ {M : Set i -> Set j} (rawMonad : RawMonad M) where
    record RawMonadErrorOver (Err : Set u) : Set (lsuc i ~U~ u ~U~ j) where
        field
            throw : Err -> M A
            catch : M A -> (Err -> M A) -> M A
            -- rawMonad : RawMonad M
        open RawMonad rawMonad

        catch' : M A -> M A -> M A
        catch' ma ma' = catch ma (const ma')

        catch-default : M A -> A -> M A
        catch-default ma a = catch' ma (return a)

        private 
            _<fork>'_ : M Unit -> M Unit -> M Unit
            a <fork>' b = catch a (\_ -> b) >> b

        _<fork>_ : M A -> M B -> M Unit
        a <fork> b = void a <fork>' void b

module _ 
    {M : Set i -> Set j}
    {rawMonad : RawMonad M} 
    (isMonad : IsMonad rawMonad) where
    -- Laws from monad throw and monad catch
    record IsMonadErrorOver 
        {Err : Set u}
        (rawMonadError : RawMonadErrorOver rawMonad Err) : Set (lsuc i ~U~ u ~U~ j) where
        open RawMonadErrorOver rawMonadError
        open RawMonad rawMonad
        field
            left-absorb : throw e >>= m === throw e
            throw-catch : catch (throw e) f === f e
            -- isMonad : IsMonad rawMonad

module _ 
    {M : Set i -> Set j}
    (mon : Monad M) where

    record MonadErrorOver (Err : Set u) : Set (lsuc i ~U~ u ~U~ j) where
        field
            rawMonadErrorOver : RawMonadErrorOver (Monad.rawMonad mon) Err
            isMonadErrorOver  : IsMonadErrorOver (Monad.isMonad mon) rawMonadErrorOver
        open RawMonadErrorOver rawMonadErrorOver public
        open IsMonadErrorOver  isMonadErrorOver  public

        -- monad : Monad M
        -- Monad.rawMonad monad = rawMonad
        -- Monad.isMonad  monad = isMonad