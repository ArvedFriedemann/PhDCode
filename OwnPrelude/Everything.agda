{-# OPTIONS --cubical --guardedness #-}
module OwnPrelude.Everything where

-- code on general categorical constructions like functors and monads and other monadic interfaces
open import OwnPrelude.Categorical.Alternatives
open import OwnPrelude.Categorical.Applicatives
open import OwnPrelude.Categorical.Functors
open import OwnPrelude.Categorical.IApplicatives
open import OwnPrelude.Categorical.IMonads
open import OwnPrelude.Categorical.IMonadTs
open import OwnPrelude.Categorical.IMonoids
open import OwnPrelude.Categorical.MonadErrors
open import OwnPrelude.Categorical.MonadFailAlternatives
open import OwnPrelude.Categorical.MonadPlus
open import OwnPrelude.Categorical.Monads
open import OwnPrelude.Categorical.MonadTs
open import OwnPrelude.Categorical.Monoids

open import OwnPrelude.Data.BiThresholdVariables        -- (semi)lattice bi-threshold variables
open import OwnPrelude.Data.BooleanInstances
open import OwnPrelude.Data.ConstrainedStates           -- constrained state monad transformer
open import OwnPrelude.Data.Containers
open import OwnPrelude.Data.Decidables
open import OwnPrelude.Data.ErrorT
open import OwnPrelude.Data.IConstrainedStates          -- indexed version of constrained state monad transformer
open import OwnPrelude.Data.ILatticeStates
open import OwnPrelude.Data.LatticeStates
open import OwnPrelude.Data.ListCategorical
open import OwnPrelude.Data.MaybeCategorical
open import OwnPrelude.Data.MonadicVariables            -- definition of monadic variables from Chapter on Monadic Solving
open import OwnPrelude.Data.NTuples
open import OwnPrelude.Data.Perhaps                     -- definition of perhaps values from Chapter on Theory of Solving
open import OwnPrelude.Data.SizedFixpoints
open import OwnPrelude.Data.ThresholdVariables          -- threshold variables before the introduction of bi-threshold variables
open import OwnPrelude.Data.TrivialLattices             -- definition and instances for the trivial lattice
open import OwnPrelude.Data.VarAsms                     -- variable assignments used as the result of threshold functions

open import OwnPrelude.Examples.DataTypesForMonadicSolvingExamples      -- examples for the folds in the explanation of containers in Chapter on Data Types for Monadic Solving
open import OwnPrelude.Examples.LatticeStateSATSolver                   -- SAT-Solving example

--Chapter Data Types for Monadic Solving                                    -- fist three files are the constructions for the Chapter on Data Types for Monadic Solving
open import OwnPrelude.GeneralSolving.BiThresholdsAndContainers             -- constructions around commuting contexts and held-in-stasis data types
open import OwnPrelude.GeneralSolving.BiThresholdsAndContainersPartII       -- construction of the lattice instance for container extensions
open import OwnPrelude.GeneralSolving.BiThresholdsAndContainersPartIII      -- constructions for the lemma attaching variables to positions in the latticed container extension
open import OwnPrelude.GeneralSolving.TypeOfTypeTheory                      -- type of type theory / type for syntax of type theory


--Chapter Towards a General Theory of Solving
open import OwnPrelude.GeneralSolving.GeneralSolving                        -- some first constructions in Chapter on Theory of Solving
open import OwnPrelude.GeneralSolving.LatticeTheory                         -- theory around order preserving increasing functions from Chapter THeory of Solving


-- miscillaneous definitions of relations, including (indexed) lattices
open import OwnPrelude.Relation.Functions
open import OwnPrelude.Relation.ILattices
open import OwnPrelude.Relation.IPreOrders
open import OwnPrelude.Relation.LatticeConstructions                        -- lattice product construction
open import OwnPrelude.Relation.Lattices
open import OwnPrelude.Relation.PreOrders
open import OwnPrelude.Relation.Properties


open import Preliminaries.Preliminaries
open import Preliminaries.PreliminariesPartII

-- not cubical compatible yet
-- open import ChapterMonadicSolving.MonadicSolvingChapterPartI
-- open import ChapterMonadicSolving.MonadicSolvingChapterPartII