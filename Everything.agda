------------------------------------------------------------------------
-- Graded modal type theory formalized in Agda
------------------------------------------------------------------------

module Everything where

------------------------------------------------------------------------
-- A small library

import Tools.Level
import Tools.Empty
import Tools.Unit
import Tools.Relation
import Tools.PropositionalEquality
import Tools.Nullary
import Tools.Bool
import Tools.Product
import Tools.Function
import Tools.Nat
import Tools.Fin
import Tools.Sum
import Tools.List
import Tools.Algebra

import Tools.Reasoning.Preorder
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- The type theory

-- Grammar of the language
import Definition.Untyped.NotParametrised
import Definition.Untyped

-- Properties of the untyped syntax
import Definition.Untyped.Inversion
import Definition.Untyped.Properties

-- Typing and conversion rules of language
import Definition.Typed.Restrictions
import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.RedSteps
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance

-- The logical relation for reducibility
import Definition.LogicalRelation
import Definition.LogicalRelation.Properties.Escape
import Definition.LogicalRelation.Properties.Reflexivity
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties.Conversion
import Definition.LogicalRelation.Properties.MaybeEmb
import Definition.LogicalRelation.Properties.Symmetry
import Definition.LogicalRelation.Properties.Neutral
import Definition.LogicalRelation.Properties.Universe
import Definition.LogicalRelation.Properties.Reduction
import Definition.LogicalRelation.Properties.Successor
import Definition.LogicalRelation.Properties.Transitivity
import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Application

-- The logical relation for validity
import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Reducibility
import Definition.LogicalRelation.Substitution.Escape

-- The fundamental lemma of the logical relations
import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
import Definition.LogicalRelation.Substitution.Introductions.Universe
import Definition.LogicalRelation.Substitution.Introductions.Empty
import Definition.LogicalRelation.Substitution.Introductions.Emptyrec
import Definition.LogicalRelation.Substitution.Introductions.Unit
import Definition.LogicalRelation.Substitution.Introductions.Nat
import Definition.LogicalRelation.Substitution.Introductions.Natrec
import Definition.LogicalRelation.Substitution.Introductions.Pi
import Definition.LogicalRelation.Substitution.Introductions.Lambda
import Definition.LogicalRelation.Substitution.Introductions.Application
import Definition.LogicalRelation.Substitution.Introductions.Prod
import Definition.LogicalRelation.Substitution.Introductions.Fst
import Definition.LogicalRelation.Substitution.Introductions.Snd
import Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta
import Definition.LogicalRelation.Substitution.Introductions.Var
import Definition.LogicalRelation.Substitution.Introductions.DoubleSubst
import Definition.LogicalRelation.Substitution.Introductions.Prodrec
import Definition.LogicalRelation.Substitution.Introductions
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the logical relation for typing
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Consequences.Inequality
import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Consequences.Stability
import Definition.Untyped.Sigma
import Definition.Typed.Consequences.DerivedRules.Nat
import Definition.Typed.Consequences.DerivedRules.Sigma
import Definition.Typed.Consequences.DerivedRules
import Definition.Typed.Consequences.InverseUniv
import Definition.Typed.Consequences.NeTypeEq
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Consequences.RedSteps

-- Algorithmic equality with lemmas that depend on typing consequences
import Definition.Conversion
import Definition.Conversion.Whnf
import Definition.Conversion.Reduction
import Definition.Conversion.Soundness
import Definition.Conversion.Stability
import Definition.Conversion.Conversion
import Definition.Conversion.Symmetry
import Definition.Conversion.Transitivity
import Definition.Conversion.Weakening
import Definition.Conversion.Lift
import Definition.Conversion.Universe
import Definition.Conversion.Decidable
import Definition.Conversion.EqRelInstance
import Definition.Conversion.Consequences.Completeness
import Definition.Untyped.Normal-form
import Definition.Typed.Eta-long-normal-form
import Definition.Conversion.FullReduction

-- Bi-directional typechecking
import Definition.Typechecking
import Definition.Typechecking.Deterministic
import Definition.Typechecking.Soundness
import Definition.Typechecking.Completeness

-- Decidability of typing
import Definition.Typed.Decidable.Equality
import Definition.Typed.Decidable.Reduction
import Definition.Typechecking.Decidable
import Definition.Typed.Decidable

------------------------------------------------------------------------
-- Graded modalities and usage

-- Modality structure
import Graded.Modality.Variant
import Graded.Modality
import Graded.Modality.Natrec-star-instances
import Graded.Modality.Dedicated-star
import Graded.Modality.Dedicated-star.Instance

-- Properties of the modality semiring
import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Equivalence
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Star
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties

-- Modality contexts and their properties
import Graded.Context
import Graded.Context.Properties.Equivalence
import Graded.Context.Properties.PartialOrder
import Graded.Context.Properties.Meet
import Graded.Context.Properties.Addition
import Graded.Context.Properties.Multiplication
import Graded.Context.Properties.Star
import Graded.Context.Properties.Lookup
import Graded.Context.Properties.Update
import Graded.Context.Properties.Has-well-behaved-zero
import Graded.Context.Properties

-- Usage modes
import Graded.Mode

-- The usage relation and its properties
import Graded.Usage.Restrictions
import Graded.Usage
import Graded.Usage.Inversion
import Graded.Usage.Properties
import Graded.Usage.Properties.Has-well-behaved-zero
import Graded.Usage.Weakening
import Graded.Usage.Decidable

-- Definitions related to type and usage restrictions
import Graded.Restrictions

-- Modality substitutions
import Graded.Substitution
import Graded.Substitution.Properties
import Graded.Substitution.Decidable

-- Assumptions used to state the theorems in
-- Graded.FullReduction
import Graded.FullReduction.Assumptions

-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa.
import Graded.Derived.Sigma

-- Modality pseudo-instances
import Graded.Modality.Instances.LowerBounded
import Graded.Modality.Instances.BoundedStar
import Graded.Modality.Instances.Finite
import Graded.Modality.Instances.Recursive.Sequences
import Graded.Modality.Instances.Recursive
import Graded.Modality.Instances.Erasure
import Graded.Modality.Instances.Zero-one-many
import Graded.Modality.Instances.Bounded-distributive-lattice

-- Modality instances
import Graded.Modality.Instances.Erasure.Modality
import Graded.Modality.Instances.Erasure.Properties
import Graded.Modality.Instances.Unit
import Graded.Modality.Instances.Affine
import Graded.Modality.Instances.Linearity
import Graded.Modality.Instances.Linearity.Properties
import Graded.Modality.Instances.Linear-or-affine
import Graded.Modality.Instances.Information-flow
import Graded.Modality.Instances.Zero-below-one
import Graded.Modality.Instances.Nat-plus-infinity
import
  Graded.Modality.Instances.Bounded-distributive-lattice.No-division

-- Subject reduction for modalities.
import Graded.Reduction

-- A "full reduction" lemma for modalities.
import Graded.FullReduction


------------------------------------------------------------------------
-- A case study: erasure

-- Target language

import Graded.Erasure.Target
import Graded.Erasure.Target.Properties.Weakening
import Graded.Erasure.Target.Properties.Substitution
import Graded.Erasure.Target.Properties.Reduction
import Graded.Erasure.Target.Properties

-- Extraction

import Graded.Erasure.Extraction
import Graded.Erasure.Extraction.Properties

-- Logical relation for Erasure

import Graded.Erasure.LogicalRelation
import Graded.Erasure.LogicalRelation.Conversion
import Graded.Erasure.LogicalRelation.Irrelevance
import Graded.Erasure.LogicalRelation.Reduction
import Graded.Erasure.LogicalRelation.Subsumption

-- The fundamental lemma of the logical relation

import Graded.Erasure.LogicalRelation.Fundamental.Application
import Graded.Erasure.LogicalRelation.Fundamental.Empty
import Graded.Erasure.LogicalRelation.Fundamental.Lambda
import Graded.Erasure.LogicalRelation.Fundamental.Nat
import Graded.Erasure.LogicalRelation.Fundamental.Natrec
import Graded.Erasure.LogicalRelation.Fundamental.Prodrec
import Graded.Erasure.LogicalRelation.Fundamental.Product
import Graded.Erasure.LogicalRelation.Fundamental.Unit
import Graded.Erasure.LogicalRelation.Fundamental.Assumptions
import Graded.Erasure.LogicalRelation.Fundamental

-- The fundamental lemma does not hold in general without the
-- assumption that erased matches are disallowed or the context is
-- empty
import Graded.Erasure.LogicalRelation.Fundamental.Counterexample

-- Soundness of Extraction function
import Graded.Erasure.SucRed
import Graded.Erasure.Consequences.Soundness

-- Non-interference
import Graded.Erasure.Consequences.Non-interference

-- Some examples related to the erasure modality and extraction

import Graded.Erasure.Examples

------------------------------------------------------------------------
-- Pointers to code related to a paper

-- Pointers to code related to the paper "A Graded Modal Dependent
-- Type Theory with a Universe and Erasure, Formalized".
import README
