--------------------------------------------------------------------------

--------------------------------------------------------------------------

-- The code does not follow the paper exactly. Notably, the formalization
-- covers both the main one used in majority of the paper and the
-- extended one used in section 8.

-- This is done achieved through a type of restrictions
-- (Definition.Modality.Restrictions) bundled with the modality semiring.
-- In particular, the system without modes is retrieved by disallowing
-- the zero mode and requireing that the extra Σ-type annotation equals
-- 𝟙. The moded system is converesly retrieved by allowing the zero mode.

-- This affects a number of other definitions and theorems which mention
-- modes. When the zero mode is disallowed, these reduce to the statments
-- found in the paper for the system without modes.

-- In addition, some parts of the code have been updated no longer match
-- the paper. Such differences are noted below.
-- TODO: Note such differences below.


module README where

import Definition.Modality
import Definition.Modality.Context
import Definition.Modality.FullReduction
import Definition.Modality.Instances.Unit
import Definition.Modality.Instances.Erasure
import Definition.Modality.Instances.Erasure.Modality
import Definition.Modality.Instances.Erasure.Properties
import Definition.Modality.Instances.Affine
import Definition.Modality.Instances.Linearity
import Definition.Modality.Instances.LowerBounded
import Definition.Modality.Instances.Recursive
import Definition.Modality.Instances.BoundedStar
import Definition.Modality.Usage
import Definition.Modality.Usage.Decidable
import Definition.Modality.Usage.Properties
import Definition.Modality.Substitution
import Definition.Modality.Substitution.Properties

import Definition.Untyped
import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Usage
import Definition.LogicalRelation
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility
import Definition.LogicalRelation.Substitution
import Definition.Mode

import Erasure.Target
import Erasure.Extraction
import Erasure.Extraction.Properties
import Erasure.LogicalRelation
import Erasure.LogicalRelation.Reduction
import Erasure.LogicalRelation.Subsumption
import Erasure.LogicalRelation.Fundamental
import Erasure.LogicalRelation.Fundamental.Counterexample
import Erasure.SucRed
import Erasure.Consequences.Soundness

import Application.NegativeAxioms.Canonicity.Erased
import Application.NegativeAxioms.Canonicity.EliminateErased

------------------------------------------------------------------------
-- 3: Modalities as grades in an ordered semiring

-- Definition 3.1: The modality semiring
-- Note that for the definition given here, the restrictions should be
-- set to disallow the zero mode.

Modality = Definition.Modality.Modality

-- Operations on modality contexts are lifted to act pointwise

_+_ = Definition.Modality.Context._+ᶜ_
_·_ = Definition.Modality.Context._·ᶜ_
_∧_ = Definition.Modality.Context._∧ᶜ_
_⊛_▷_ = Definition.Modality.Context._⊛ᶜ_▷_
_≤_ = Definition.Modality.Context._≤ᶜ_

-- The trivial (one element) modality

unitModality = Definition.Modality.Instances.Unit.UnitModality

-- An erasure modality

erasureModality = Definition.Modality.Instances.Erasure.Modality.ErasureModality

-- An "affine types" modality

affineModality = Definition.Modality.Instances.Affine.affineModality

-- A "linear types" modality.

linearityModality = Definition.Modality.Instances.Linearity.linearityModality

------------------------------------------------------------------------
-- 4: Type theory with grades

-- The grammar of the language

grammar = Definition.Untyped.Term

-- Weakenings

Wk = Definition.Untyped.Wk

-- Substitutions

Subst = Definition.Untyped.Subst

-- The typing relations

⊢_ = Definition.Typed.⊢_
_⊢_ = Definition.Typed._⊢_
_⊢_∷_ = Definition.Typed._⊢_∷_
_⊢_≡_ = Definition.Typed._⊢_≡_
_⊢_≡_∷_ = Definition.Typed._⊢_≡_∷_

-- Typing contexts

Con = Definition.Untyped.Con

-- Reduction relations

_⊢_⇒_ = Definition.Typed._⊢_⇒_
_⊢_⇒_∷_ = Definition.Typed._⊢_⇒_∷_
_⊢_⇒*_ = Definition.Typed._⊢_⇒*_
_⊢_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Theorem 4.3

Theorem-4-3a = Definition.Typed.Properties.whnfRed*Term
Theorem-4-3b = Definition.Typed.Properties.whnfRed*

-- Theorem 4.4

Theorem-4-4a = Definition.Typed.Properties.whrDet*Term
Theorem-4-4b = Definition.Typed.Properties.whrDet*

------------------------------------------------------------------------
-- 5: Assigning grades

-- Note that for the definitions and theorems in this section,
-- a modality with the zero mode disallowed should be used and the
-- extra annotation on Σ-types should be 𝟙

-- Definition 5.1: The usage relation

_▸_ = Definition.Modality.Usage._▸[_]_

-- Definition 5.2

_▶_ = Definition.Modality.Substitution._▶[_]_

-- Theorem 5.3: Substitution lemma for grade usage

Theorem-5-3 = Definition.Modality.Substitution.Properties.substₘ-lemma₁

-- Theorem 5.4: Subject reduction for grade usage

Theorem-5-4 = Definition.Typed.Usage.usagePresTerm

------------------------------------------------------------------------
-- 6: Erasure case study

-- Note that for the definitions and theorems in this section,
-- the modality has the zero mode disallowed and the extra annotation
-- on Σ-types is required to be 𝟙

-- Definition 6.1

𝟘ω = Definition.Modality.Instances.Erasure.Erasure

-- Theorem 6.2

Theorem-62 = Definition.Modality.Instances.Erasure.Modality.ErasureModality

-- Theorem 6.3

Theorem-63 = Definition.Modality.Instances.Erasure.Properties.valid-var-usage

-- The grammar of the untyped target language

target = Erasure.Target.Term

-- Definition 6.5: The extraction function

_• = Erasure.Extraction.erase

-- Theorem 6.6

Theorem-66 = Erasure.Extraction.Properties.erased-hasX

-- Reducibility logical relation for types

_⊩′⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- Reducibility logical relation for terms

_⊩′⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- The fundamental lemma of the reducibility relation

fundamentalReducible = Definition.LogicalRelation.Fundamental.fundamental

-- Definition 6.7: The logical relation for erasure

_®⟨_⟩_∷_/_ = Erasure.LogicalRelation._®⟨_⟩_∷_/_

-- Valid substitutions

_⊩ˢ_∷_/_ = Definition.LogicalRelation.Substitution._⊩ˢ_∷_/_/_

-- Definition 6.8: The logical relation for substitutions

_®⟨_⟩_∷_◂_/_/_ = Erasure.LogicalRelation._®⟨_⟩_∷[_]_◂_/_/_

-- Definition 6.9: Erasure validity

_▸_⊩ʳ⟨_⟩_∷_/_/_ = Erasure.LogicalRelation._▸_⊩ʳ⟨_⟩_∷[_]_/_/_

-- Theorem 6.10: Backwards closure of logical relation under reduction

Theorem-610 = Erasure.LogicalRelation.Reduction.redSubstTerm*

-- Theorem 6.11: Subsumption of the logical relation

Theorem-611a = Erasure.LogicalRelation.Subsumption.subsumptionSubst
Theorem-611b = Erasure.LogicalRelation.Subsumption.subsumption

-- Theorem 6.12: The fundamental lemma

fundamental = Erasure.LogicalRelation.Fundamental.fundamental

-- Theorem 6.13: All substitutions are related under erased contexts

Theorem-613 = Erasure.LogicalRelation.Subsumption.erasedSubst

-- Theorem 6.14: The fundamental lemma for fully erased terms

Theorem-614 = Erasure.LogicalRelation.Fundamental.fundamentalErased

-- Extended reduction relations
_⊢_⇒ˢ_∷ℕ = Erasure.SucRed._⊢_⇒ˢ_∷ℕ
_⊢_⇒ˢ*_∷ℕ = Erasure.SucRed._⊢_⇒ˢ*_∷ℕ
_⇒ˢ_ = Erasure.SucRed._⇒ˢ_
_⇒ˢ*_ = Erasure.SucRed._⇒ˢ*_

-- Theorem 6.15: Soundness of the extraction function

soundness = Erasure.Consequences.Soundness.soundness-ℕ

------------------------------------------------------------------------
-- 7: Discussion

-- A lawful definition of ⊛ᵣ for lower bounded structures

⊛ᵣ-lower-bounded = Definition.Modality.Instances.LowerBounded._⊛_▷_

-- A lawful definition of ⊛ᵣ defined recursively

⊛ᵣ-recursive = Definition.Modality.Instances.Recursive._⊛_▷_

-- A lawful definition of ⊛ᵣ for bounded star-semirings

⊛ᵣ-star-semiring = Definition.Modality.Instances.BoundedStar._⊛_▷_

-- Theorem 7.1

theorem-71 = Application.NegativeAxioms.Canonicity.Erased.canonicityRed

-- A counteraxample to theorem 7.1 if erased matches are allowed

counterexample₁ = Application.NegativeAxioms.Canonicity.EliminateErased.cEx

-- A counterexample to the fundamental lemma if erased matches are allowed

counterexample₂ = Erasure.LogicalRelation.Fundamental.Counterexample.cEx

-- The existence of η-long normal forms

η-long-normal-forms = Definition.Modality.FullReduction.fullRedTerm

------------------------------------------------------------------------
-- 8: Extension: modes and graded Σ-types

-- Note that for the definitions and theorems in this section,
-- a modality with the zero mode allowed should be used.

-- Modes

Mode = Definition.Mode.Mode

-- Definition 8.1: The extended modality structure

ExtendedModality = Definition.Modality.Modality

-- The modality structures for erasure, affine and linear types
-- satisfy the conditions of the extended modality definition

erasureModalityₑ = Definition.Modality.Instances.Erasure.Modality.ErasureModality
affineModalityₑ = Definition.Modality.Instances.Affine.affineModality
linearityModalityₑ = Definition.Modality.Instances.Linearity.linearityModality

-- Subject reduction for the extended grade usage relation

subjectReduction = Definition.Typed.Usage.usagePresTerm

-- Translating modes into grades

⌜_⌝ = Definition.Mode.⌜_⌝

-- Translating grades into modes

⌞_⌟ = Definition.Mode.⌞_⌟

-- Scaling modes by grades

_⊙_ = Definition.Mode._ᵐ·_

-- The usage relation with modes

_▸[_]_ = Definition.Modality.Usage._▸[_]_

-- Theorem 8.3: Subject reduction for the usage relation with modes

Theorem-83 = Definition.Typed.Usage.usagePresTerm

-- The extraction function
-- Note that this has been updated to no longer use substitutions

_◦ = Erasure.Extraction.erase

-- Theorem 8.4: Soundness of the extraction function

Theorem-84 = Erasure.Consequences.Soundness.soundness-ℕ

------------------------------------------------------------------------
-- A: Logical relation for reducibility

-- Combined reduction and typing relations

_⊢_:⇒*:_∷_ = Definition.Typed._⊢_:⇒*:_∷_
_⊢_:⇒*:_ = Definition.Typed._⊢_:⇒*:_

-- Definition A.1: Reducibility of types

_⊩⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- Definition A.2: Reducibility of terms

_⊩⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- Definition A.3: Equality of reducible types

_⊩⟨_⟩_≡_/_ = Definition.LogicalRelation._⊩⟨_⟩_≡_/_

-- Definition A.4: Equality of reducible terms

_⊩⟨_⟩_≡_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_≡_∷_/_

-- Definition A.6: Validity of contexts

⊩ᵛ_ = Definition.LogicalRelation.Substitution.⊩ᵛ_

-- Definition A.7: Validity of substitutions and equality of
-- valid substitutions

_⊩ˢ_∷_/_/_ = Definition.LogicalRelation.Substitution._⊩ˢ_∷_/_/_

-- Definition A.8: Validity of types, terms and equality of
-- valid types and terms

_⊩ᵛ⟨_⟩_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_/_
_⊩ᵛ⟨_⟩_∷_/_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_∷_/_/_
_⊩ᵛ⟨_⟩_≡_/_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_≡_/_/_
_⊩ᵛ⟨_⟩_≡_∷_/_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_≡_∷_/_/_

-- Theorem A.9: The fundamental lemma

fundamentalType = Definition.LogicalRelation.Fundamental.Reducibility.reducible
fundamentalTerm = Definition.LogicalRelation.Fundamental.Reducibility.reducibleTerm
fundamentalTypeEq = Definition.LogicalRelation.Fundamental.Reducibility.reducibleEq
fundamentalTermEq = Definition.LogicalRelation.Fundamental.Reducibility.reducibleEqTerm

------------------------------------------------------------------------
-- B: Usage inference

-- Definition B.1: Usage inference

∣_∣ = Definition.Modality.Usage.⌈_⌉

-- Theorem B.2

Theorem-B2a = Definition.Modality.Usage.Properties.usage-inf
Theorem-B2b = Definition.Modality.Usage.Properties.usage-upper-bound

-- Theorem B.3: Decidability of the usage relation

Theorem-B3a = Definition.Modality.Usage.Decidable.⌈⌉▸[_]?_
Theorem-B3b = Definition.Modality.Usage.Decidable._▸[_]?_

-- Definition B.4: Substitution matrix inference

∥_∥ = Definition.Modality.Substitution.∥_∥

-- Theorem B.5

Theorem-B5 = Definition.Modality.Substitution.Properties.subst-calc-correct′
