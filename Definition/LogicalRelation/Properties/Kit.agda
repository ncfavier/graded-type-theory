------------------------------------------------------------------------
-- Some definitions related to kit and kit′
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Kit
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (K)
open import Definition.Untyped.Neutral Mod type-variant
open import Definition.Untyped.Properties Mod
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.LogicalRelation R

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private variable
  l l₁ l₂ k₁ k₂ n : Nat
  Γ               : Con Term _
  A B t u         : Term _

-- A variant of _⊩⟨_⟩_.

infix 4 _⊩<⟨_⟩_

_⊩<⟨_⟩_ : Con Term n → l₁ <ᵘ l₂ → Term n → Set a
Γ ⊩<⟨ p ⟩ A = LogRelKit._⊩_ (kit′ p) Γ A

-- A variant of _⊩⟨_⟩_≡_/_.

infix 4 _⊩<⟨_⟩_≡_/_

_⊩<⟨_⟩_≡_/_ :
  (Γ : Con Term n) (p : l₁ <ᵘ l₂) (A _ : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A = LogRelKit._⊩_≡_/_ (kit′ p) Γ A B ⊩A

-- A variant of _⊩⟨_⟩_∷_/_.

infix 4 _⊩<⟨_⟩_∷_/_

_⊩<⟨_⟩_∷_/_ :
  (Γ : Con Term n) (p : l₁ <ᵘ l₂) (t A : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A = LogRelKit._⊩_∷_/_ (kit′ p) Γ t A ⊩A

-- A variant of _⊩⟨_⟩_≡_∷_/_.

infix 4 _⊩<⟨_⟩_≡_∷_/_

_⊩<⟨_⟩_≡_∷_/_ :
  (Γ : Con Term n) (p : l₁ <ᵘ l₂) (t u : Term n) (A : Term n) → Γ ⊩<⟨ p ⟩ A → Set a
Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A = LogRelKit._⊩_≡_∷_/_ (kit′ p) Γ t u A ⊩A

-- If p : l₁ <ᵘ l₂, then Γ ⊩<⟨ p ⟩ A is logically equivalent to
-- Γ ⊩⟨ l₁ ⟩ A.

⊩<⇔⊩ : (p : l₁ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A ⇔ Γ ⊩⟨ l₁ ⟩ A
⊩<⇔⊩ ≤ᵘ-refl     = id⇔
⊩<⇔⊩ (≤ᵘ-step p) = ⊩<⇔⊩ p

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<≡⇔⊩≡ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡⇔⊩≡ ≤ᵘ-refl     = id⇔
⊩<≡⇔⊩≡ (≤ᵘ-step p) = ⊩<≡⇔⊩≡ p

-- A variant of ⊩<≡⇔⊩≡.

⊩<≡⇔⊩≡′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ A ≡ B / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩A
⊩<≡⇔⊩≡′ ≤ᵘ-refl     = id⇔
⊩<≡⇔⊩≡′ (≤ᵘ-step p) = ⊩<≡⇔⊩≡′ p

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<∷⇔⊩∷ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ∷ A / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<∷⇔⊩∷ ≤ᵘ-refl     = id⇔
⊩<∷⇔⊩∷ (≤ᵘ-step p) = ⊩<∷⇔⊩∷ p

-- A variant of ⊩<∷⇔⊩∷.

⊩<∷⇔⊩∷′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ∷ A / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩A
⊩<∷⇔⊩∷′ ≤ᵘ-refl     = id⇔
⊩<∷⇔⊩∷′ (≤ᵘ-step p) = ⊩<∷⇔⊩∷′ p

-- If p : l₁ <ᵘ l₂ and ⊩A : Γ ⊩<⟨ p ⟩ A, then Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A is
-- logically equivalent to Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A.

⊩<≡∷⇔⊩≡∷ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₁ ⊩A
⊩<≡∷⇔⊩≡∷ ≤ᵘ-refl     = id⇔
⊩<≡∷⇔⊩≡∷ (≤ᵘ-step p) = ⊩<≡∷⇔⊩≡∷ p

-- A variant of ⊩<≡∷⇔⊩≡∷.

⊩<≡∷⇔⊩≡∷′ :
  (p : l₁ <ᵘ l₂) {⊩A : Γ ⊩⟨ l₁ ⟩ A} →
  Γ ⊩<⟨ p ⟩ t ≡ u ∷ A / ⊩<⇔⊩ p .proj₂ ⊩A ⇔ Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩A
⊩<≡∷⇔⊩≡∷′ ≤ᵘ-refl     = id⇔
⊩<≡∷⇔⊩≡∷′ (≤ᵘ-step p) = ⊩<≡∷⇔⊩≡∷′ p

opaque

  -- If p : l₁ <ᵘ l₂, then kit l₁ is equal to kit′ p.

  kit≡kit′ : (p : l₁ <ᵘ l₂) → kit l₁ PE.≡ kit′ p
  kit≡kit′ ≤ᵘ-refl     = PE.refl
  kit≡kit′ (≤ᵘ-step p) = kit≡kit′ p

opaque

  -- Irrelevance for _⊩<⟨_⟩_.

  irrelevance-⊩< :
    (eq : k₁ PE.≡ k₂) (p : k₁ <ᵘ l₁) (q : k₂ <ᵘ l₂) → Γ ⊩<⟨ p ⟩ A → Γ ⊩<⟨ q ⟩ A
  irrelevance-⊩< PE.refl ≤ᵘ-refl     ≤ᵘ-refl     = idᶠ
  irrelevance-⊩< PE.refl p           (≤ᵘ-step q) = irrelevance-⊩< PE.refl p q
  irrelevance-⊩< PE.refl (≤ᵘ-step p) q           = irrelevance-⊩< PE.refl p q

opaque
  unfolding irrelevance-⊩<

  -- One form of irrelevance for _⊩<⟨_⟩_≡_/_.

  irrelevance-⊩<≡ :
    ∀ {Γ : Con Term n} (eq : k₁ PE.≡ k₂) (p : k₁ <ᵘ l₁) (q : k₂ <ᵘ l₂) {⊩A : Γ ⊩<⟨ p ⟩ A} →
    Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A →
    Γ ⊩<⟨ q ⟩ A ≡ B / irrelevance-⊩< eq p q ⊩A
  irrelevance-⊩<≡ PE.refl ≤ᵘ-refl     ≤ᵘ-refl     = idᶠ
  irrelevance-⊩<≡ PE.refl (≤ᵘ-step p) ≤ᵘ-refl     = irrelevance-⊩<≡ PE.refl p ≤ᵘ-refl
  irrelevance-⊩<≡ PE.refl ≤ᵘ-refl     (≤ᵘ-step q) = irrelevance-⊩<≡ PE.refl ≤ᵘ-refl q
  irrelevance-⊩<≡ PE.refl (≤ᵘ-step p) (≤ᵘ-step q) = irrelevance-⊩<≡ PE.refl (≤ᵘ-step p) q
