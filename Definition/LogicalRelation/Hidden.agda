------------------------------------------------------------------------
-- A variant of the logical relation with hidden reducibility
-- arguments, along with variants of some other relations
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Hidden
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R {{eqrel}} renaming (_⊩⟨_⟩_ to _⊩′⟨_⟩_) public
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Properties.Primitive R
open import Definition.LogicalRelation.ShapeView R {{eqrel}}
import Definition.LogicalRelation.Weakening R as W

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R using (_∷ʷ_⊇_)
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n                      : Nat
  Γ Δ                    : Con Term _
  A B C t t₁ t₂ u v l l′ : Term _
  ρ                      : Wk _ _
  k                      : LogRelKit
  ℓ                      : Universe-level

------------------------------------------------------------------------
-- The type formers

opaque

  -- Reducible types.

  infix 4 _⊩⟨_⟩_

  _⊩⟨_⟩_ : Con Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ A =
    ∃ λ (⊩l : Γ ⊩Level l ∷Level) → Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ A

  -- Reducible terms.

  infix 4 _⊩⟨_⟩_∷_

  _⊩⟨_⟩_∷_ : Con Term n → Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ∷ A =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ ↑ᵘ ⊩A .proj₁ ⟩ t ∷ A / ⊩A .proj₂

  -- Reducible type equality.

  infix 4 _⊩⟨_⟩_≡_

  _⊩⟨_⟩_≡_ : Con Term n → Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ A ≡ B =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) → (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ ↑ᵘ ⊩A .proj₁ ⟩ A ≡ B / ⊩A .proj₂

  -- Reducible term equality.

  infix 4 _⊩⟨_⟩_≡_∷_

  _⊩⟨_⟩_≡_∷_ :
    Con Term n → Term n → Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ ↑ᵘ ⊩A .proj₁ ⟩ t ∷ A / ⊩A .proj₂ ×
    Γ ⊩⟨ ↑ᵘ ⊩A .proj₁ ⟩ u ∷ A / ⊩A .proj₂ ×
    Γ ⊩⟨ ↑ᵘ ⊩A .proj₁ ⟩ t ≡ u ∷ A / ⊩A .proj₂

------------------------------------------------------------------------
-- Conversions to the underlying type formers

opaque
  unfolding _⊩⟨_⟩_

  -- A conversion to _⊩′⟨_⟩_.

  ⊩→⊩ : (⊩l : Γ ⊩Level l ∷Level) → Γ ⊩⟨ l ⟩ A → Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ A
  ⊩→⊩ ⊩l (⊩l′ , ⊩A) = PE.subst (_ ⊩′⟨_⟩ _) (↑ᵘ-irrelevance ⊩l′ ⊩l) ⊩A

opaque

  -- A conversion to _⊩<⟨_⟩_.

  ⊩→⊩< : {⊩l : Γ ⊩Level l ∷Level} (p : ↑ᵘ ⊩l <ᵘ ℓ) → Γ ⊩⟨ l ⟩ A → Γ ⊩<⟨ p ⟩ A
  ⊩→⊩< p ⊩A = ⊩<⇔⊩ p .proj₂ (⊩→⊩ _ ⊩A)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A conversion to _⊩⟨_⟩_∷_/_.

  ⊩∷→⊩∷/ : (⊩A : Γ ⊩′⟨ ℓ ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ ℓ ⟩ t ∷ A / ⊩A
  ⊩∷→⊩∷/ ⊩A (⊩A′ , ⊩t) = irrelevanceTerm (⊩A′ .proj₂) ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A conversion to _⊩⟨_⟩_≡_/_.

  ⊩≡→⊩≡/ : (⊩A : Γ ⊩′⟨ ℓ ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ ℓ ⟩ A ≡ B / ⊩A
  ⊩≡→⊩≡/ ⊩A (⊩A′ , _ , A≡B) = irrelevanceEq (⊩A′ .proj₂) ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A conversion to _⊩<⟨_⟩_≡_/_.

  ⊩≡→⊩<≡/ : {⊩l : Γ ⊩Level l ∷Level} (p : ↑ᵘ ⊩l <ᵘ ℓ) (⊩A : Γ ⊩<⟨ p ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A
  ⊩≡→⊩<≡/ p ⊩A A≡B = ⊩<≡⇔⊩≡ p .proj₂ (⊩≡→⊩≡/ (⊩<⇔⊩ p .proj₁ ⊩A) A≡B)

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A conversion to _⊩⟨_⟩_≡_∷_/_.

  ⊩≡∷→⊩≡∷/ :
    (⊩A : Γ ⊩′⟨ ℓ ⟩ A) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / ⊩A
  ⊩≡∷→⊩≡∷/ ⊩A (⊩A′ , _ , _ , t≡u) = irrelevanceEqTerm (⊩A′ .proj₂) ⊩A t≡u

------------------------------------------------------------------------
-- Reflexivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reflexivity for _⊩⟨_⟩_≡_.

  refl-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ A ≡ A
  refl-⊩≡ ⊩A =
    ⊩A , ⊩A , reflEq (⊩A .proj₂)

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Reflexivity for _⊩⟨_⟩_≡_∷_.

  refl-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  refl-⊩≡∷ (⊩A , ⊩t) =
    ⊩A , ⊩t , ⊩t , reflEqTerm (⊩A .proj₂) ⊩t

------------------------------------------------------------------------
-- Symmetry

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Symmetry for _⊩⟨_⟩_≡_.

  sym-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ A
  sym-⊩≡ (⊩A , ⊩B , A≡B) =
    ⊩B , ⊩A , symEq (⊩A .proj₂) (⊩B .proj₂) A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Symmetry for _⊩⟨_⟩_≡_∷_.

  sym-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ t ∷ A
  sym-⊩≡∷ (⊩A , ⊩t , ⊩u , t≡u) =
    ⊩A , ⊩u , ⊩t , symEqTerm (⊩A .proj₂) t≡u

------------------------------------------------------------------------
-- Transitivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Transitivity for _⊩⟨_⟩_≡_.

  trans-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l ⟩ A ≡ C
  trans-⊩≡ (⊩A , _ , A≡B) (⊩B , ⊩C , B≡C) =
    ⊩A , ⊩C , transEq (⊩A .proj₂) (⊩B .proj₂) (⊩C .proj₂) A≡B B≡C

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Transitivity for _⊩⟨_⟩_≡_∷_.

  trans-⊩≡∷ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  trans-⊩≡∷ (⊩A′ , ⊩t , _ , t≡u) (⊩A , _ , ⊩v , u≡v) =
      ⊩A , irrelevanceTerm (⊩A′ .proj₂) (⊩A .proj₂) ⊩t , ⊩v
    , transEqTerm (⊩A .proj₂) (irrelevanceEqTerm (⊩A′ .proj₂) (⊩A .proj₂) t≡u) u≡v

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- A level well-formedness lemma for _⊩⟨_⟩_.

  wfᵘ-⊩ : Γ ⊩⟨ l ⟩ A → Γ ⊩Level l ∷Level
  wfᵘ-⊩ (⊩l , _) = ⊩l

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A level well-formedness lemma for _⊩⟨_⟩_≡_.

  wfᵘ-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩Level l ∷Level
  wfᵘ-⊩≡ (⊩A , _) = wfᵘ-⊩ ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A level well-formedness lemma for _⊩⟨_⟩_∷_.

  wfᵘ-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩Level l ∷Level
  wfᵘ-⊩∷ (⊩A , _) = wfᵘ-⊩ ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A level well-formedness lemma for _⊩⟨_⟩_≡_∷_.

  wfᵘ-⊩≡∷ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩Level l ∷Level
  wfᵘ-⊩≡∷ (⊩A , _) = wfᵘ-⊩ ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_∷_.

  wf-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ A
  wf-⊩∷ (⊩A , _) = ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_.

  wf-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A × Γ ⊩⟨ l ⟩ B
  wf-⊩≡ (⊩A , ⊩B , _) = ⊩A , ⊩B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_∷_.

  wf-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A
  wf-⊩≡∷ (⊩A , ⊩t , ⊩u , _) = (⊩A , ⊩t) , (⊩A , ⊩u)

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩⇔ : (Γ ⊩⟨ l ⟩ A) ⇔ ∃ λ (⊩l : Γ ⊩Level l ∷Level) → Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ A
  ⊩⇔ = id⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩⇔⊩≡ : (Γ ⊩⟨ l ⟩ A) ⇔ Γ ⊩⟨ l ⟩ A ≡ A
  ⊩⇔⊩≡ = refl-⊩≡ , proj₁ ∘→ wf-⊩≡

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷⇔⊩≡∷ : Γ ⊩⟨ l ⟩ t ∷ A ⇔ Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  ⊩∷⇔⊩≡∷ = refl-⊩≡∷ , proj₁ ∘→ wf-⊩≡∷

------------------------------------------------------------------------
-- Changing type levels

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Changing type levels for _⊩⟨_⟩_≡_.

  level-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  level-⊩≡ ⊩A ⊩B A≡B =
    ⊩A , ⊩B , ⊩≡→⊩≡/ (⊩A .proj₂) A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Changing type levels for _⊩⟨_⟩_≡_∷_.

  level-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  level-⊩≡∷ ⊩A t≡u =
    case wf-⊩≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩A , ⊩∷→⊩∷/ (⊩A .proj₂) ⊩t , ⊩∷→⊩∷/ (⊩A .proj₂) ⊩u , ⊩≡∷→⊩≡∷/ (⊩A .proj₂) t≡u

opaque

  -- Changing type levels for _⊩⟨_⟩_∷_.

  level-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  level-⊩∷ ⊩A =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ level-⊩≡∷ ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Conversion

opaque
  unfolding _⊩⟨_⟩_

  -- Level conversion for _⊩⟨_⟩_.

  level-conv-⊩ :
    Γ ⊩Level l ≡ l′ ∷Level →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ A
  level-conv-⊩ {Γ} {A} l≡l′ (⊩l , ⊩A) =
      wf-⊩Level l≡l′ .proj₂
    , PE.subst (Γ ⊩′⟨_⟩ A) (↑ᵘ-cong ⊩l (wf-⊩Level l≡l′ .proj₂) l≡l′) ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Level conversion for _⊩⟨_⟩_≡_.

  level-conv-⊩≡ :
    Γ ⊩Level l ≡ l′ ∷Level →
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B
  level-conv-⊩≡ l≡l′ (⊩A , ⊩B , A≡B) =
    level-⊩≡ (level-conv-⊩ l≡l′ ⊩A) (level-conv-⊩ l≡l′ ⊩B) (⊩A , ⊩B , A≡B)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Level conversion for _⊩⟨_⟩_∷_.

  level-conv-⊩∷ :
    Γ ⊩Level l ≡ l′ ∷Level →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A
  level-conv-⊩∷ l≡l′ (⊩A , ⊩t) =
    level-⊩∷ (level-conv-⊩ l≡l′ ⊩A) (⊩A , ⊩t)

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Level conversion for _⊩⟨_⟩_≡_∷_.

  level-conv-⊩≡∷ :
    Γ ⊩Level l ≡ l′ ∷Level →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A
  level-conv-⊩≡∷ l≡l′ (⊩A , ⊩t , ⊩u , t≡u) =
    level-⊩≡∷ (level-conv-⊩ l≡l′ ⊩A) (⊩A , ⊩t , ⊩u , t≡u)

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- Conversion for _⊩⟨_⟩_≡_∷_.

  conv-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ B
  conv-⊩≡∷ (⊩A , ⊩B , A≡B) (⊩A′ , ⊩t , ⊩u , t≡u) =
    case irrelevanceEq (⊩A .proj₂) (⊩A′ .proj₂) A≡B of λ
      A≡B →
      ⊩B , convTerm₁ (⊩A′ .proj₂) (⊩B .proj₂) A≡B ⊩t , convTerm₁ (⊩A′ .proj₂) (⊩B .proj₂) A≡B ⊩u
    , convEqTerm₁ (⊩A′ .proj₂) (⊩B .proj₂) A≡B t≡u

opaque

  -- Conversion for _⊩⟨_⟩_∷_.

  conv-⊩∷ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ B
  conv-⊩∷ A≡B =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ conv-⊩≡∷ A≡B ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Weakening

opaque
  unfolding _⊩⟨_⟩_

  -- Weakening for _⊩⟨_⟩_.

  wk-⊩ : ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ wk ρ l ⟩ wk ρ A
  wk-⊩ {ρ} {Δ} {A} [ρ] (⊩l , ⊩A) =
      W.wkTermLevel [ρ] ⊩l
    , PE.subst (Δ ⊩′⟨_⟩ wk ρ A) (PE.sym (W.wk-↑ᵘ [ρ] ⊩l (W.wkTermLevel [ρ] ⊩l)))
        (W.wk [ρ] ⊩A)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Weakening for _⊩⟨_⟩_≡_.

  wk-⊩≡ : ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ A ≡ B → Δ ⊩⟨ wk ρ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩≡ Δ⊇Γ (⊩A , ⊩B , A≡B) =
      wk-⊩ Δ⊇Γ ⊩A
    , wk-⊩ Δ⊇Γ ⊩B
    , irrelevanceEq (W.wk Δ⊇Γ (⊩A .proj₂)) (wk-⊩ Δ⊇Γ ⊩A .proj₂)
        (W.wkEq Δ⊇Γ (⊩A .proj₂) A≡B)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Weakening for _⊩⟨_⟩_∷_.

  wk-⊩∷ : ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ t ∷ A → Δ ⊩⟨ wk ρ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩∷ Δ⊇Γ (⊩A , ⊩t) =
      wk-⊩ Δ⊇Γ ⊩A
    , irrelevanceTerm (W.wk Δ⊇Γ (⊩A .proj₂)) (wk-⊩ Δ⊇Γ ⊩A .proj₂)
        (W.wkTerm Δ⊇Γ (⊩A .proj₂) ⊩t)

opaque
  unfolding _⊩⟨_⟩_≡_∷_ wk-⊩∷

  -- Weakening for _⊩⟨_⟩_≡_∷_.

  wk-⊩≡∷ :
    ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Δ ⊩⟨ wk ρ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩≡∷ Δ⊇Γ (⊩A , ⊩t , ⊩u , t≡u) =
      wk-⊩ Δ⊇Γ ⊩A
    , wk-⊩∷ Δ⊇Γ (⊩A , ⊩t) .proj₂
    , wk-⊩∷ Δ⊇Γ (⊩A , ⊩u) .proj₂
    , irrelevanceEqTerm (W.wk Δ⊇Γ (⊩A .proj₂)) (wk-⊩ Δ⊇Γ ⊩A .proj₂)
        (W.wkEqTerm Δ⊇Γ (⊩A .proj₂) t≡u)

------------------------------------------------------------------------
-- Reduction

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- A reduction lemma for _⊩⟨_⟩_.

  ⊩-⇒* : Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇒* A⇒*B ⊩A =
    case redSubst*′ A⇒*B (⊩A .proj₂) of λ
      (⊩B , A≡B) →
    ⊩A , (⊩A .proj₁ , ⊩B) , A≡B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A reduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-⇒* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇒* t⇒*u (⊩A , ⊩t) =
    ⊩A , ⊩t , redSubst*Term′ t⇒*u (⊩A .proj₂) ⊩t

------------------------------------------------------------------------
-- Expansion

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- An expansion lemma for _⊩⟨_⟩_.

  ⊩-⇐* : Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ B → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇐* A⇒*B ⊩B =
    case redSubst* A⇒*B (⊩B .proj₂) of λ
      (⊩A , A≡B) →
    (⊩B .proj₁ , ⊩A) , ⊩B , A≡B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- An expansion lemma for _⊩⟨_⟩_∷_.

  ⊩∷-⇐* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇐* t⇒*u (⊩A , ⊩u) =
    case redSubst*Term t⇒*u (⊩A .proj₂) ⊩u of λ
      (⊩t , t≡u) →
    ⊩A , ⊩t , ⊩u , t≡u

------------------------------------------------------------------------
-- Escape lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- An escape lemma for _⊩⟨_⟩_.

  escape-⊩ : Γ ⊩⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ (⊩l , ⊩A) = escape ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_

  -- An escape lemma for _⊩⟨_⟩_∷_.

  escape-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩∷ (⊩A , ⊩t) = escapeTerm (⊩A .proj₂) ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An escape lemma for _⊩⟨_⟩_≡_.

  escape-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩≡ (⊩A , _ , A≡B) = escapeEq (⊩A .proj₂) A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- An escape lemma for _⊩⟨_⟩_≡_∷_.

  escape-⊩≡∷ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩≡∷ (⊩A , _ , _ , t≡u) = escapeTermEq (⊩A .proj₂) t≡u

------------------------------------------------------------------------
-- Equational reasoning combinators

-- For more explanations of the combinators, see
-- Definition.Typed.Reasoning.Reduction.

opaque

  -- Equational reasoning combinators for _⊩Level_≡_∷Level.

  infix -1
    finally-⊩Level≡
  infixr -2
    step-⊩Level≡ step-⊩Level≡≡ finally-⊩Level≡≡

  step-⊩Level≡ : ∀ t → Γ ⊩Level u ≡ v ∷Level → Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ≡ v ∷Level
  step-⊩Level≡ _ = flip transEqTermLevel

  syntax step-⊩Level≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩Level u≡v

  step-⊩Level≡≡ : ∀ t → Γ ⊩Level u ≡ v ∷Level → t PE.≡ u → Γ ⊩Level t ≡ v ∷Level
  step-⊩Level≡≡ _ u≡v PE.refl = u≡v

  syntax step-⊩Level≡≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩Level≡ u≡v

  finally-⊩Level≡ : ∀ t u → Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ≡ u ∷Level
  finally-⊩Level≡ _ _ t≡u = t≡u

  syntax finally-⊩Level≡ t u t≡u = t ≡⟨ t≡u ⟩⊩Level∎ u ∎

  finally-⊩Level≡≡ : ∀ t → u PE.≡ v → Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ≡ v ∷Level
  finally-⊩Level≡≡ _ PE.refl t≡u = t≡u

  syntax finally-⊩Level≡≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩Level∎≡ u≡v

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_.

  infix -1
    _∎⟨_⟩⊩ finally-⊩≡ finally-⊩≡˘
  infixr -2
    step-⊩≡ step-⊩≡˘ step-⊩≡≡ step-⊩≡≡˘ step-⊩≡⇒* step-⊩≡⇒ step-⊩≡⇐*
    step-⊩≡⇐ _≡⟨⟩⊩_ finally-⊩≡≡ finally-⊩≡≡˘ finally-⊩≡⇐* finally-⊩≡⇒*

  step-⊩≡ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡ _ = flip trans-⊩≡

  syntax step-⊩≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩ B≡C

  step-⊩≡˘ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡˘ _ B≡C B≡A = trans-⊩≡ (sym-⊩≡ B≡A) B≡C

  syntax step-⊩≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩ B≡C

  step-⊩≡≡ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → A PE.≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡≡ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩≡ B≡C

  step-⊩≡≡˘ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → B PE.≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡≡˘ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩≡ B≡C

  step-⊩≡⇒* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇒* _ B≡C A⇒*B =
    trans-⊩≡ (⊩-⇐* A⇒*B (wf-⊩≡ B≡C .proj₁)) B≡C

  syntax step-⊩≡⇒* A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊩ B≡C

  step-⊩≡⇒ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ A ⇒ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇒ _ B≡C A⇒B = step-⊩≡⇒* _ B≡C (redMany-⊢ A⇒B)

  syntax step-⊩≡⇒ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊩ B≡C

  step-⊩≡⇐* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B ⇒* A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐* _ B≡C B⇒*A =
    trans-⊩≡ (sym-⊩≡ (⊩-⇒* B⇒*A (wf-⊩≡ B≡C .proj₁))) B≡C

  syntax step-⊩≡⇐* A B≡C B⇒*A = A ⇐*⟨ B⇒*A ⟩⊩ B≡C

  step-⊩≡⇐ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B ⇒ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐ _ B≡C B⇒A = step-⊩≡⇐* _ B≡C (redMany-⊢ B⇒A)

  syntax step-⊩≡⇐ A B≡C B⇒A = A ⇐⟨ B⇒A ⟩⊩ B≡C

  _≡⟨⟩⊩_ : ∀ A → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  _ ≡⟨⟩⊩ A≡B = A≡B

  _∎⟨_⟩⊩ : ∀ A → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A ≡ A
  _ ∎⟨ ⊩A ⟩⊩ = refl-⊩≡ ⊩A

  finally-⊩≡ : ∀ A B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  finally-⊩≡ _ _ A≡B = A≡B

  syntax finally-⊩≡ A B A≡B = A ≡⟨ A≡B ⟩⊩∎ B ∎

  finally-⊩≡˘ : ∀ A B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ B
  finally-⊩≡˘ _ _ A≡B = sym-⊩≡ A≡B

  syntax finally-⊩≡˘ A B B≡A = A ≡˘⟨ B≡A ⟩⊩∎ B ∎

  finally-⊩≡≡ : ∀ A → B PE.≡ C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡≡ _ PE.refl A≡B = A≡B

  syntax finally-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩∎≡ B≡C

  finally-⊩≡≡˘ : ∀ A → B PE.≡ C → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡≡˘ _ PE.refl B≡A = sym-⊩≡ B≡A

  syntax finally-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩∎≡ B≡C

  finally-⊩≡⇐* :
    ∀ A → Γ ⊢ C ⇒* B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡⇐* _ C⇒*B A≡B =
    trans-⊩≡ A≡B (sym-⊩≡ (⊩-⇐* C⇒*B (wf-⊩≡ A≡B .proj₂)))

  syntax finally-⊩≡⇐* A C⇒*B A≡B = A ≡⟨ A≡B ⟩⊩⇐* C⇒*B

  finally-⊩≡⇒* :
    ∀ A → Γ ⊢ B ⇒* C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡⇒* _ B⇒*C A≡B =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    trans-⊩≡ A≡B (⊩-⇒* B⇒*C ⊩B)

  syntax finally-⊩≡⇒* A B⇒*C A≡B = A ≡⟨ A≡B ⟩⊩⇒* B⇒*C

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_.

  infix -1
    _∎⟨_⟩⊩∷ finally-⊩≡∷ finally-⊩≡∷˘
  infix -2
    step-⊩≡∷-conv step-⊩≡∷-conv˘ step-⊩≡∷-conv-≡ step-⊩≡∷-conv-≡˘
  infixr -2
    step-⊩≡∷ step-⊩≡∷˘ step-⊩≡∷≡ step-⊩≡∷≡˘ step-⊩≡∷⇒* step-⊩≡∷⇒
    step-⊩≡∷⇐* step-⊩≡∷⇐ _≡⟨⟩⊩∷_ finally-⊩≡∷≡ finally-⊩≡∷≡˘
    finally-⊩≡∷⇐* finally-⊩≡∷⇒*

  step-⊩≡∷ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷ _ = flip trans-⊩≡∷

  syntax step-⊩≡∷ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷ u≡v

  step-⊩≡∷˘ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷˘ _ u≡v u≡t = trans-⊩≡∷ (sym-⊩≡∷ u≡t) u≡v

  syntax step-⊩≡∷˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷ u≡v

  step-⊩≡∷≡ : ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷≡ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷≡ u≡v

  step-⊩≡∷≡˘ : ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷≡˘ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷≡ u≡v

  step-⊩≡∷⇒* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇒* _ u≡v t⇒*u =
    trans-⊩≡∷ (⊩∷-⇐* t⇒*u (wf-⊩≡∷ u≡v .proj₁)) u≡v

  syntax step-⊩≡∷⇒* t u≡v t⇒*u = t ⇒*⟨ t⇒*u ⟩⊩∷ u≡v

  step-⊩≡∷⇒ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇒ _ u≡v t⇒u = step-⊩≡∷⇒* _ u≡v (redMany t⇒u)

  syntax step-⊩≡∷⇒ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩⊩∷ u≡v

  step-⊩≡∷⇐* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒* t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐* _ u≡v u⇒*t =
    trans-⊩≡∷ (sym-⊩≡∷ (⊩∷-⇒* u⇒*t (wf-⊩≡∷ u≡v .proj₁))) u≡v

  syntax step-⊩≡∷⇐* t u≡v u⇒*t = t ⇐*⟨ u⇒*t ⟩⊩∷ u≡v

  step-⊩≡∷⇐ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐ _ u≡v u⇒t = step-⊩≡∷⇐* _ u≡v (redMany u⇒t)

  syntax step-⊩≡∷⇐ t u≡v u⇒t = t ⇐⟨ u⇒t ⟩⊩∷ u≡v

  _≡⟨⟩⊩∷_ : ∀ t → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  _ ≡⟨⟩⊩∷ t≡u = t≡u

  step-⊩≡∷-conv :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv t≡u A≡B = conv-⊩≡∷ (sym-⊩≡ A≡B) t≡u

  syntax step-⊩≡∷-conv t≡u A≡B = ⟨ A≡B ⟩⊩∷ t≡u

  step-⊩≡∷-conv˘ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv˘ t≡u B≡A = conv-⊩≡∷ B≡A t≡u

  syntax step-⊩≡∷-conv˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷ t≡u

  step-⊩≡∷-conv-≡ : Γ ⊩⟨ l ⟩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡ t≡u A≡B = ⟨ A≡B ⟩⊩∷≡ t≡u

  step-⊩≡∷-conv-≡˘ : Γ ⊩⟨ l ⟩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡˘ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷≡ t≡u

  _∎⟨_⟩⊩∷ : ∀ t → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  _ ∎⟨ ⊩t ⟩⊩∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷ : ∀ t u → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷ _ _ t≡u = t≡u

  syntax finally-⊩≡∷ t u t≡u = t ≡⟨ t≡u ⟩⊩∷∎ u ∎

  finally-⊩≡∷˘ : ∀ t u → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷˘ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷˘ t u u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎ u ∎

  finally-⊩≡∷≡ :
    ∀ t → u PE.≡ v → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷≡ _ PE.refl t≡u = t≡u

  syntax finally-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷≡˘ :
    ∀ t → u PE.≡ v → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷≡˘ _ PE.refl u≡t = sym-⊩≡∷ u≡t

  syntax finally-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷⇐* :
    ∀ t → Γ ⊢ v ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷⇐* _ v⇒*u t≡u =
    trans-⊩≡∷ t≡u (sym-⊩≡∷ (⊩∷-⇐* v⇒*u (wf-⊩≡∷ t≡u .proj₂)))

  syntax finally-⊩≡∷⇐* t v⇒*u t≡u = t ≡⟨ t≡u ⟩⊩∷⇐* v⇒*u

  finally-⊩≡∷⇒* :
    ∀ t → Γ ⊢ u ⇒* v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷⇒* _ u⇒*v t≡u =
    case wf-⊩≡∷ t≡u of λ
      (_ , ⊩u) →
    trans-⊩≡∷ t≡u (⊩∷-⇒* u⇒*v ⊩u)

  syntax finally-⊩≡∷⇒* t u⇒*v t≡u = t ≡⟨ t≡u ⟩⊩∷⇒* u⇒*v

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_ with explicit
  -- types.

  infix -1
    _∷_∎⟨_⟩⊩∷∷ finally-⊩≡∷∷ finally-⊩≡∷∷˘
  infix -2
    step-⊩≡∷∷-conv step-⊩≡∷∷-conv˘ step-⊩≡∷∷-conv-≡ step-⊩≡∷∷-conv-≡˘
  infixr -2
    step-⊩≡∷∷ step-⊩≡∷∷˘ step-⊩≡∷∷≡ step-⊩≡∷∷≡˘ step-⊩≡∷∷⇒* step-⊩≡∷∷⇒
    step-⊩≡∷∷⇐* step-⊩≡∷∷⇐ _∷_≡⟨⟩⊩∷∷_ finally-⊩≡∷∷≡ finally-⊩≡∷∷≡˘
    finally-⊩≡∷∷⇐* finally-⊩≡∷∷⇒*

  step-⊩≡∷∷ :
    ∀ t A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷ _ _ = step-⊩≡∷ _

  syntax step-⊩≡∷∷ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷˘ :
    ∀ t A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷˘ _ _ = step-⊩≡∷˘ _

  syntax step-⊩≡∷∷˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷≡ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷≡ _ _ = step-⊩≡∷≡ _

  syntax step-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷≡˘ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷≡˘ _ _ = step-⊩≡∷≡˘ _

  syntax step-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷⇒* :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇒* _ _ = step-⊩≡∷⇒* _

  syntax step-⊩≡∷∷⇒* t A u≡v t⇒*u = t ∷ A ⇒*⟨ t⇒*u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇒ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇒ _ _ = step-⊩≡∷⇒ _

  syntax step-⊩≡∷∷⇒ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒* t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐* _ _ = step-⊩≡∷⇐* _

  syntax step-⊩≡∷∷⇐* t A u≡v u⇒*t = t ∷ A ⇐*⟨ u⇒*t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐ _ _ = step-⊩≡∷⇐ _

  syntax step-⊩≡∷∷⇐ t A u≡v u⇒t = t ∷ A ⇐⟨ u⇒t ⟩⊩∷∷ u≡v

  _∷_≡⟨⟩⊩∷∷_ : ∀ t A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  _ ∷ _ ≡⟨⟩⊩∷∷ t≡u = t≡u

  step-⊩≡∷∷-conv :
    ∀ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv _ = step-⊩≡∷-conv

  syntax step-⊩≡∷∷-conv A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv˘ :
    ∀ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv˘ _ = step-⊩≡∷-conv˘

  syntax step-⊩≡∷∷-conv˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv-≡ :
    ∀ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡ _ = step-⊩≡∷-conv-≡

  syntax step-⊩≡∷∷-conv-≡ A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷≡ t≡u

  step-⊩≡∷∷-conv-≡˘ :
    ∀ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡˘ _ = step-⊩≡∷-conv-≡˘

  syntax step-⊩≡∷∷-conv-≡˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷≡ t≡u

  _∷_∎⟨_⟩⊩∷∷ : ∀ t A → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  _ ∷ _ ∎⟨ ⊩t ⟩⊩∷∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷∷ : ∀ t A u → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷∷ _ _ _ t≡u = t≡u

  syntax finally-⊩≡∷∷ t A u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷˘ : ∀ t A u → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷∷˘ _ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷∷˘ t A u u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷≡ :
    ∀ t A → u PE.≡ v → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷≡ _ _ = finally-⊩≡∷≡ _

  syntax finally-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷≡˘ :
    ∀ t A → u PE.≡ v → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷≡˘ _ _ = finally-⊩≡∷≡˘ _

  syntax finally-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊢ v ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷⇐* _ _ = finally-⊩≡∷⇐* _

  syntax finally-⊩≡∷∷⇐* t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷⇐* v⇒*u

  finally-⊩≡∷∷⇒* :
    ∀ t A → Γ ⊢ u ⇒* v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷⇒* _ _ = finally-⊩≡∷⇒* _

  syntax finally-⊩≡∷∷⇒* t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷⇒* v⇒*u

------------------------------------------------------------------------
-- Embedding

opaque
  unfolding _⊩_≤_∷Level _⊩⟨_⟩_

  -- Embedding for _⊩⟨_⟩_.

  emb-⊩ :
    Γ ⊩ l ≤ l′ ∷Level →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ A
  emb-⊩ (⊩l , ⊩l′ , l<l′) (⊩′l , ⊩A) =
      ⊩l′
    , emb-≤-⊩ (PE.subst (_≤ᵘ ↑ᵘ ⊩l′) (↑ᵘ-irrelevance ⊩l ⊩′l) l<l′)
        ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_ emb-⊩

  -- Embedding for _⊩⟨_⟩_≡_.

  emb-⊩≡ :
    Γ ⊩ l ≤ l′ ∷Level →
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B
  emb-⊩≡ p (⊩A , ⊩B , A≡B) = emb-⊩ p ⊩A , emb-⊩ p ⊩B , emb-≤-⊩≡ A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_ emb-⊩

  -- Embedding for _⊩⟨_⟩_≡_∷_.

  emb-⊩≡∷ :
    Γ ⊩ l ≤ l′ ∷Level →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A
  emb-⊩≡∷ p (⊩A , ⊩t , ⊩u , t≡u) =
      emb-⊩ p ⊩A
    , emb-≤-⊩∷ ⊩t
    , emb-≤-⊩∷ ⊩u
    , emb-≤-⊩≡∷ t≡u

opaque

  -- Embedding for _⊩⟨_⟩_∷_.

  emb-⊩∷ :
    Γ ⊩ l ≤ l′ ∷Level →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A
  emb-⊩∷ l≤l′ =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ emb-⊩≡∷ l≤l′ ∘→ ⊩∷⇔⊩≡∷ .proj₁

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Heterogeneous transitivity for _⊩⟨_⟩_≡_.

  trans′-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ B ≡ C →
    Γ ⊩⟨ l maxᵘ l′ ⟩ A ≡ C
  trans′-⊩≡ (⊩A , _ , A≡B) (⊩B , ⊩C , B≡C) =
    let ⊩A′ = emb-⊩ {!   !} ⊩A
        ⊩C′ = emb-⊩ {!   !} ⊩C
    in ⊩A′ , ⊩C′ , transEq (⊩A′ .proj₂) (⊩B .proj₂) (⊩C′ .proj₂)
      (irrelevanceEq (⊩A .proj₂) (⊩A′ .proj₂) A≡B) B≡C

------------------------------------------------------------------------
-- Some introduction lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- An introduction lemma for _⊩⟨_⟩_.

  ⊩-intro :
    (⊩l : Γ ⊩Level l ∷Level) →
    Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ A →
    Γ ⊩⟨ l ⟩ A
  ⊩-intro ⊩l ⊩A = ⊩l , ⊩A

opaque

  -- Another introduction lemma for _⊩⟨_⟩_.

  ⊩-intro-< :
    {⊩l : Γ ⊩Level l ∷Level} →
    (p : ↑ᵘ ⊩l <ᵘ ℓ) →
    Γ ⊩<⟨ p ⟩ A →
    Γ ⊩⟨ l ⟩ A
  ⊩-intro-< {⊩l} p ⊩A = ⊩-intro ⊩l (⊩<⇔⊩ p .proj₁ ⊩A)

opaque

  -- Another introduction lemma for _⊩⟨_⟩_.

  ⊩-intro-wk :
    ∀ {ρ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ) {⊩l : Γ ⊩Level l ∷Level} →
    Δ ⊩′⟨ ↑ᵘ ⊩l ⟩ A →
    Δ ⊩⟨ wk ρ l ⟩ A
  ⊩-intro-wk [ρ] {⊩l} ⊩A = ⊩-intro (W.wkTermLevel [ρ] ⊩l)
    (PE.subst (_ ⊩′⟨_⟩ _) (PE.sym $ W.wk-↑ᵘ [ρ] ⊩l _) ⊩A)

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩-intro

  -- An introduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-intro :
    (⊩l : Γ ⊩Level l ∷Level) →
    (⊩A : Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ A) →
    Γ ⊩⟨ ↑ᵘ ⊩l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ∷ A
  ⊩∷-intro ⊩l ⊩A ⊩t = ⊩-intro ⊩l ⊩A , ⊩t

opaque

  -- Another introduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-intro-wk :
    ∀ {ρ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ) {⊩l : Γ ⊩Level l ∷Level} →
    (⊩A : Δ ⊩′⟨ ↑ᵘ ⊩l ⟩ A) →
    Δ ⊩⟨ ↑ᵘ ⊩l ⟩ t ∷ A / ⊩A →
    Δ ⊩⟨ wk ρ l ⟩ t ∷ A
  ⊩∷-intro-wk [ρ] {⊩l} ⊩A ⊩t =
    let ⊩A′ = PE.subst (_ ⊩′⟨_⟩ _) (PE.sym $ W.wk-↑ᵘ [ρ] ⊩l _) ⊩A
    in ⊩∷-intro (W.wkTermLevel [ρ] ⊩l) ⊩A′
      (irrelevanceTerm ⊩A ⊩A′ ⊩t)

opaque
  unfolding _⊩⟨_⟩_≡_ ⊩-intro

  -- An introduction lemma for _⊩⟨_⟩_≡_.

  ⊩≡-intro :
    (⊩l : Γ ⊩Level l ∷Level) →
    (⊩A : Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ A) →
    Γ ⊩′⟨ ↑ᵘ ⊩l ⟩ B →
    Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l ⟩ A ≡ B
  ⊩≡-intro ⊩l ⊩A ⊩B A≡B = ⊩-intro ⊩l ⊩A , ⊩-intro ⊩l ⊩B , A≡B

opaque

  -- Another introduction lemma for _⊩⟨_⟩_≡_.

  ⊩≡-intro-< :
    {⊩l : Γ ⊩Level l ∷Level} →
    (p : ↑ᵘ ⊩l <ᵘ ℓ) →
    (⊩A : Γ ⊩<⟨ p ⟩ A) →
    Γ ⊩<⟨ p ⟩ B →
    Γ ⊩<⟨ p ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l ⟩ A ≡ B
  ⊩≡-intro-< {⊩l} p ⊩A ⊩B A≡B = ⊩≡-intro ⊩l (⊩<⇔⊩ p .proj₁ ⊩A) (⊩<⇔⊩ p .proj₁ ⊩B) (⊩<≡⇔⊩≡ p .proj₁ A≡B)

opaque

  -- Another introduction lemma for _⊩⟨_⟩_≡_.

  ⊩≡-intro-wk :
    ∀ {ρ} ([ρ] : ρ ∷ʷ Δ ⊇ Γ) {⊩l : Γ ⊩Level l ∷Level} →
    (⊩A : Δ ⊩′⟨ ↑ᵘ ⊩l ⟩ A) →
    Δ ⊩′⟨ ↑ᵘ ⊩l ⟩ B →
    Δ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B / ⊩A →
    Δ ⊩⟨ wk ρ l ⟩ A ≡ B
  ⊩≡-intro-wk [ρ] {⊩l} ⊩A ⊩B A≡B =
    let ⊩A′ = PE.subst (_ ⊩′⟨_⟩ _) (PE.sym $ W.wk-↑ᵘ [ρ] ⊩l _) ⊩A
        ⊩B′ = PE.subst (_ ⊩′⟨_⟩ _) (PE.sym $ W.wk-↑ᵘ [ρ] ⊩l _) ⊩B
    in ⊩≡-intro (W.wkTermLevel [ρ] ⊩l) ⊩A′ ⊩B′
      (irrelevanceEq ⊩A ⊩A′ A≡B)

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩⇔

  -- An introduction lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ ↑ᵘ ⊩⇔ .proj₁ ⊩A .proj₁ ⟩ t ≡ u ∷ A / ⊩⇔ .proj₁ ⊩A .proj₂ →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩≡∷-intro ⊩A ⊩t ⊩u t≡u =
    ⊩A , ⊩∷→⊩∷/ (⊩A .proj₂) ⊩t , ⊩∷→⊩∷/ (⊩A .proj₂) ⊩u , t≡u

------------------------------------------------------------------------
-- Neutral types and terms

opaque

  -- Neutral types that satisfy certain properties are reducible.

  neutral-⊩ :
    Γ ⊩Level l ∷Level →
    Neutral A →
    Γ ⊢≅ A →
    Γ ⊩⟨ l ⟩ A
  neutral-⊩ ⊩l neA ⊢≅A = ⊩-intro ⊩l (neu neA ⊢≅A)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Neutral terms that satisfy certain properties are reducible.

  neutral-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutral t →
    Γ ⊢~ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  neutral-⊩∷ ⊩A t-ne t~t =
    ⊩A , neuTerm (⊩A .proj₂) t-ne t~t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reducible equality holds between neutral types that satisfy
  -- certain properties.

  neutral-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Neutral A →
    Neutral B →
    Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  neutral-⊩≡ ⊩A ⊩B A-ne B-ne A≅B =
    ⊩A , ⊩B , neuEq (⊩A .proj₂) A-ne B-ne A≅B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Reducible equality holds between neutral terms that satisfy
  -- certain properties.

  neutral-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutral t →
    Neutral u →
    Γ ⊢ t ~ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  neutral-⊩≡∷ ⊩A t-ne u-ne t~u =
    let ~t , ~u = wf-⊢~∷ t~u in
      ⊩A
    , neuTerm (⊩A .proj₂) t-ne ~t
    , neuTerm (⊩A .proj₂) u-ne ~u
    , neuEqTerm (⊩A .proj₂) t-ne u-ne t~u

opaque
  unfolding _⊩⟨_⟩_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ne⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ A ⇔ (Γ ⊩Level l ∷Level × Γ ⊢≅ A)
  ⊩ne⇔ A-ne =
      (λ ⊩A →
         case ne-elim A-ne (⊩A .proj₂) of λ {
           (ne (ne B A⇒*B _ B≅B)) →
         case whnfRed* A⇒*B (ne A-ne) of λ {
           PE.refl →
         ⊩A .proj₁ , B≅B }})
    , (λ (⊩l , A≅A) → neutral-⊩ ⊩l A-ne A≅A)

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩ne⇔ neutral-⊩ ⊩-intro neu

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷ne⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ t ∷ A ⇔
    (Γ ⊩Level l ∷Level × Γ ⊢≅ A × ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Neutral u × Γ ⊢~ u ∷ A)
  ⊩∷ne⇔ {A} A-ne =
      (λ ((⊩l , ⊩A) , ⊩t) →
        case ne-elim A-ne ⊩A of λ {
          (ne (ne _ A⇒*A′ _ _)) →
        case whnfRed* A⇒*A′ (ne A-ne) of λ {
          PE.refl →
        case ⊩t of λ
          (neₜ u t⇒*u (neNfₜ u-ne u~u)) →
        ⊩l ,
        ⊩ne⇔ A-ne .proj₁ (⊩l , ⊩A) .proj₂ ,
        u , t⇒*u , u-ne ,  u~u } })
    , (λ (⊩l , ≅A , u , t⇒*u , u-ne , u~u) →
          ⊩ne⇔ A-ne .proj₂ (⊩l , ≅A)
         , neₜ u t⇒*u (neNfₜ u-ne u~u))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ne≡⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ A ≡ B ⇔
    (Γ ⊩Level l ∷Level × ∃ λ C → Neutral C × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)
  ⊩ne≡⇔ {A} {B} A-ne =
      (λ ((⊩l , ⊩A) , ⊩B , A≡B) →
        case ne-elim A-ne ⊩A of λ {
          (ne (ne _ A⇒*A′ _ _)) →
        case whnfRed* A⇒*A′ (ne A-ne) of λ {
          PE.refl →
        case A≡B of λ
          (ne₌ C B⇒*C C-ne A′≅C) →
        ⊩l , C , C-ne , B⇒*C , A′≅C }})
    , (λ (⊩l , C , C-ne , B⇒*C , A≅C) →
         let ≅A , ≅C = wf-⊢≅ A≅C in
         sym-⊩≡
           (B  ⇒*⟨ B⇒*C ⟩⊩
            C  ≡⟨ neutral-⊩≡ (⊩ne⇔ C-ne .proj₂ (⊩l , ≅C)) (⊩ne⇔ A-ne .proj₂ (⊩l , ≅A))
                    C-ne A-ne (≅-sym A≅C) ⟩⊩∎
            A  ∎))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ne≡ne⇔ :
    Neutral A →
    Neutral B →
    Γ ⊩⟨ l ⟩ A ≡ B ⇔ (Γ ⊩Level l ∷Level × Γ ⊢ A ≅ B)
  ⊩ne≡ne⇔ {A} {B} {Γ} {l} A-ne B-ne =
    Γ ⊩⟨ l ⟩ A ≡ B                                ⇔⟨ ⊩ne≡⇔ A-ne ⟩
    (Γ ⊩Level l ∷Level × ∃ λ C → Neutral C × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)  ⇔⟨ id⇔ ×-cong-⇔ ((λ (_ , _ , B⇒*C , A≅C) →
                                                        case whnfRed* B⇒*C (ne B-ne) of λ {
                                                          PE.refl →
                                                        A≅C })
                                                   , (λ A≅B → _ , B-ne , id (wf-⊢≡ (≅-eq A≅B) .proj₂) , A≅B))
                                                   ⟩
    Γ ⊩Level l ∷Level × Γ ⊢ A ≅ B                                     □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩ne⇔ neutral-⊩ ⊩-intro neu

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷ne⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A ⇔
    (Γ ⊩Level l ∷Level ×
     Γ ⊢≅ A ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ ⇒* u₁ ∷ A × Γ ⊢ t₂ ⇒* u₂ ∷ A ×
     Γ ⊩neNf u₁ ≡ u₂ ∷ A)
  ⊩≡∷ne⇔ {A} {Γ} {l} A-ne =
      (λ ((⊩l , ⊩A) , _ , _ , t₁≡t₂) →
          case ne-elim A-ne ⊩A of λ {
          (ne (ne _ A⇒*A′ _ _)) →
        case t₁≡t₂ of λ
          (neₜ₌ u₁ u₂ t₁⇒*u₁ t₂⇒*u₂ u₁≡u₂) →
        case whnfRed* A⇒*A′ (ne A-ne) of λ {
          PE.refl →
        ⊩l ,
        ⊩ne⇔ A-ne .proj₁ (⊩l , ⊩A) .proj₂ ,
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≡u₂ }})
    , (λ (⊩l , ≅A , u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ ,
          u₁≡u₂@(neNfₜ₌ u₁-ne u₂-ne u₁~u₂)) →
         let ⊩A′       = ⊩ne⇔ A-ne .proj₂ (⊩l , ≅A)
             ~u₁ , ~u₂ = wf-⊢~∷ u₁~u₂
         in
           ⊩A′
        , ⊩∷→⊩∷/ (⊩A′ .proj₂)
            (⊩∷ne⇔ A-ne .proj₂ (⊩l , ≅A , u₁ , t₁⇒*u₁ , u₁-ne , ~u₁))
        , ⊩∷→⊩∷/ (⊩A′ .proj₂)
            (⊩∷ne⇔ A-ne .proj₂ (⊩l , ≅A , u₂ , t₂⇒*u₂ , u₂-ne , ~u₂))
        , neₜ₌ u₁ u₂ t₁⇒*u₁ t₂⇒*u₂ u₁≡u₂)
