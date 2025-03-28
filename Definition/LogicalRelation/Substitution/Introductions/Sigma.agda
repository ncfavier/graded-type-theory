------------------------------------------------------------------------
-- Validity for Σ-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module
  Definition.LogicalRelation.Substitution.Introductions.Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open Type-restrictions R

open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.Sigma.Strong R
open import
  Definition.LogicalRelation.Substitution.Introductions.Sigma.Weak R

open import Definition.Untyped M

private variable
  Γ                   : Con Term _
  A B l l′ l″ t t₁ t₂ u u₁ u₂ : Term _
  p q                 : M
  s                   : Strength

opaque

  -- Reducibility of equality between applications of prod.

  ⊩prod≡prod :
    Γ ⊩⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩⟨ l ⟩ prod s p t₁ u₁ ≡ prod s p t₂ u₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
  ⊩prod≡prod {s = 𝕨} = ⊩prodʷ≡prodʷ
  ⊩prod≡prod {s = 𝕤} = ⊩prodˢ≡prodˢ

opaque

  -- Validity of equality preservation for prod.

  prod-congᵛ :
    Σ-allowed s p q →
    Γ ∙ A ⊩ᵛ⟨ wk1 l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ prod s p t₁ u₁ ≡ prod s p t₂ u₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
  prod-congᵛ {s = 𝕨} = prodʷ-congᵛ
  prod-congᵛ {s = 𝕤} = prodˢ-congᵛ

opaque

  -- Validity of prod.

  prodᵛ :
    Σ-allowed s p q →
    Γ ∙ A ⊩ᵛ⟨ wk1 l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
  prodᵛ {s = 𝕨} = prodʷᵛ
  prodᵛ {s = 𝕤} = prodˢᵛ
