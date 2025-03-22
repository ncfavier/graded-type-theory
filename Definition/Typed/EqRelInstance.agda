------------------------------------------------------------------------
-- The typing relation is an instance of the abstract set of
-- equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.EqRelInstance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.EqualityRelation R

open import Tools.Function
open import Tools.Product

private opaque

  -- A lemma used below.

  equality-relations : Equality-relations _⊢_≡_ _⊢_≡_∷_ _⊢_≡_∷_
  equality-relations = λ where
      .~-to-≅ₜ      → idᶠ
      .≅-eq         → idᶠ
      .≅ₜ-eq        → idᶠ
      .≅-univ       → univ
      .≅-sym        → sym
      .≅ₜ-sym       → sym′
      .~-sym        → sym′
      .≅-trans      → trans
      .≅ₜ-trans     → trans
      .~-trans      → trans
      .≅-conv       → conv
      .~-conv       → conv
      .≅-wk         → wkEq
      .≅ₜ-wk        → wkEqTerm
      .~-wk         → wkEqTerm
      .≅-red        → λ (A⇒* , _) (B⇒* , _) → reduction A⇒* B⇒*
      .≅ₜ-red       → λ (A⇒* , _) (t⇒* , _) (u⇒* , _) →
                        reductionₜ A⇒* t⇒* u⇒*
      .≅-Levelrefl  → refl ∘ᶠ Levelⱼ
      .≅ₜ-zeroᵘrefl → refl ∘ᶠ zeroᵘⱼ
      .≅ₜ-sucᵘ-cong → sucᵘ-cong
      .≅ₜ-maxᵘ-congˡ → maxᵘ-cong
      .≅ₜ-maxᵘ-congʳ → λ t₁≡t₂ u₁≡u₂ → maxᵘ-cong (sucᵘ-cong t₁≡t₂) u₁≡u₂
      .≅-Urefl      → refl ∘ᶠ Uⱼ
      .≅-U-cong     → U-cong
      .≅ₜ-U-cong    → U-cong
      .≅ₜ-ℕrefl     → refl ∘ᶠ ℕⱼ
      .≅ₜ-Emptyrefl → refl ∘ᶠ Emptyⱼ
      .≅ₜ-Unit-cong → Unit-cong
      .≅ₜ-η-unit    → η-unit
      .≅-ΠΣ-cong    → ΠΣ-cong
      .≅ₜ-ΠΣ-cong   → ΠΣ-cong
      .≅ₜ-zerorefl  → refl ∘ᶠ zeroⱼ
      .≅-suc-cong   → suc-cong
      .≅-prod-cong  → prod-cong
      .≅-η-eq       → λ ⊢t ⊢u _ _ t0≡u0 → η-eq′ ⊢t ⊢u t0≡u0
      .≅-Σ-η        → λ _ ⊢t ⊢u _ _ fst≡ snd≡ → Σ-η′ ⊢t ⊢u fst≡ snd≡
      .~-var        → refl
      .~-app        → app-cong
      .~-fst        → fst-cong
      .~-snd        → snd-cong
      .~-natrec     → natrec-cong
      .~-prodrec    → prodrec-cong
      .~-emptyrec   → emptyrec-cong
      .~-unitrec    → unitrec-cong
      .≅ₜ-starrefl  → λ ⊢Γ ok → refl (starⱼ ⊢Γ ok)
      .≅-Id-cong    → Id-cong
      .≅ₜ-Id-cong   → Id-cong
      .≅ₜ-rflrefl   → refl ∘ᶠ rflⱼ
      .~-J          → J-cong
      .~-K          → K-cong
      .~-[]-cong    → []-cong-cong
    where
    open Equality-relations

-- An EqRelSet instance that uses definitional equality (_⊢_≡_ and
-- _⊢_≡_∷_).

instance

  eqRelInstance : EqRelSet
  eqRelInstance = λ where
    .EqRelSet._⊢_≅_              → _⊢_≡_
    .EqRelSet._⊢_≅_∷_            → _⊢_≡_∷_
    .EqRelSet._⊢_~_∷_            → _⊢_≡_∷_
    .EqRelSet.equality-relations → equality-relations
