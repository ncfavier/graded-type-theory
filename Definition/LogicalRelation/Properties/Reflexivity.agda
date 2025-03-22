------------------------------------------------------------------------
-- Equality in the logical relation is reflexive
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Reflexivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Properties.Kit R {{eqrel}}
open import Definition.LogicalRelation.Properties.Primitive R {{eqrel}}

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    l′ l : Universe-level
    A B t : Term _
    Γ : Con Term n

mutual
  reflLevel-prop : ∀ {n}
                 → Level-prop Γ n
                 → [Level]-prop Γ n n
  reflLevel-prop (sucᵘᵣ [n]) = sucᵘᵣ (reflLevel [n])
  reflLevel-prop zeroᵘᵣ = zeroᵘᵣ
  reflLevel-prop (ne (neNfₜ neK k≡k)) = ne (neNfₜ₌ neK neK k≡k)

  reflLevel : ∀ {n}
            → Γ ⊩Level n ∷Level
            → Γ ⊩Level n ≡ n ∷Level
  reflLevel (Levelₜ n d t≡t prop) =
    Levelₜ₌ n n d d t≡t (reflLevel-prop prop)

reflNatural-prop : ∀ {n}
                 → Natural-prop Γ n
                 → [Natural]-prop Γ n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflEmpty-prop : ∀ {n}
                 → Empty-prop Γ n
                 → [Empty]-prop Γ n n
reflEmpty-prop (ne (neNfₜ neK k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflUnitʷ-prop : ∀ {t A k}
               → Unit-prop Γ 𝕨 A k t
               → [Unitʷ]-prop Γ A k t t
reflUnitʷ-prop (starᵣ k≡k′) = starᵣ k≡k′ (reflLevel (wf-⊩Level k≡k′ .proj₂))
reflUnitʷ-prop (ne (neNfₜ neK k≡k)) = ne (neNfₜ₌ neK neK k≡k)


-- Reflexivity of reducible types.
reflEq : ∀ {l A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]

private

  -- A lemma used below.

  reflEq-⊩< :
    (p : l′ <ᵘ l) (⊩A : Γ ⊩<⟨ p ⟩ A) → Γ ⊩<⟨ p ⟩ A ≡ A / ⊩A
  reflEq-⊩< ≤ᵘ-refl     = reflEq
  reflEq-⊩< (≤ᵘ-step p) = reflEq-⊩< p

reflEq (Levelᵣ D) = D
reflEq (Uᵣ′ k [k] k< A⇒*U) = U₌ k A⇒*U (reflLevel [k])
reflEq (ℕᵣ D) = D
reflEq (Emptyᵣ D) = D
reflEq (Unitᵣ′ k [k] _ D _) = Unit₌ k D (reflLevel [k])
reflEq (ne′ _ D neK K≡K) = ne₌ _ D neK K≡K
reflEq (Bᵣ′ _ _ _ D A≡A [F] [G] _ _) =
   B₌ _ _ D A≡A
      (λ ρ → reflEq ([F] ρ))
      (λ ρ [a] → reflEq ([G] ρ [a]))
reflEq (Idᵣ ⊩A) = record
  { ⇒*Id′             = ⇒*Id
  ; Ty≡Ty′            = reflEq ⊩Ty
  ; lhs≡lhs′          = reflEqTerm ⊩Ty ⊩lhs
  ; rhs≡rhs′          = reflEqTerm ⊩Ty ⊩rhs
  ; lhs≡rhs→lhs′≡rhs′ = idᶠ
  ; lhs′≡rhs′→lhs≡rhs = idᶠ
  }
  where
  open _⊩ₗId_ ⊩A

reflEqTerm (Levelᵣ D) = reflLevel
reflEqTerm (Uᵣ′ k [k] k< ⊢Γ) (Uₜ A d A-type A≅A ⊩A) =
  Uₜ₌ A A d d A-type A-type A≅A ⊩A ⊩A (reflEq-⊩< k< ⊩A)
reflEqTerm (ℕᵣ D) (ℕₜ n d t≡t prop) =
  ℕₜ₌ n n d d t≡t (reflNatural-prop prop)
reflEqTerm (Emptyᵣ D) (Emptyₜ n d t≡t prop) =
  Emptyₜ₌ n n d d t≡t (reflEmpty-prop prop)
reflEqTerm (Unitᵣ {s} D) (Unitₜ n d t≡t prop) =
  let ⊢t = redFirst*Term d in
  case Unit-with-η? s of λ where
    (inj₁ η)                → Unitₜ₌ˢ ⊢t ⊢t η
    (inj₂ (PE.refl , no-η)) →
      Unitₜ₌ʷ n n d d t≡t (reflUnitʷ-prop prop) no-η
reflEqTerm (ne′ _ D neK K≡K) (neₜ k d (neNfₜ neK₁ k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm
  (Bᵣ′ BΠ! _ _ _ _ [F] _ _ _) [t]@(Πₜ f d funcF f≡f [f] _) =
  Πₜ₌ f f d d funcF funcF f≡f [t] [t]
      (λ ρ [a] → [f] ρ [a] [a] (reflEqTerm ([F] ρ) [a]))
reflEqTerm
  (Bᵣ′ BΣˢ _ _ _ _ [F] [G] _ _)
  [t]@(Σₜ p d p≅p prodP ([fstp] , [sndp])) =
  Σₜ₌ p p d d prodP prodP p≅p [t] [t]
      ([fstp] , [fstp] , reflEqTerm ([F] _) [fstp] ,
       reflEqTerm ([G] _ [fstp]) [sndp])
reflEqTerm
  (Bᵣ′ BΣʷ _ _ _ _ [F] [G] _ _)
  [t]@(Σₜ p d p≅p prodₙ (PE.refl , [p₁] , [p₂] , PE.refl)) =
  Σₜ₌ p p d d prodₙ prodₙ p≅p [t] [t]
      (PE.refl , PE.refl , [p₁] , [p₁] , [p₂] , [p₂] ,
        reflEqTerm ([F] _) [p₁] ,
        reflEqTerm ([G] _ [p₁]) [p₂])
reflEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _) [t]@(Σₜ p d p≅p (ne x) p~p) =
  Σₜ₌ p p d d (ne x) (ne x) p≅p [t] [t] p~p
reflEqTerm (Idᵣ _) ⊩t =
  ⊩Id≡∷ ⊩t ⊩t
    (case ⊩Id∷-view-inhabited ⊩t of λ where
       (rflᵣ _)     → _
       (ne _ t′~t′) → t′~t′)
