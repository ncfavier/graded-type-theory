------------------------------------------------------------------------
-- Some basic properties of the logical relation for neutrals and levels.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed.Properties.Reduction R
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A B t u : Term _
    Γ : Con Term n

wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ∷ A × Γ ⊩neNf u ∷ A
wf-neNf (neNfₜ₌ neK neM k≡m)
  = neNfₜ neK (wf-⊢~∷ k≡m .proj₁)
  , neNfₜ neM (wf-⊢~∷ k≡m .proj₂)

mutual
  wf-⊩Level : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-⊩Level (Levelₜ₌ k k′ d d′ k≡k′ prop)
    = Levelₜ k d (wf-⊢≅∷ k≡k′ .proj₁) (wf-[Level]-prop prop .proj₁)
    , Levelₜ k′ d′ (wf-⊢≅∷ k≡k′ .proj₂) (wf-[Level]-prop prop .proj₂)

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop zeroᵘᵣ = zeroᵘᵣ , zeroᵘᵣ
  wf-[Level]-prop (sucᵘᵣ x) = sucᵘᵣ (wf-⊩Level x .proj₁) , sucᵘᵣ (wf-⊩Level x .proj₂)
  wf-[Level]-prop (ne x) = ne (wf-neNf x .proj₁) , ne (wf-neNf x .proj₂)

transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′ ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ neK neM k≡m) (neNfₜ₌ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermLevel : ∀ {n n′ n″}
                  → Γ ⊩Level n  ≡ n′ ∷Level
                  → Γ ⊩Level n′ ≡ n″ ∷Level
                  → Γ ⊩Level n  ≡ n″ ∷Level
  transEqTermLevel (Levelₜ₌ k _ d d′ t≡u prop) (Levelₜ₌ _ k″ d₁ d″ t≡u₁ prop₁)
    with whrDet*Term (d₁ , proj₁ (lsplit prop₁)) (d′ , proj₂ (lsplit prop))
  ... | PE.refl = Levelₜ₌ k k″ d d″ (≅ₜ-trans t≡u t≡u₁) (transLevel-prop prop prop₁)

  transLevel-prop : ∀ {k k′ k″}
                    → [Level]-prop Γ k k′
                    → [Level]-prop Γ k′ k″
                    → [Level]-prop Γ k k″
  transLevel-prop zeroᵘᵣ prop′ = prop′
  transLevel-prop prop zeroᵘᵣ = prop
  transLevel-prop (sucᵘᵣ a) (sucᵘᵣ b) = sucᵘᵣ (transEqTermLevel a b)
  transLevel-prop (ne [k≡k′]) (ne [k′≡k″]) =
    ne (transEqTermNe [k≡k′] [k′≡k″])
  transLevel-prop (sucᵘᵣ _) (ne (neNfₜ₌ () _ _))
  transLevel-prop (ne (neNfₜ₌ _ () _)) (sucᵘᵣ _)

symNeutralTerm : ∀ {t u A}
              → Γ ⊩neNf t ≡ u ∷ A
              → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

mutual
  symLevel-prop : ∀ {k k′}
                → [Level]-prop Γ k k′
                → [Level]-prop Γ k′ k
  symLevel-prop zeroᵘᵣ = zeroᵘᵣ
  symLevel-prop (sucᵘᵣ x) = sucᵘᵣ (symLevel x)
  symLevel-prop (ne prop) = ne (symNeutralTerm prop)

  symLevel : ∀ {k k′}
          → Γ ⊩Level k ≡ k′ ∷Level
          → Γ ⊩Level k′ ≡ k ∷Level
  symLevel (Levelₜ₌ k k′ d d′ k≡k′ prop) =
    Levelₜ₌ k′ k d′ d (≅ₜ-sym k≡k′) (symLevel-prop prop)
