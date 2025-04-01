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
open import Definition.Untyped.Neutral M type-variant
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

-- Transitivity for neutrals in WHNF and levels

transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′ ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ inc neK neM k≡m) (neNfₜ₌ _ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ inc neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermNeLevel : ∀ {n n′ n″}
                   → Γ ⊩neLvl n  ≡ n′ ∷Level
                   → Γ ⊩neLvl n′ ≡ n″ ∷Level
                   → Γ ⊩neLvl n  ≡ n″ ∷Level
  transEqTermNeLevel (neLvlₜ₌ ne-n _ prop) (neLvlₜ₌ _ ne-n″ prop′) = neLvlₜ₌ ne-n ne-n″ (transneLevel-prop prop prop′)

  transEqTermLevel : ∀ {n n′ n″}
                   → Γ ⊩Level n  ≡ n′ ∷Level
                   → Γ ⊩Level n′ ≡ n″ ∷Level
                   → Γ ⊩Level n  ≡ n″ ∷Level
  transEqTermLevel (Levelₜ₌ k _ d d′ prop) (Levelₜ₌ _ k″ d₁ d″ prop₁)
    with whrDet*Term (d₁ , proj₁ (lsplit prop₁)) (d′ , proj₂ (lsplit prop))
  ... | PE.refl = Levelₜ₌ k k″ d d″ (transLevel-prop prop prop₁)

  transneLevel-prop : ∀ {k k′ k″}
                    → [neLevel]-prop Γ k k′
                    → [neLevel]-prop Γ k′ k″
                    → [neLevel]-prop Γ k k″
  transneLevel-prop (maxᵘˡᵣ x y) (maxᵘˡᵣ z w) = maxᵘˡᵣ (transEqTermNeLevel x z) (transEqTermLevel y w)
  transneLevel-prop (maxᵘʳᵣ x y) (maxᵘʳᵣ z w) = maxᵘʳᵣ (transEqTermLevel x z) (transEqTermNeLevel y w)
  transneLevel-prop (ne x) (ne y) = ne (transEqTermNe x y)
  transneLevel-prop (maxᵘˡᵣ (neLvlₜ₌ _ (ne ()) _) y) (maxᵘʳᵣ z w)
  transneLevel-prop (maxᵘˡᵣ x y) (ne (neNfₜ₌ _ () _ _))
  transneLevel-prop (maxᵘʳᵣ x y) (maxᵘˡᵣ (neLvlₜ₌ (ne ()) _ _) w)
  transneLevel-prop (maxᵘʳᵣ x y) (ne (neNfₜ₌ _ () _ _))
  transneLevel-prop (ne (neNfₜ₌ _ _ () _)) (maxᵘˡᵣ y z)
  transneLevel-prop (ne (neNfₜ₌ _ _ () _)) (maxᵘʳᵣ y z)

  transLevel-prop : ∀ {k k′ k″}
                    → [Level]-prop Γ k k′
                    → [Level]-prop Γ k′ k″
                    → [Level]-prop Γ k k″
  transLevel-prop zeroᵘᵣ y = y
  transLevel-prop (sucᵘᵣ x) (sucᵘᵣ y) = sucᵘᵣ (transEqTermLevel x y)
  transLevel-prop (ne x) (ne y) = ne (transEqTermNeLevel x y)
  transLevel-prop (sucᵘᵣ x) (ne (neLvlₜ₌ (ne ()) _ _))
  transLevel-prop (ne (neLvlₜ₌ _ (ne ()) _)) zeroᵘᵣ
  transLevel-prop (ne (neLvlₜ₌ _ (ne ()) _)) (sucᵘᵣ y)

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

mutual
  symneLevel-prop : ∀ {k k′}
                → [neLevel]-prop Γ k k′
                → [neLevel]-prop Γ k′ k
  symneLevel-prop (maxᵘˡᵣ x y) = maxᵘˡᵣ (symNeLevel x) (symLevel y)
  symneLevel-prop (maxᵘʳᵣ x y) = maxᵘʳᵣ (symLevel x) (symNeLevel y)
  symneLevel-prop (ne x) = ne (symNeutralTerm x)

  symLevel-prop : ∀ {k k′}
                → [Level]-prop Γ k k′
                → [Level]-prop Γ k′ k
  symLevel-prop zeroᵘᵣ = zeroᵘᵣ
  symLevel-prop (sucᵘᵣ x) = sucᵘᵣ (symLevel x)
  symLevel-prop (ne prop) = ne (symNeLevel prop)

  symNeLevel : ∀ {k k′}
          → Γ ⊩neLvl k ≡ k′ ∷Level
          → Γ ⊩neLvl k′ ≡ k ∷Level
  symNeLevel (neLvlₜ₌ a b prop) = neLvlₜ₌ b a (symneLevel-prop prop)

  symLevel : ∀ {k k′}
          → Γ ⊩Level k ≡ k′ ∷Level
          → Γ ⊩Level k′ ≡ k ∷Level
  symLevel (Levelₜ₌ k k′ d d′ prop) =
    Levelₜ₌ k′ k d′ d (symLevel-prop prop)

-- Well-formedness for neutrals in WHNF and levels

wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ t ∷ A × Γ ⊩neNf u ≡ u ∷ A
wf-neNf t≡u =
    transEqTermNe t≡u (symNeutralTerm t≡u)
  , transEqTermNe (symNeutralTerm t≡u) t≡u

mutual
  wf-⊩Level : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-⊩Level t≡u =
      transEqTermLevel t≡u (symLevel t≡u)
    , transEqTermLevel (symLevel t≡u) t≡u
