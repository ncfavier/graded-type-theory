------------------------------------------------------------------------
-- Some lemmas related to the logical relation and WHNFs
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Whnf
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

open import Tools.Product

private variable
  Γ   : Con Term _
  t u : Term _

opaque

  -- If t and u satisfy [Level]-prop Γ, then they are WHNFs.

  lsplit : [Level]-prop Γ t u → Whnf t × Whnf u
  lsplit zeroᵘᵣ = zeroᵘₙ , zeroᵘₙ
  lsplit (sucᵘᵣ x) = sucᵘₙ , sucᵘₙ
  lsplit (ne (neLvlₜ₌ t-ne u-ne _)) = ne t-ne , ne u-ne

opaque

  -- If t and u satisfy [Natural]-prop Γ, then they are "Naturals".

  split : [Natural]-prop Γ t u → Natural t × Natural u
  split (sucᵣ _)                    = sucₙ , sucₙ
  split zeroᵣ                       = zeroₙ , zeroₙ
  split (ne (neNfₜ₌ _ t-ne u-ne _)) = ne t-ne , ne u-ne

opaque

  -- If t and u satisfy [Empty]-prop Γ, then they are neutral terms.

  esplit : [Empty]-prop Γ t u → Neutral t × Neutral u
  esplit (ne (neNfₜ₌ _ t-ne u-ne _)) = t-ne , u-ne

opaque

  -- If t and u satisfy [Unitʷ]-prop Γ, then they are WHNFs.

  usplit : ∀ {k} → [Unitʷ]-prop Γ k t u → Whnf t × Whnf u
  usplit (starᵣ _ _)               = starₙ , starₙ
  usplit (ne (neNfₜ₌ _ t-ne u-ne _)) = ne (ne t-ne) , ne (ne u-ne)
