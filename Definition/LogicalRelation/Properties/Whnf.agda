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

open import Definition.LogicalRelation R ⦃ eqrel ⦄

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

open import Tools.Product

private variable
  Γ   : Con Term _
  t u : Term _

opaque

  -- If t satisfies Level-prop Γ, then it is a WHNF.

  nelevel : neLevel-prop Γ t → Semineutral t
  nelevel (maxᵘˡᵣ x x₁) = maxᵘˡₙ (nelevel x)
  nelevel (maxᵘʳᵣ x x₁) = maxᵘʳₙ (nelevel x₁)
  nelevel (ne (neNfₜ₌ _ neK neM k≡m)) = ne neK

  level : Level-prop Γ t → Whnf t
  level zeroᵘᵣ = zeroᵘₙ
  level (sucᵘᵣ x) = sucᵘₙ
  level (neLvl x) = ne (nelevel x)

opaque

  -- If t and u satisfy [Level]-prop Γ, then they are WHNFs.

  nelsplit : [neLevel]-prop Γ t u → Semineutral t × Semineutral u
  nelsplit (maxᵘˡᵣ t≡u x) = let a , b = nelsplit t≡u in maxᵘˡₙ a , maxᵘˡₙ b
  nelsplit (maxᵘʳᵣ x t≡u) = let a , b = nelsplit t≡u in maxᵘʳₙ a , maxᵘʳₙ b
  nelsplit (maxᵘ-zeroʳˡᵣ u≡u) = let a , _ = nelsplit u≡u in maxᵘˡₙ a , a
  nelsplit (maxᵘ-assoc¹ᵣ x y z) = let a , _ = nelsplit x in maxᵘˡₙ (maxᵘˡₙ a) , maxᵘˡₙ a
  nelsplit (maxᵘ-assoc²ᵣ x y z) = let a , _ = nelsplit y in maxᵘˡₙ (maxᵘʳₙ a) , maxᵘʳₙ (maxᵘˡₙ a)
  nelsplit (maxᵘ-assoc³ᵣ x y z) = let a , _ = nelsplit z in maxᵘʳₙ a , maxᵘʳₙ (maxᵘʳₙ a)
  nelsplit (maxᵘ-comm¹ᵣ x d y d′) =
    let t₁ , _ = nelsplit x
        u₂ , _ = nelsplit y
    in maxᵘˡₙ t₁ , maxᵘˡₙ u₂
  nelsplit (maxᵘ-comm²ᵣ x d y) = let u₁ , u₂ = nelsplit y in maxᵘʳₙ u₁ , maxᵘˡₙ u₂
  nelsplit (maxᵘ-idem x y) = let n , _ = nelsplit x in maxᵘˡₙ n , n
  nelsplit (ne (neNfₜ₌ _ neK neM _)) = ne neK , ne neM

  -- lsplit : [Level]-prop Γ t u → Whnf t × Whnf u
  -- lsplit zeroᵘᵣ = zeroᵘₙ , zeroᵘₙ
  -- lsplit (sucᵘᵣ x) = sucᵘₙ , sucᵘₙ
  -- lsplit (sub _ x) = let a , b = nelsplit x in ne a , sucᵘₙ
  -- lsplit (neLvl x) = let a , b = nelsplit x in ne a , ne b
  -- lsplit (sym u≡t) = let a , b = lsplit u≡t in b , a
  -- lsplit (trans t≡u u≡v) = let a , _ = lsplit t≡u; _ , b = lsplit u≡v in a , b

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

  -- If t and u satisfy [Unit]-prop′ Γ, then they are WHNFs.

  usplit : ∀ {s k} → [Unit]-prop′ Γ k s t u → Whnf t × Whnf u
  usplit (starᵣ _ _)                 = starₙ , starₙ
  usplit (ne (neNfₜ₌ _ t-ne u-ne _)) = ne! t-ne , ne! u-ne
