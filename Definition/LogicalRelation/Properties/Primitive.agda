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
open import Definition.Typed R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    A B t t₁ t₂ t₁′ t₂′ u u₁ u₂ v : Term _
    Γ : Con Term n

wf-Level-eq : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
wf-Level-eq (Levelₜ₌ [t] [u] _) = [t] , [u]

combineLevel : ([t] : Γ ⊩Level t ∷Level) → ([u] : Γ ⊩Level u ∷Level) → [Level]-prop Γ t u → Γ ⊩Level t ≡ u ∷Level
combineLevel [t] [u] t≅u = Levelₜ₌ [t] [u] t≅u

-- Transitivity for neutrals in WHNF and levels

transEqTermNe : ∀ {n n′ n″ A}
              → Γ ⊩neNf n  ≡ n′ ∷ A
              → Γ ⊩neNf n′ ≡ n″ ∷ A
              → Γ ⊩neNf n  ≡ n″ ∷ A
transEqTermNe (neNfₜ₌ inc neK neM k≡m) (neNfₜ₌ _ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ inc neK neM₁ (~-trans k≡m k≡m₁)

transEqTermLevel : ∀ {n n′ n″}
                  → Γ ⊩Level n  ≡ n′ ∷Level
                  → Γ ⊩Level n′ ≡ n″ ∷Level
                  → Γ ⊩Level n  ≡ n″ ∷Level
transEqTermLevel (Levelₜ₌ [t] [u] t≡u) (Levelₜ₌ [u]′ [v] u≡v) =
  Levelₜ₌ [t] [v] (trans t≡u u≡v)

-- Symmetry for neutrals in WHNF and levels

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

symLevel : ∀ {k k′}
          → Γ ⊩Level k ≡ k′ ∷Level
          → Γ ⊩Level k′ ≡ k ∷Level
symLevel (Levelₜ₌ [t] [u] t≡u) = Levelₜ₌ [u] [t] (sym t≡u)

-- Some reduction and expansion lemmas

-- redLevel
--   : ∀ {t t′}
--   → Γ ⊢ t ⇒* t′ ∷ Level
--   → Γ ⊩Level t ∷Level
--   → Γ ⊩Level t ≡ t′ ∷Level
-- redLevel t⇒ (Levelₜ k d prop) =
--   Levelₜ₌ _ _ d (whrDet↘Term (d , level prop) t⇒)
--     prop prop
--     -- (reflLevel-prop (wfTerm (redFirst*Term d)) prop)
--     {!   !}

⊩Level-⇒*
  : ∀ {t t′}
  → Γ ⊢ t′ ⇒* t ∷ Level
  → Γ ⊩Level t ∷Level
  → Γ ⊩Level t′ ∷Level
⊩Level-⇒* t′⇒t (Levelₜ k d prop) =
  Levelₜ _ (t′⇒t ⇨∷* d) prop

-- ⊩Level≡-⇒*
--   : ∀ {t t′ u u′}
--   → Γ ⊢ t′ ⇒* t ∷ Level
--   → Γ ⊢ u′ ⇒* u ∷ Level
--   → Γ ⊩Level t ≡ u ∷Level
--   → Γ ⊩Level t′ ≡ u′ ∷Level
-- ⊩Level≡-⇒* t′⇒t u′⇒u (Levelₜ₌ k k′ d d′ prop prop′ k≡k′) =
--   Levelₜ₌ _ _ (t′⇒t ⇨∷* d) (u′⇒u ⇨∷* d′) prop prop′ {!k≡k′!}

-- Escape lemmas for levels

-- lem : ∀ {t t′ u u′} → Γ ⊢ t ⇒* t′ ∷ Level → Γ ⊢ u ⇒* u′ ∷ Level → Γ ⊢ t ≅ u ∷ Level → Γ ⊢ t′ ≅ u′ ∷ Level
-- lem (id x) (id x₁) t≡u = t≡u
-- lem (id x) (x₁ ⇨ d′) t≡u = {! x₁  !}
-- lem (x ⇨ d) d′ t≡u = {!   !}

mutual
  -- Reducible level equalities are well-formed.
  escapeLevelEq
    : Γ ⊩Level t ≡ u ∷Level
    → Γ ⊢ t ≅ u ∷ Level
  escapeLevelEq (Levelₜ₌ [t] [u] t≡u) =
    -- let lk = level prop
    --     lk′ = level prop′
    -- in ≅ₜ-red (id (Levelⱼ (wfTerm (redFirst*Term D))) , Levelₙ) (D , lk) (D′ , lk′)
      -- (escape-[Level]-prop (wfTerm (redFirst*Term D)) k≡k′)
      -- escape-[Level]-prop [t] [u] t≡u
      ?

  -- escape-[Level]-prop
  --   : Γ ⊩Level t ∷Level
  --   → Γ ⊩Level u ∷Level
  --   → [Level]-prop Γ t u
  --   → Γ ⊢ t ≅ u ∷ Level
  -- escape-[Level]-prop [t] [u] zeroᵘᵣ = ≅ₜ-zeroᵘrefl {!   !}
  -- escape-[Level]-prop [t] [u] (sucᵘᵣ x) = ≅ₜ-sucᵘ-cong (escapeLevelEq x)
  -- escape-[Level]-prop [t] [u] (maxᵘᵣ x x₁) = ≅ₜ-maxᵘ-cong (escapeLevelEq x) (escapeLevelEq x₁)
  -- escape-[Level]-prop [t] [u] (ne (neNfₜ₌ neutrals-included neK neM k≡m)) = ~-to-≅ₜ k≡m
  -- escape-[Level]-prop [t] [u] refl = {!   !}
  -- escape-[Level]-prop [t] [u] (sym x) = ≅ₜ-sym (escape-[Level]-prop [u] [t] x)
  -- escape-[Level]-prop [t] [u] (trans x x₁) = ≅ₜ-trans (escape-[Level]-prop [t] {!   !} x) (escape-[Level]-prop {!   !} [u] x₁)

  -- Reducible levels are well-formed.
  escapeLevel
    : Γ ⊩Level t ∷Level
    → Γ ⊢ t ∷ Level
  escapeLevel (Levelₜ k D prop) = redFirst*Term D

  escape-Level-prop
    : ⊢ Γ
    → Level-prop Γ t
    → Γ ⊢ t ∷ Level
  escape-Level-prop ⊢Γ zeroᵘᵣ = zeroᵘⱼ ⊢Γ
  escape-Level-prop ⊢Γ (sucᵘᵣ x) = sucᵘⱼ (escapeLevel x)
  escape-Level-prop ⊢Γ (neLvl x) = escape-neLevel-prop x

  escape-neLevel-prop
    : neLevel-prop Γ t
    → Γ ⊢ t ∷ Level
  escape-neLevel-prop (maxᵘˡᵣ x y) = maxᵘⱼ (escape-neLevel-prop x) (escapeLevel y)
  escape-neLevel-prop (maxᵘʳᵣ x y) = maxᵘⱼ (sucᵘⱼ (escapeLevel x)) (escape-neLevel-prop y)
  escape-neLevel-prop (ne (neNfₜ₌ _ _ _ k≡m)) = wf-⊢≡∷ (≅ₜ-eq (~-to-≅ₜ k≡m)) .proj₂ .proj₁

⊩neLvl : neLevel-prop Γ t → Γ ⊩Level t ∷Level
⊩neLvl x = Levelₜ _ (id (escape-neLevel-prop x)) (neLvl x)
-- ⊩[neLvl] : [Level]-prop Γ t u → Γ ⊩Level t ≡ u ∷Level
-- ⊩[neLvl] t≡u = Levelₜ₌ _ _ (id {!   !}) (id {!   !}) {! wf-Level-eq   !} {!   !} t≡u

opaque

  ⊩zeroᵘ : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩zeroᵘ ⊢Γ =
    Levelₜ _ (id (zeroᵘⱼ ⊢Γ)) zeroᵘᵣ

opaque

  ⊩sucᵘ : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩sucᵘ [t]@(Levelₜ _ t⇒*t′ prop) =
    Levelₜ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (sucᵘᵣ [t])

  ⊩sucᵘ≡sucᵘ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
  ⊩sucᵘ≡sucᵘ t≡u@(Levelₜ₌ [t] [u] t′≡u′) =
    -- let t′-ok = level propt
    --     u′-ok = level propu
    --     [t] , [u] = wf-Level-eq t≡u
    --     t≅u = escapeLevelEq t≡u
    Levelₜ₌
      -- (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      -- (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (⊩sucᵘ [t])
      (⊩sucᵘ [u])
      -- (≅ₜ-sucᵘ-cong t≅u)
      (sucᵘᵣ t≡u)

mutual

  -- Reflexivity of level terms.

  reflLevel : Γ ⊩Level t ∷Level → Γ ⊩Level t ≡ t ∷Level
  reflLevel [t] = Levelₜ₌ [t] [t]
    -- (reflLevel-prop prop)
    refl

  reflneLevel-prop : neLevel-prop Γ t → [Level]-prop Γ t t
  reflneLevel-prop (maxᵘˡᵣ x x₁) = maxᵘᵣ (reflLevel (⊩neLvl x)) (reflLevel x₁)
  reflneLevel-prop (maxᵘʳᵣ x x₁) = maxᵘᵣ (reflLevel (⊩sucᵘ x)) (reflLevel (⊩neLvl x₁))
  reflneLevel-prop (ne x) = ne x

  reflLevel-prop : Level-prop Γ t → [Level]-prop Γ t t
  reflLevel-prop zeroᵘᵣ = zeroᵘᵣ
  reflLevel-prop (sucᵘᵣ x) = sucᵘᵣ (reflLevel x)
  reflLevel-prop (neLvl x₁) = reflneLevel-prop x₁

opaque

  -- An introduction lemma for _⊩Level _ maxᵘ _ ∷Level

  ⊩maxᵘ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ∷Level
  ⊩maxᵘ {t} {u} [t]@(Levelₜ t′ t⇒ propt) [u]@(Levelₜ u′ u⇒ propu) =
    let ⊢u = escapeLevel [u]
        ⊢Γ = wfTerm ⊢u
        ⊢t′ = escape-Level-prop ⊢Γ propt
        ⊢u′ = escape-Level-prop ⊢Γ propu
    in ⊩Level-⇒* (maxᵘ-substˡ* t⇒ ⊢u) $
        case propt of λ where
          zeroᵘᵣ →
            Levelₜ u′
              (zeroᵘ maxᵘ u  ⇒⟨ maxᵘ-zeroˡ ⊢u ⟩
                          u  ⇒*⟨ u⇒ ⟩∎
                          u′ ∎)
              propu
          (sucᵘᵣ {k = t′} [t′]) →
            let ⊢t′ = escapeLevel [t′]
            in ⊩Level-⇒* (maxᵘ-substʳ* ⊢t′ u⇒) $
                case propu of λ where
                  zeroᵘᵣ → Levelₜ _
                    (sucᵘ t′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t′ ⟩∎
                     sucᵘ t′            ∎)
                    (sucᵘᵣ [t′])
                  (sucᵘᵣ {k = u′} [u′]) →
                    let ⊢u′ = escapeLevel [u′]
                    in Levelₜ _
                      (sucᵘ t′ maxᵘ sucᵘ u′ ⇒⟨ maxᵘ-sucᵘ ⊢t′ ⊢u′ ⟩∎
                       sucᵘ (t′ maxᵘ u′)    ∎)
                      (sucᵘᵣ (⊩maxᵘ [t′] [u′]))
                  (neLvl [u′]) →
                    Levelₜ _
                      (id (maxᵘⱼ (sucᵘⱼ ⊢t′) ⊢u′))
                      (neLvl (maxᵘʳᵣ [t′] [u′]))
          (neLvl [t′]) →
            Levelₜ (t′ maxᵘ u)
              (id (maxᵘⱼ ⊢t′ ⊢u))
              (neLvl (maxᵘˡᵣ [t′] [u]))

-- Well-formedness for neutrals in WHNF and levels

⊩predᵘ : Γ ⊩Level sucᵘ t ∷Level → Γ ⊩Level t ∷Level
⊩predᵘ (Levelₜ _ sucᵘ-t⇒*t′ [t′]) =
  case whnfRed*Term sucᵘ-t⇒*t′ sucᵘₙ of λ {
    PE.refl →
  lemma₀ [t′]}
  where
  lemma₀ : ∀ {t} → Level-prop Γ (sucᵘ t) → Γ ⊩Level t ∷Level
  lemma₀ (sucᵘᵣ x) = x
  lemma₀ (neLvl x) = case nelevel x of λ { (ne ()) }

wf-neNf : Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ t ∷ A × Γ ⊩neNf u ≡ u ∷ A
wf-neNf t≡u = transEqTermNe t≡u (symNeutralTerm t≡u) , transEqTermNe (symNeutralTerm t≡u) t≡u

wf-neLevel-prop : neLevel-prop Γ t → ⊢ Γ
wf-neLevel-prop (maxᵘˡᵣ x₁ x₂) = wf-neLevel-prop x₁
wf-neLevel-prop (maxᵘʳᵣ x₁ x₂) = wf-neLevel-prop x₂
wf-neLevel-prop (ne (neNfₜ₌ _ neK neM k≡m)) = wfEqTerm (≅ₜ-eq (~-to-≅ₜ k≡m))

{-
mutual
  wf-Level-eq : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level
  wf-Level-eq (Levelₜ₌ k k′ d d′ prop) =
    let x , y = wf-[Level]-prop prop
    in Levelₜ k d x , Levelₜ k′ d′ y

  wf-[Level]-prop : [Level]-prop Γ t u → Level-prop Γ t × Level-prop Γ u
  wf-[Level]-prop zeroᵘᵣ = zeroᵘᵣ , zeroᵘᵣ
  wf-[Level]-prop (sucᵘᵣ x) = let a , b = wf-Level-eq x in sucᵘᵣ a , sucᵘᵣ b
  wf-[Level]-prop (sub k≡k x) =
    let [t] , _ = wf-[neLevel]-prop x
        [k′] , _ = wf-[neLevel]-prop k≡k
    in neLvl [t] , sucᵘᵣ (⊩neLvl [k′])
  wf-[Level]-prop (neLvl t≡u) = let [t] , [u] = wf-[neLevel]-prop t≡u in neLvl [t] , neLvl [u]
  wf-[Level]-prop (sym u≡t) =
    let [u] , [t] = wf-[Level]-prop u≡t
    in [t] , [u]
  wf-[Level]-prop (trans x y) =
    let [t] , _ = wf-[Level]-prop x
        _ , [u] = wf-[Level]-prop y
    in [t] , [u]

  wf-[neLevel]-prop : [neLevel]-prop Γ t u → neLevel-prop Γ t × neLevel-prop Γ u
  wf-[neLevel]-prop (maxᵘˡᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-[neLevel]-prop k₁≡k₁′
        [k₂] , [k₂′] = wf-Level-eq k₂≡k₂′
    in maxᵘˡᵣ [k₁] [k₂] , maxᵘˡᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘʳᵣ k₁≡k₁′ k₂≡k₂′) =
    let [k₁] , [k₁′] = wf-Level-eq k₁≡k₁′
        [k₂] , [k₂′] = wf-[neLevel]-prop k₂≡k₂′
    in maxᵘʳᵣ [k₁] [k₂] , maxᵘʳᵣ [k₁′] [k₂′]
  wf-[neLevel]-prop (maxᵘ-zeroʳˡᵣ k≡k) =
    let [k] , _ = wf-[neLevel]-prop k≡k
    in maxᵘˡᵣ [k] (Levelₜ _ (id (zeroᵘⱼ (wf-neLevel-prop [k]))) zeroᵘᵣ) , [k]
  wf-[neLevel]-prop (maxᵘ-assoc¹ᵣ x y z) =
    let [t] , _ = wf-[neLevel]-prop x
        [u] , _ = wf-Level-eq y
        [v] , _ = wf-Level-eq z
    in maxᵘˡᵣ (maxᵘˡᵣ [t] [u]) [v] , maxᵘˡᵣ [t] (⊩maxᵘ [u] [v])
  wf-[neLevel]-prop (maxᵘ-assoc²ᵣ x y z) =
    let [t] , _ = wf-Level-eq x
        [u] , _ = wf-[neLevel]-prop y
        [v] , _ = wf-Level-eq z
    in maxᵘˡᵣ (maxᵘʳᵣ [t] [u]) [v] , maxᵘʳᵣ [t] (maxᵘˡᵣ [u] [v])
  wf-[neLevel]-prop (maxᵘ-assoc³ᵣ x y z) =
    let [t] , _ = wf-Level-eq x
        [u] , _ = wf-Level-eq y
        [v] , _ = wf-[neLevel]-prop z
    in maxᵘʳᵣ (⊩maxᵘ [t] [u]) [v] , maxᵘʳᵣ [t] (maxᵘʳᵣ [u] [v])
  wf-[neLevel]-prop (maxᵘ-comm¹ᵣ x d y d′) =
    let [t₁] , _ = wf-[neLevel]-prop x
        [u₁] , _ = wf-Level-eq d′
        _ , [t₂] = wf-Level-eq d
        [u₂] , _ = wf-[neLevel]-prop y
    in maxᵘˡᵣ [t₁] [u₁] , maxᵘˡᵣ [u₂] [t₂]
  wf-[neLevel]-prop (maxᵘ-comm²ᵣ x d y) =
    let [t₁] , _ = wf-Level-eq x
        _ , [t₂] = wf-Level-eq d
        [u] , _ = wf-[neLevel]-prop y
    in maxᵘʳᵣ [t₁] [u] , maxᵘˡᵣ [u] [t₂]
  wf-[neLevel]-prop (maxᵘ-idem x y) =
    let [u] , _ = wf-[neLevel]-prop x
        _ , [t₂] = wf-Level-eq y
    in maxᵘˡᵣ [u] [t₂] , [u]
  wf-[neLevel]-prop (ne x) =
    let a , b = wf-neNf x
    in ne a , ne b
-}

opaque mutual

  -- An introduction lemma for _⊩Level _ maxᵘ _ ≡ _ maxᵘ _ ∷Level

  -- ⊩maxᵘ≡maxᵘ-prop :
  --   [Level]-prop Γ t₁′ t₂′ →
  --   Γ ⊩Level u₁ ≡ u₂ ∷Level →
  --   Γ ⊩Level t₁′ maxᵘ u₁ ≡ t₂′ maxᵘ u₂ ∷Level
  -- ⊩maxᵘ≡maxᵘ-prop zeroᵘᵣ u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
  --   let _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq u₁≡u₂))
  --   in Levelₜ₌ _ _ (maxᵘ-zeroˡ ⊢u₁ ⇨ u₁⇒) (maxᵘ-zeroˡ ⊢u₂ ⇨ u₂⇒) propu
  -- ⊩maxᵘ≡maxᵘ-prop (sucᵘᵣ x) u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
  --   {!   !}
  -- ⊩maxᵘ≡maxᵘ-prop (sub k≡k x) u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
  --   {!   !}
  -- ⊩maxᵘ≡maxᵘ-prop (neLvl t₁′≡t₂′) u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
  --   let _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq u₁≡u₂))
  --       _ , ⊢t₁′ , ⊢t₂′ = wf-⊢≡∷ (≅ₜ-eq (escape-[neLevel]-prop t₁′≡t₂′))
  --   in Levelₜ₌ _ _ (id (maxᵘⱼ ⊢t₁′ ⊢u₁)) (id (maxᵘⱼ ⊢t₂′ ⊢u₂)) (neLvl (maxᵘˡᵣ t₁′≡t₂′ u₁≡u₂))
  -- ⊩maxᵘ≡maxᵘ-prop (sym x) u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
  --   symLevel (⊩maxᵘ≡maxᵘ-prop x (symLevel u₁≡u₂))
  -- ⊩maxᵘ≡maxᵘ-prop (trans x y) u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) =
  --   transEqTermLevel (⊩maxᵘ≡maxᵘ-prop x u₁≡u₂) (⊩maxᵘ≡maxᵘ-prop y (reflLevel (wf-Level-eq u₁≡u₂ .proj₂)))

  ⊩maxᵘ≡maxᵘ :
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷Level
  ⊩maxᵘ≡maxᵘ {t₁} {t₂} {u₁} {u₂} t₁≡t₂@(Levelₜ₌ [t₁] [t₂] t₁′≡t₂′) u₁≡u₂@(Levelₜ₌ [u₁] [u₂] u₁′≡u₂′) =
    -- let _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq u₁≡u₂))
    --     ⊢Γ = wfTerm ⊢u₁
    --     [t₁] , [t₂] = wf-Level-eq t₁≡t₂
    --     [u₁] , [u₂] = wf-Level-eq u₁≡u₂
    --     -- _ , ⊢t₁′ , ⊢t₂′ = wf-⊢≡∷ (≅ₜ-eq (escape-[Level]-prop ⊢Γ propt))
    --     -- _ , ⊢u₁′ , ⊢u₂′ = wf-⊢≡∷ (≅ₜ-eq (escape-[Level]-prop ⊢Γ propu))
    -- in -- ⊩Level≡-⇒* (maxᵘ-substˡ* t₁⇒ {!   !}) (maxᵘ-substˡ* t₂⇒ {!   !}) $
      -- ⊩maxᵘ≡maxᵘ-prop propt u₁≡u₂
      -- Levelₜ₌ _ _ {!   !} {!   !} {!   !} {!   !} {!   !}
      combineLevel (⊩maxᵘ [t₁] [u₁]) (⊩maxᵘ [t₂] [u₂])
        -- (≅ₜ-maxᵘ-cong t₁′≡t₂′ u₁′≡u₂′)
        (maxᵘᵣ t₁≡t₂ u₁≡u₂)
        -- case propt of λ where
        --   zeroᵘᵣ →
        --     Levelₜ₌ u₁′ u₂′
        --       (zeroᵘ maxᵘ u₁  ⇒⟨ maxᵘ-zeroˡ ⊢u₁ ⟩
        --                   u₁  ⇒*⟨ u₁⇒ ⟩∎
        --                   u₁′ ∎)
        --       (zeroᵘ maxᵘ u₂  ⇒⟨ maxᵘ-zeroˡ ⊢u₂ ⟩
        --                   u₂  ⇒*⟨ u₂⇒ ⟩∎
        --                   u₂′ ∎)
        --       propu
        --   (sucᵘᵣ {k = t₁′} {k′ = t₂′} t₁′≡t₂′) →
        --     let _ , ⊢t₁′ , ⊢t₂′ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq t₁′≡t₂′))
        --     in ⊩Level≡-⇒* (maxᵘ-substʳ* ⊢t₁′ u₁⇒) (maxᵘ-substʳ* ⊢t₂′ u₂⇒) $
        --         case propu of λ where
        --           zeroᵘᵣ → Levelₜ₌ _ _
        --             (sucᵘ t₁′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₁′ ⟩∎
        --              sucᵘ t₁′            ∎)
        --             (sucᵘ t₂′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₂′ ⟩∎
        --              sucᵘ t₂′            ∎)
        --             (sucᵘᵣ t₁′≡t₂′)
        --           (sucᵘᵣ {k = u₁′} {k′ = u₂′} u₁′≡u₂′) →
        --             let _ , ⊢u₁′ , ⊢u₂′ = wf-⊢≡∷ (≅ₜ-eq (escapeLevelEq u₁′≡u₂′))
        --             in Levelₜ₌ _ _
        --               (sucᵘ t₁′ maxᵘ sucᵘ u₁′ ⇒⟨ maxᵘ-sucᵘ ⊢t₁′ ⊢u₁′ ⟩∎
        --                sucᵘ (t₁′ maxᵘ u₁′)    ∎)
        --               (sucᵘ t₂′ maxᵘ sucᵘ u₂′ ⇒⟨ maxᵘ-sucᵘ ⊢t₂′ ⊢u₂′ ⟩∎
        --                sucᵘ (t₂′ maxᵘ u₂′)    ∎)
        --               (sucᵘᵣ (⊩maxᵘ≡maxᵘ t₁′≡t₂′ u₁′≡u₂′))
        --           (neLvl u₁′≡u₂′) →
        --             Levelₜ₌ _ _
        --               (id (maxᵘⱼ (sucᵘⱼ ⊢t₁′) ⊢u₁′))
        --               (id (maxᵘⱼ (sucᵘⱼ ⊢t₂′) ⊢u₂′))
        --               (neLvl (maxᵘʳᵣ t₁′≡t₂′ u₁′≡u₂′))
        --           x → {!   !}
        --   (sub x y z) → {!   !}
        --   (neLvl t₁≡t₂) →
        --     Levelₜ₌ _ _
        --       (id (maxᵘⱼ ⊢t₁′ ⊢u₁))
        --       (id (maxᵘⱼ ⊢t₂′ ⊢u₂))
        --       (neLvl (maxᵘˡᵣ t₁≡t₂ u₁≡u₂))
        --   (sym x) → symLevel (⊩maxᵘ≡maxᵘ (Levelₜ₌ _ _ (id {!   !}) (id {!   !}) {!   !}) (symLevel u₁≡u₂))
        --   (trans x y) → {!   !}

opaque

  -- An associativity lemma for levels

  ⊩maxᵘ-assoc :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level v ∷Level →
    Γ ⊩Level (t maxᵘ u) maxᵘ v ≡ t maxᵘ (u maxᵘ v) ∷Level
  ⊩maxᵘ-assoc {t} {u} {v} [t]@(Levelₜ t′ t⇒ propt) [u]@(Levelₜ u′ u⇒ propu) [v]@(Levelₜ v′ v⇒ propv) =
    combineLevel (⊩maxᵘ (⊩maxᵘ [t] [u]) [v]) (⊩maxᵘ [t] (⊩maxᵘ [u] [v]))
      -- (≅ₜ-maxᵘ-assoc (escapeLevel [t]) (escapeLevel [u]) (escapeLevel [v]))
      {!   !}
    -- let
    --   ⊢u = escapeLevel [u]
    --   ⊢v = escapeLevel [v]
    --   ⊢Γ = wfTerm ⊢u
    --   ⊢t′ = escape-Level-prop ⊢Γ propt
    --   ⊢u′ = escape-Level-prop ⊢Γ propu
    --   ⊢v′ = escape-Level-prop ⊢Γ propv
    -- in ⊩Level≡-⇒*
    --   (maxᵘ-substˡ* (maxᵘ-substˡ* t⇒ ⊢u) ⊢v)
    --   (maxᵘ-substˡ* t⇒ (maxᵘⱼ ⊢u ⊢v)) $
    --   case propt of λ where
    --     zeroᵘᵣ → ⊩Level≡-⇒*
    --       (redMany (maxᵘ-substˡ (maxᵘ-zeroˡ ⊢u) ⊢v))
    --       (redMany (maxᵘ-zeroˡ (maxᵘⱼ ⊢u ⊢v)))
    --       (reflLevel (⊩maxᵘ [u] [v]))
    --     (sucᵘᵣ {k = t″} [t″]) →
    --       let ⊢t″ = escapeLevel [t″]
    --       in ⊩Level≡-⇒*
    --         (maxᵘ-substˡ* (maxᵘ-substʳ* ⊢t″ u⇒) ⊢v)
    --         (maxᵘ-substʳ* ⊢t″ (maxᵘ-substˡ* u⇒ ⊢v)) $
    --         case propu of λ where
    --           zeroᵘᵣ → ⊩Level≡-⇒*
    --             (redMany (maxᵘ-substˡ (maxᵘ-zeroʳ ⊢t″) ⊢v))
    --             (redMany (maxᵘ-substʳ ⊢t″ (maxᵘ-zeroˡ ⊢v)))
    --             (reflLevel (⊩maxᵘ (⊩sucᵘ [t″]) [v]))
    --           (sucᵘᵣ {k = u″} [u″]) →
    --             let ⊢u″ = escapeLevel [u″]
    --             in ⊩Level≡-⇒*
    --               (maxᵘ-substˡ (maxᵘ-sucᵘ ⊢t″ ⊢u″) ⊢v ⇨ maxᵘ-substʳ* (maxᵘⱼ ⊢t″ ⊢u″) v⇒)
    --               (maxᵘ-substʳ* ⊢t″ (maxᵘ-substʳ* ⊢u″ v⇒)) $
    --               case propv of λ where
    --                 zeroᵘᵣ → ⊩Level≡-⇒*
    --                   (redMany (maxᵘ-zeroʳ (maxᵘⱼ ⊢t″ ⊢u″)))
    --                   (maxᵘ-substʳ ⊢t″ (maxᵘ-zeroʳ ⊢u″) ⇨ redMany (maxᵘ-sucᵘ ⊢t″ ⊢u″))
    --                   (reflLevel (⊩sucᵘ (⊩maxᵘ [t″] [u″])))
    --                 (sucᵘᵣ {k = v″} [v″]) →
    --                   let ⊢v″ = escapeLevel [v″]
    --                   in ⊩Level≡-⇒*
    --                     (redMany (maxᵘ-sucᵘ (maxᵘⱼ ⊢t″ ⊢u″) ⊢v″))
    --                     (maxᵘ-substʳ ⊢t″ (maxᵘ-sucᵘ ⊢u″ ⊢v″) ⇨ redMany (maxᵘ-sucᵘ ⊢t″ (maxᵘⱼ ⊢u″ ⊢v″)))
    --                     (⊩sucᵘ≡sucᵘ (⊩maxᵘ-assoc [t″] [u″] [v″]))
    --                 (neLvl nepropv) →
    --                   Levelₜ₌ _ _
    --                     (id (maxᵘⱼ (sucᵘⱼ (maxᵘⱼ ⊢t″ ⊢u″)) ⊢v′))
    --                     (id (maxᵘⱼ (sucᵘⱼ ⊢t″) (maxᵘⱼ (sucᵘⱼ ⊢u″) ⊢v′)))
    --                     (neLvl (maxᵘ-assoc³ᵣ (reflLevel [t″]) (reflLevel [u″]) (reflneLevel-prop nepropv)))
    --           (neLvl nepropu) →
    --             Levelₜ₌ _ _
    --               (id (maxᵘⱼ (maxᵘⱼ (sucᵘⱼ ⊢t″) ⊢u′) ⊢v))
    --               (id (maxᵘⱼ (sucᵘⱼ ⊢t″) (maxᵘⱼ ⊢u′ ⊢v)))
    --               (neLvl (maxᵘ-assoc²ᵣ (reflLevel [t″]) (reflneLevel-prop nepropu) (reflLevel [v])))
    --     (neLvl nepropt) →
    --       Levelₜ₌ _ _
    --         (id (maxᵘⱼ (maxᵘⱼ ⊢t′ ⊢u) ⊢v))
    --         (id (maxᵘⱼ ⊢t′ (maxᵘⱼ ⊢u ⊢v)))
    --         (neLvl (maxᵘ-assoc¹ᵣ (reflneLevel-prop nepropt) (reflLevel [u]) (reflLevel [v])))

opaque
  -- private
  --   maxᵘ-zeroʳ′ : ⊢ Γ → Level-prop Γ t → ∃ λ u → Γ ⊢ t maxᵘ zeroᵘ ⇒* u ∷ Level × [Level]-prop Γ u t
  --   maxᵘ-zeroʳ′ ⊢Γ zeroᵘᵣ =
  --     _ , redMany (maxᵘ-zeroˡ (zeroᵘⱼ ⊢Γ)) , zeroᵘᵣ
  --   maxᵘ-zeroʳ′ ⊢Γ (sucᵘᵣ x) =
  --     _ , redMany (maxᵘ-zeroʳ (escapeLevel x)) , sucᵘᵣ (reflLevel x)
  --   maxᵘ-zeroʳ′ ⊢Γ (neLvl n) =
  --       _
  --     , id (maxᵘⱼ (escape-neLevel-prop n) (zeroᵘⱼ ⊢Γ))
  --     , neLvl (maxᵘ-zeroʳˡᵣ (reflneLevel-prop n))

  ⊩maxᵘ-zeroʳ :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ zeroᵘ ≡ t ∷Level
  ⊩maxᵘ-zeroʳ {t} [t] =
    -- let ⊢Γ = wfEqTerm (subset*Term t⇒)
    --     u , k⇒ , u≡k = maxᵘ-zeroʳ′ ⊢Γ prop
    -- in Levelₜ₌ _ _
    --   (t maxᵘ zeroᵘ ⇒*⟨ maxᵘ-substˡ* t⇒ (zeroᵘⱼ ⊢Γ) ⟩
    --    k maxᵘ zeroᵘ ⇒*⟨ k⇒ ⟩∎
    --    u ∎)
    --   t⇒
    --   u≡k
    combineLevel (⊩maxᵘ [t] (⊩zeroᵘ (wfTerm (escapeLevel [t])))) [t]
      -- (≅ₜ-maxᵘ-zeroʳ (escapeLevel [t]))
      {!   !}

opaque

  -- A commutativity lemma for levels

  ⊩maxᵘ-comm :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ≡ u maxᵘ t ∷Level
  ⊩maxᵘ-comm {t} {u} [t]@(Levelₜ t′ t⇒ propt) [u]@(Levelₜ u′ u⇒ propu) =
    combineLevel (⊩maxᵘ [t] [u]) (⊩maxᵘ [u] [t]) {!   !}
    -- let
    --   ⊢t = escapeLevel [t]
    --   ⊢u = escapeLevel [u]
    --   ⊢Γ = wfTerm ⊢u
    --   ⊢t′ = escape-Level-prop ⊢Γ propt
    --   ⊢u′ = escape-Level-prop ⊢Γ propu
    -- in ⊩Level≡-⇒* (maxᵘ-substˡ* t⇒ ⊢u) (id (maxᵘⱼ ⊢u ⊢t)) $ case propt of λ where
    --   zeroᵘᵣ → ⊩Level≡-⇒*
    --     (redMany (maxᵘ-zeroˡ ⊢u))
    --     (id (maxᵘⱼ ⊢u ⊢t))
    --     (transEqTermLevel
    --       (symLevel (⊩maxᵘ-zeroʳ [u]))
    --       (⊩maxᵘ≡maxᵘ (reflLevel [u]) (symLevel (redLevel t⇒ [t]))))
    --   (sucᵘᵣ {k = t′} [t′]) →
    --     let ⊢t′ = escapeLevel [t′]
    --     in
    --       ⊩Level≡-⇒* (maxᵘ-substʳ* ⊢t′ u⇒) (maxᵘ-substˡ* u⇒ ⊢t) $
    --       case propu of λ where
    --         zeroᵘᵣ → ⊩Level≡-⇒*
    --           (redMany (maxᵘ-zeroʳ ⊢t′))
    --           (maxᵘ-zeroˡ ⊢t ⇨ t⇒)
    --           (reflLevel (⊩sucᵘ [t′]))
    --         (sucᵘᵣ {k = u′} [u′]) →
    --           let ⊢u′ = escapeLevel [u′]
    --           in ⊩Level≡-⇒*
    --             (redMany (maxᵘ-sucᵘ ⊢t′ ⊢u′))
    --             (maxᵘ-substʳ* ⊢u′ t⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢u′ ⊢t′))
    --             (⊩sucᵘ≡sucᵘ (⊩maxᵘ-comm [t′] [u′]))
    --         (neLvl [u′]) → Levelₜ₌ _ _
    --           (id (maxᵘⱼ (sucᵘⱼ ⊢t′) ⊢u′))
    --           (id (maxᵘⱼ ⊢u′ ⊢t))
    --           (neLvl (maxᵘ-comm²ᵣ (reflLevel [t′]) (symLevel (redLevel t⇒ [t])) (reflneLevel-prop [u′])))
    --   (neLvl [t′]) → ⊩Level≡-⇒* (id (maxᵘⱼ ⊢t′ ⊢u)) (maxᵘ-substˡ* u⇒ ⊢t) $
    --     case propu of λ where
    --       zeroᵘᵣ → ⊩Level≡-⇒* (id (maxᵘⱼ ⊢t′ ⊢u)) (maxᵘ-zeroˡ ⊢t ⇨ t⇒)
    --         (transEqTermLevel (⊩maxᵘ≡maxᵘ (reflLevel (⊩neLvl [t′])) (redLevel u⇒ [u])) (⊩maxᵘ-zeroʳ (⊩neLvl [t′])))
    --       (sucᵘᵣ {k = u′} [u′]) →
    --         let ⊢u′ = escapeLevel [u′]
    --         in Levelₜ₌ _ _ (id (maxᵘⱼ ⊢t′ ⊢u)) (maxᵘ-substʳ* ⊢u′ t⇒)
    --           (sym (neLvl (maxᵘ-comm²ᵣ (reflLevel [u′]) (symLevel (redLevel u⇒ [u])) (reflneLevel-prop [t′]))))
    --       (neLvl [u′]) →
    --         Levelₜ₌ _ _ (id (maxᵘⱼ ⊢t′ ⊢u)) (id (maxᵘⱼ ⊢u′ ⊢t))
    --           (neLvl (maxᵘ-comm¹ᵣ (reflneLevel-prop [t′]) (symLevel (redLevel t⇒ [t])) (reflneLevel-prop [u′]) (redLevel u⇒ [u])))

opaque

  -- An idempotence lemma for levels

  ⊩maxᵘ-idem :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level t maxᵘ t ≡ t ∷Level
  ⊩maxᵘ-idem {t} [t]@(Levelₜ t′ t⇒ propt) =
    combineLevel (⊩maxᵘ [t] [t]) [t] {!   !}
    -- let
    --   ⊢t = escapeLevel [t]
    --   ⊢Γ = wfTerm ⊢t
    --   ⊢t′ = escape-Level-prop ⊢Γ propt
    -- in ⊩Level≡-⇒* (maxᵘ-substˡ* t⇒ ⊢t) t⇒ $
    --   case propt of λ where
    --     zeroᵘᵣ → redLevel (maxᵘ-zeroˡ ⊢t ⇨ t⇒) (⊩maxᵘ (⊩zeroᵘ ⊢Γ) [t])
    --     (sucᵘᵣ [t′]) →
    --       let ⊢t′ = escapeLevel [t′]
    --       in ⊩Level≡-⇒*
    --         (maxᵘ-substʳ* ⊢t′ t⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢t′ ⊢t′))
    --         (id (sucᵘⱼ ⊢t′))
    --         (⊩sucᵘ≡sucᵘ (⊩maxᵘ-idem [t′]))
    --     (neLvl [t′]) → Levelₜ₌ _ _
    --       (id (maxᵘⱼ ⊢t′ ⊢t))
    --       (id ⊢t′)
    --       (neLvl (maxᵘ-idem (reflneLevel-prop [t′]) (symLevel (redLevel t⇒ [t]))))
