------------------------------------------------------------------------
-- Validity for levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Level
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation.Hidden R {{eqrel}} as H
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Properties.Primitive R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                                          : Con Term _
  A A₁ A₂ B l l′ l″ l‴ t t′ t₁ t₂ u u′ u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                                        : Subst _ _
  p q r                                        : M
  ℓ                                            : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Level⇔ : Γ ⊩⟨ l ⟩ Level ⇔ Γ ⊩Level l ∷Level
  ⊩Level⇔ =
      wfᵘ-⊩
    , λ ⊩l → ⊩l , Levelᵣ (id (Levelⱼ (wfTerm (escapeLevel ⊩l))))

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Level⇔ : Γ ⊩⟨ l ⟩ t ∷ Level ⇔ (Γ ⊩Level l ∷Level × Γ ⊩Level t ∷Level)
  ⊩∷Level⇔ =
      (λ ((⊩l , ⊩L) , ⊩t) →
        case Level-elim ⊩L of λ { (Levelᵣ _) → ⊩l , ⊩t })
    , (λ (⊩l , ⊩t@(Levelₜ _ d _ _)) →
          (⊩l , Levelᵣ (id (Levelⱼ (wfEqTerm (subset*Term d)))))
        , ⊩t)

opaque

  -- A characterisation lemma for _⊩Level_∷Level.

  ⊩Levelzeroᵘ∷Level : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩Levelzeroᵘ∷Level ⊢Γ =
    Levelₜ zeroᵘ (id (zeroᵘⱼ ⊢Γ)) (≅ₜ-zeroᵘrefl ⊢Γ) zeroᵘᵣ

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level ⇔ Γ ⊩Level l ∷Level
  ⊩zeroᵘ∷Level⇔ =
      wfᵘ-⊩∷
    , (λ ⊩l →
         ⊩∷Level⇔ .proj₂ (⊩l , ⊩Levelzeroᵘ∷Level (wfTerm (escapeLevel ⊩l))))

opaque

  ⊩Levelsucᵘ∷Level : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩Levelsucᵘ∷Level ⊩t =
    Levelₜ _ (id (sucᵘⱼ (escapeLevel ⊩t)))
      (≅ₜ-sucᵘ-cong (escapeLevelEq (reflLevel ⊩t)))
      (sucᵘᵣ ⊩t)

opaque

  -- A characterisation lemma for _⊩Level_∷Level.

  ⊩Levelsucᵘ∷Level⇔ :
    Γ ⊩Level sucᵘ t ∷Level ⇔
    Γ ⊩Level t ∷Level
  ⊩Levelsucᵘ∷Level⇔ {Γ} {t} =
    (λ { (Levelₜ _ sucᵘ-t⇒*u _ u-ok) →
          case whnfRed*Term sucᵘ-t⇒*u sucᵘₙ of λ {
            PE.refl →
          lemma u-ok }})
    , ⊩Levelsucᵘ∷Level
    where
    lemma : Level-prop Γ (sucᵘ t) → Γ ⊩Level t ∷Level
    lemma (sucᵘᵣ ⊩t)         = ⊩t
    lemma (ne (neNfₜ () _))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ∷ Level
  ⊩sucᵘ∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level                     ⇔⟨ ⊩∷Level⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩Level sucᵘ t ∷Level  ⇔⟨ id⇔ ×-cong-⇔ ⊩Levelsucᵘ∷Level⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩Level t ∷Level       ⇔˘⟨ ⊩∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ∷ Level                          □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zeroᵘ≡zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level ⇔ Γ ⊩Level l ∷Level
  ⊩zeroᵘ≡zeroᵘ∷Level⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  ⇔⟨ proj₁ ∘→ wf-⊩≡∷ , refl-⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level          ⇔⟨ ⊩zeroᵘ∷Level⇔ ⟩
    Γ ⊩Level l ∷Level               □⇔

opaque

  -- A characterisation lemma for _⊩Level_≡_∷Level_.

  ⊩Levelsucᵘ≡sucᵘ∷Level⇔ :
    Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level ⇔
    Γ ⊩Level t ≡ u ∷Level
  ⊩Levelsucᵘ≡sucᵘ∷Level⇔ {Γ} {t} {u} = lemma₁ , lemma₂
    where
    lemma₀ : [Level]-prop Γ (sucᵘ t) (sucᵘ u) → Γ ⊩Level t ≡ u ∷Level
    lemma₀ (sucᵘᵣ t≡u)           = t≡u
    lemma₀ (ne (neNfₜ₌ () _ _))

    lemma₁ : Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level → Γ ⊩Level t ≡ u ∷Level
    lemma₁ (Levelₜ₌ _ _ sucᵘ-t⇒*t′ sucᵘ-u⇒*u′ _ t′≡u′) =
      case whnfRed*Term sucᵘ-t⇒*t′ sucᵘₙ of λ {
        PE.refl →
      case whnfRed*Term sucᵘ-u⇒*u′ sucᵘₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

    lemma₂ : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
    lemma₂
      t≡u@(Levelₜ₌ _ _ t⇒*t′ u⇒*u′ t′≅u′ t′≡u′) =
      let t′-ok , u′-ok = lsplit t′≡u′
          ⊢t = redFirst*Term t⇒*t′
          ⊢u = redFirst*Term u⇒*u′
      in
      Levelₜ₌ _ _ (id (sucᵘⱼ ⊢t)) (id (sucᵘⱼ ⊢u))
        (≅ₜ-sucᵘ-cong $
         ≅ₜ-red (id (Levelⱼ (wfTerm ⊢t)) , Levelₙ) (t⇒*t′ , t′-ok)
           (u⇒*u′ , u′-ok) t′≅u′)
        (sucᵘᵣ t≡u)

opaque

  -- A characterisation lemma for _⊩Level_≡_∷Level.

  -- TODO: ↑ᵘ sends maxᵘ to ⊔ᵘ

  ⊩Levelmaxᵘ≡maxᵘ∷Level :
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷Level
  ⊩Levelmaxᵘ≡maxᵘ∷Level {t₁} {t₂} {u₁} {u₂}
    (Levelₜ₌ .zeroᵘ .zeroᵘ t₁⇒ t₂⇒ _ zeroᵘᵣ)
    u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ u₁′≡u₂′ prop′) =
    let ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢u₁       = escapeLevel ⊩u₁
        ⊢u₂       = escapeLevel ⊩u₂
    in Levelₜ₌ u₁′ u₂′
      (t₁    maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
       zeroᵘ maxᵘ u₁  ⇒⟨ maxᵘ-zeroˡ ⊢u₁ ⟩
                  u₁  ⇒*⟨ u₁⇒ ⟩∎
                  u₁′ ∎)
      (t₂    maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
       zeroᵘ maxᵘ u₂  ⇒⟨ maxᵘ-zeroˡ ⊢u₂ ⟩
                  u₂  ⇒*⟨ u₂⇒ ⟩∎
                  u₂′ ∎)
      u₁′≡u₂′
      prop′
  ⊩Levelmaxᵘ≡maxᵘ∷Level {t₁} {t₂} {u₁} {u₂}
    (Levelₜ₌ .(sucᵘ t₁′) .(sucᵘ t₂′) t₁⇒ t₂⇒ t₁′≡t₂′ (sucᵘᵣ {k = t₁′} {k′ = t₂′} ⊩t₁′≡t₂′))
    u₁≡u₂@(Levelₜ₌ .zeroᵘ .zeroᵘ u₁⇒ u₂⇒ _ zeroᵘᵣ) =
    let ⊩t₁′ , ⊩t₂′ = wf-⊩Level ⊩t₁′≡t₂′
        ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢t₁′ = escapeLevel ⊩t₁′
        ⊢t₂′ = escapeLevel ⊩t₂′
        ⊢u₁  = escapeLevel ⊩u₁
        ⊢u₂  = escapeLevel ⊩u₂
    in Levelₜ₌ (sucᵘ t₁′) (sucᵘ t₂′)
      (t₁       maxᵘ u₁    ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
       sucᵘ t₁′ maxᵘ u₁    ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ ⟩
       sucᵘ t₁′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₁′ ⟩∎
       sucᵘ t₁′            ∎)
      (t₂       maxᵘ u₂    ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
       sucᵘ t₂′ maxᵘ u₂    ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ ⟩
       sucᵘ t₂′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₂′ ⟩∎
       sucᵘ t₂′            ∎)
      t₁′≡t₂′
      (sucᵘᵣ ⊩t₁′≡t₂′)
  ⊩Levelmaxᵘ≡maxᵘ∷Level {t₁} {t₂} {u₁} {u₂}
    (Levelₜ₌ .(sucᵘ t₁′) .(sucᵘ t₂′) t₁⇒ t₂⇒ _ (sucᵘᵣ {k = t₁′} {k′ = t₂′} ⊩t₁′≡t₂′))
    u₁≡u₂@(Levelₜ₌ .(sucᵘ u₁′) .(sucᵘ u₂′) u₁⇒ u₂⇒ _ (sucᵘᵣ {k = u₁′} {k′ = u₂′} ⊩u₁′≡u₂′)) =
    let ⊩t₁′ , ⊩t₂′ = wf-⊩Level ⊩t₁′≡t₂′
        ⊩u₁′ , ⊩u₂′ = wf-⊩Level ⊩u₁′≡u₂′
        ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢t₁′ = escapeLevel ⊩t₁′
        ⊢t₂′ = escapeLevel ⊩t₂′
        ⊢u₁′ = escapeLevel ⊩u₁′
        ⊢u₂′ = escapeLevel ⊩u₂′
        ⊢u₁  = escapeLevel ⊩u₁
        ⊢u₂  = escapeLevel ⊩u₂
        x₁≡x₂ = ⊩Levelmaxᵘ≡maxᵘ∷Level ⊩t₁′≡t₂′ ⊩u₁′≡u₂′
    in Levelₜ₌ (sucᵘ (t₁′ maxᵘ u₁′)) (sucᵘ (t₂′ maxᵘ u₂′))
      (t₁       maxᵘ u₁       ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
       sucᵘ t₁′ maxᵘ u₁       ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ ⟩
       sucᵘ t₁′ maxᵘ sucᵘ u₁′ ⇒⟨ maxᵘ-sucᵘ ⊢t₁′ ⊢u₁′ ⟩∎
       sucᵘ (t₁′ maxᵘ u₁′)    ∎)
      (t₂       maxᵘ u₂       ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
       sucᵘ t₂′ maxᵘ u₂       ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ ⟩
       sucᵘ t₂′ maxᵘ sucᵘ u₂′ ⇒⟨ maxᵘ-sucᵘ ⊢t₂′ ⊢u₂′ ⟩∎
       sucᵘ (t₂′ maxᵘ u₂′)    ∎)
      (escapeLevelEq (⊩Levelsucᵘ≡sucᵘ∷Level⇔ .proj₂ x₁≡x₂))
      (sucᵘᵣ x₁≡x₂)
  ⊩Levelmaxᵘ≡maxᵘ∷Level {t₁} {t₂} {u₁} {u₂}
    (Levelₜ₌ .(sucᵘ t₁′) .(sucᵘ t₂′) t₁⇒ t₂⇒ _ (sucᵘᵣ {k = t₁′} {k′ = t₂′} ⊩t₁′≡t₂′))
    u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ u₁′≡u₂′ (ne (neNfₜ₌ n₁ n₂ u₁′~u₂′))) =
    let ⊩t₁′ , ⊩t₂′ = wf-⊩Level ⊩t₁′≡t₂′
        ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢t₁′ = escapeLevel ⊩t₁′
        ⊢t₂′ = escapeLevel ⊩t₂′
        ⊢u₁  = escapeLevel ⊩u₁
        ⊢u₂  = escapeLevel ⊩u₂
        x₁~x₂ = ≅ₜ-maxᵘ-congʳ (escapeLevelEq ⊩t₁′≡t₂′) u₁′~u₂′
    in Levelₜ₌ (sucᵘ t₁′ maxᵘ u₁′) (sucᵘ t₂′ maxᵘ u₂′)
      (t₁       maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
       sucᵘ t₁′ maxᵘ u₁  ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ ⟩∎
       sucᵘ t₁′ maxᵘ u₁′ ∎)
      (t₂       maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
       sucᵘ t₂′ maxᵘ u₂  ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ ⟩∎
       sucᵘ t₂′ maxᵘ u₂′ ∎)
      (~-to-≅ₜ x₁~x₂)
      (ne (neNfₜ₌ (maxᵘʳₙ n₁) (maxᵘʳₙ n₂) x₁~x₂))
  ⊩Levelmaxᵘ≡maxᵘ∷Level {t₁} {t₂} {u₁} {u₂}
    t₁≡t₂@(Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ _ (ne (neNfₜ₌ n₁ n₂ t₁′~t₂′)))
    u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ _ prop′) =
    let ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢u₁ = escapeLevel ⊩u₁
        ⊢u₂ = escapeLevel ⊩u₂
        x₁~x₂ = ≅ₜ-maxᵘ-congˡ t₁′~t₂′ (escapeLevelEq u₁≡u₂)
    in Levelₜ₌ (t₁′ maxᵘ u₁) (t₂′ maxᵘ u₂)
      (t₁  maxᵘ u₁ ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩∎
       t₁′ maxᵘ u₁ ∎)
      (t₂  maxᵘ u₂ ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩∎
       t₂′ maxᵘ u₂ ∎)
      (~-to-≅ₜ x₁~x₂)
      (ne (neNfₜ₌ (maxᵘˡₙ n₁) (maxᵘˡₙ n₂) x₁~x₂))

opaque

  -- A characterisation lemma for _⊩Level_∷Level.

  ⊩Levelmaxᵘ∷Level :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ∷Level
  ⊩Levelmaxᵘ∷Level ⊩t ⊩u = proj₁ $ wf-⊩Level $
    ⊩Levelmaxᵘ≡maxᵘ∷Level (reflLevel ⊩t) (reflLevel ⊩u)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Level≡⇔ : Γ ⊩⟨ l ⟩ Level ≡ A ⇔ (Γ ⊩Level l ∷Level × Γ ⊩Level Level ≡ A)
  ⊩Level≡⇔ =
      (λ ((⊩l , ⊩Level) , _ , Level≡A) →
        case Level-elim ⊩Level of λ { (Levelᵣ _) → ⊩l , Level≡A })
    , (λ (⊩l , Level≡A) →
        case id (Levelⱼ (wfEq (subset* Level≡A))) of λ
          Level⇒*Level →
        let ⊩Level = Levelᵣ Level⇒*Level in
          (⊩l , ⊩Level)
        , (⊩l , (redSubst* Level≡A ⊩Level) .proj₁)
        , Level≡A)

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Level⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level ⇔
    (Γ ⊩Level l ∷Level × Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level × Γ ⊩Level t ≡ u ∷Level)
  ⊩≡∷Level⇔ =
      (λ ((⊩l , ⊩Level) , ⊩t , ⊩u , t≡u) →
        case Level-elim ⊩Level of λ { (Levelᵣ _) → ⊩l , ⊩t , ⊩u , t≡u })
    , (λ (⊩l , ⊩t , ⊩u , t≡u@(Levelₜ₌ _ _ d _ _ _)) →
         (⊩l , Levelᵣ (id (Levelⱼ (wfEqTerm (subset*Term d)))))
       , ⊩t , ⊩u , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩sucᵘ≡sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
      ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩Level sucᵘ t ∷Level × Γ ⊩Level sucᵘ u ∷Level × Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
      ⇔⟨ id⇔ ×-cong-⇔ ⊩Levelsucᵘ∷Level⇔ ×-cong-⇔ ⊩Levelsucᵘ∷Level⇔ ×-cong-⇔ ⊩Levelsucᵘ≡sucᵘ∷Level⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩Level t ∷Level × Γ ⊩Level u ∷Level × Γ ⊩Level t ≡ u ∷Level
      ⇔˘⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level  □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩maxᵘ≡maxᵘ∷Level :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩⟨ l ⟩ t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷ Level
  ⊩maxᵘ≡maxᵘ∷Level t₁≡t₂ u₁≡u₂ =
    case ⊩≡∷Level⇔ .proj₁ t₁≡t₂ of λ
      (⊩l , ⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩≡∷Level⇔ .proj₁ u₁≡u₂ of λ
      (_  , ⊩u₁ , ⊩u₂ , u₁≡u₂) →
    ⊩≡∷Level⇔ .proj₂
      ( ⊩l
      , ⊩Levelmaxᵘ∷Level ⊩t₁ ⊩u₁
      , ⊩Levelmaxᵘ∷Level ⊩t₂ ⊩u₂
      , ⊩Levelmaxᵘ≡maxᵘ∷Level t₁≡t₂ u₁≡u₂
      )

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zeroᵘ≡sucᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ sucᵘ t ∷ Level ⇔ ⊥
  ⊩zeroᵘ≡sucᵘ∷Level⇔ =
      (λ zeroᵘ≡sucᵘ →
         case ⊩≡∷Level⇔ .proj₁ zeroᵘ≡sucᵘ of λ {
           (_ , _ , _ , Levelₜ₌ _ _ zeroᵘ⇒* sucᵘ⇒* _ rest) →
         case whnfRed*Term zeroᵘ⇒* zeroᵘₙ of λ {
           PE.refl →
         case whnfRed*Term sucᵘ⇒* sucᵘₙ of λ {
           PE.refl →
         case rest of λ where
           (ne (neNfₜ₌ () _ _)) }}})
    , ⊥-elim

------------------------------------------------------------------------
-- zeroᵘ and sucᵘ are valid level constructors

opaque

  -- Level validity of zeroᵘ.

  zeroᵘᵛᵘ : ⊩ᵛ Γ → Γ ⊩ᵛᵘ zeroᵘ
  zeroᵘᵛᵘ ⊩Γ = ⊩ᵛᵘ⇔ .proj₂
    ( ⊩Γ
    , reflLevel ∘→ ⊩Levelzeroᵘ∷Level ∘→ proj₁ ∘→ escape-⊩ˢ≡∷
    )

opaque

  -- Level validity of sucᵘ.

  sucᵘᵛᵘ : Γ ⊩ᵛᵘ l → Γ ⊩ᵛᵘ sucᵘ l
  sucᵘᵛᵘ ⊩l = ⊩ᵛᵘ⇔ .proj₂
    ( wf-⊩ᵛᵘ ⊩l
    , ⊩Levelsucᵘ≡sucᵘ∷Level⇔ .proj₂ ∘→ ⊩ᵛᵘ→⊩ˢ≡∷→⊩[]≡[] ⊩l
    )

------------------------------------------------------------------------
-- Level

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛLevel⇔ : Γ ⊩ᵛ⟨ l ⟩ Level ⇔ Γ ⊩ᵛᵘ l
  ⊩ᵛLevel⇔ {Γ} {l} =
      wfᵘ-⊩ᵛ
    , λ ⊩l →
        ⊩ᵛ⇔ .proj₂
          ( ⊩l
          , λ {_} {Δ} {σ₁} {σ₂} σ₁≡σ₂ →
              ⊩Level≡⇔ .proj₂
                ( ⊩ᵛᵘ→⊩ˢ∷→⊩[] ⊩l (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
                , id (Levelⱼ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁))
                )
          )

opaque

  -- Validity of Level.

  Levelᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ zeroᵘ ⟩ Level
  Levelᵛ = ⊩ᵛLevel⇔ .proj₂ ∘→ zeroᵘᵛᵘ

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷Level⇔ : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level ⇔ (Γ ⊩ᵛᵘ l × Γ ⊩ᵛᵘ t)
  ⊩ᵛ∷Level⇔ {Γ} {l} {t} =
    (λ ⊩t →
        ⊩ᵛ⇔ .proj₁ (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₁) .proj₁
      , ⊩ᵛᵘ⇔ .proj₂
        ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
        , λ σ₁≡σ₂ →
            case ⊩≡∷Level⇔ .proj₁ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (refl-⊩ᵛ≡∷ ⊩t) σ₁≡σ₂) of λ
              (_ , _ , _ , t[σ₁]≡t[σ₂]) →
            t[σ₁]≡t[σ₂]
        ))
    , λ (⊩l , ⊩t) →
        ⊩ᵛ∷⇔ .proj₂
          ( ⊩ᵛLevel⇔ .proj₂ ⊩l
          , λ σ₁≡σ₂ →
              ⊩≡∷Level⇔ .proj₂
                ( ⊩ᵛᵘ→⊩ˢ∷→⊩[] ⊩l (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
                , ⊩ᵛᵘ→⊩ˢ∷→⊩[] ⊩t (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
                , ⊩ᵛᵘ→⊩ˢ∷→⊩[] ⊩t (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂)
                , ⊩ᵛᵘ→⊩ˢ≡∷→⊩[]≡[] ⊩t σ₁≡σ₂
                )
          )

------------------------------------------------------------------------
-- zeroᵘ and sucᵘ are valid term constructors

opaque

  -- Validity of zeroᵘ.

  zeroᵘᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ zeroᵘ ⟩ zeroᵘ ∷ Level
  zeroᵘᵛ ⊩Γ = ⊩ᵛ∷Level⇔ .proj₂ (zeroᵘᵛᵘ ⊩Γ , zeroᵘᵛᵘ ⊩Γ)


opaque

  -- Reducibility of equality between applications of suc.

  ⊩sucᵘ≡sucᵘ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  ⊩sucᵘ≡sucᵘ = ⊩sucᵘ≡sucᵘ∷Level⇔ .proj₂

opaque

  -- Validity of equality preservation for sucᵘ.

  sucᵘ-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level
  sucᵘ-congᵛ t≡u =
    ⊩ᵛ≡∷⇔ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁)
      , ⊩sucᵘ≡sucᵘ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u
      )

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ∷ Level
  sucᵘᵛ = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ sucᵘ-congᵛ ∘→ refl-⊩ᵛ≡∷

opaque

  maxᵘ-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷ Level
  maxᵘ-congᵛ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ σ₁≡σ₂ → ⊩maxᵘ≡maxᵘ∷Level
          (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
          (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
      )

------------------------------------------------------------------------

{-
opaque
  ↑ᵘ-suc : (⊩t : Γ ⊩Level t ∷Level) → ↑ᵘ ⊩t <ᵘ ↑ᵘ ⊩Level-sucᵘ ⊩t
  ↑ᵘ-suc ⊩t = ≤ᵘ-refl
-}

opaque
  unfolding _⊩_≤_∷Level

  ≡-≤-Level :
    Γ ⊩Level t ≡ u ∷Level →
    Γ ⊩ u ≤ v ∷Level →
    Γ ⊩ t ≤ v ∷Level
  ≡-≤-Level t≡u (⊩u , ⊩v , u≤v) =
    let ⊩t = wf-⊩Level t≡u .proj₁ in
      ⊩t
    , ⊩v
    , PE.subst (_≤ᵘ _) (↑ᵘ-cong ⊩u ⊩t (symLevel t≡u)) u≤v

opaque
  unfolding _⊩_<_∷Level

  ≡-<-Level :
    Γ ⊩Level t ≡ u ∷Level →
    Γ ⊩ u < v ∷Level →
    Γ ⊩ t < v ∷Level
  ≡-<-Level t≡u (⊩u , ⊩v , u<v) =
    let ⊩t = wf-⊩Level t≡u .proj₁ in
      ⊩t
    , ⊩v
    , PE.subst (_<ᵘ _) (↑ᵘ-cong ⊩u ⊩t (symLevel t≡u)) u<v

opaque
  unfolding _⊩_<_∷Level

  <-sucᵘ : Γ ⊩Level l ∷Level → Γ ⊩ l < sucᵘ l ∷Level
  <-sucᵘ ⊩l = ⊩l , ⊩Levelsucᵘ∷Level ⊩l , {!   !}

opaque
  unfolding _⊩_≤_∷Level

  ≤-reflᵘ : Γ ⊩Level l ∷Level → Γ ⊩ l ≤ l ∷Level
  ≤-reflᵘ ⊩l = ⊩l , ⊩l , ≤ᵘ-refl

opaque

  zeroᵘ<oneᵘ : ⊢ Γ → Γ ⊩ zeroᵘ < sucᵘ zeroᵘ ∷Level
  zeroᵘ<oneᵘ ⊢Γ = <-sucᵘ (⊩Levelzeroᵘ∷Level ⊢Γ)
