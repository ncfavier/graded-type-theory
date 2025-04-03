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

open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R {{eqrel}}
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Unary R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
import Definition.Typed.Stability R as S
open import Definition.Typed.Substitution R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                               : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                             : Subst _ _
  l l′ l″ l‴                        : Universe-level
  p q r                             : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Level⇔ : Γ ⊩⟨ l ⟩ Level ⇔ ⊢ Γ
  ⊩Level⇔ =
      (λ ⊩Level →
        case Level-view ⊩Level of λ {
          (Levelᵣ Level⇒*Level) →
        wfEq (subset* Level⇒*Level) })
    , (λ ⊢Γ → Levelᵣ (id (Levelⱼ ⊢Γ)))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Level≡⇔ : Γ ⊩⟨ l ⟩ Level ≡ A ⇔ Γ ⊩Level Level ≡ A
  ⊩Level≡⇔ =
      (λ (⊩Level , _ , Level≡A) →
         case Level-view ⊩Level of λ {
           (Levelᵣ _) →
         Level≡A })
    , (λ Level≡A →
         case id (Levelⱼ (wfEq (subset* Level≡A))) of λ
           Level⇒*Level →
         let ⊩Level = Levelᵣ Level⇒*Level in
           ⊩Level
         , (redSubst* Level≡A ⊩Level) .proj₁
         , Level≡A)

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Level⇔ : Γ ⊩⟨ l ⟩ t ≡ u ∷ Level ⇔ Γ ⊩Level t ≡ u ∷Level
  ⊩≡∷Level⇔ =
      (λ (⊩Level , t≡u) →
         case Level-view ⊩Level of λ {
           (Levelᵣ _) →
         t≡u })
    , (λ t≡u →
         Levelᵣ (id (Levelⱼ (wfEqTerm (subset*Term (_⊩Level_≡_∷Level.d t≡u))))) , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Level⇔ : Γ ⊩⟨ l ⟩ t ∷ Level ⇔ Γ ⊩Level t ∷Level
  ⊩∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ Level      ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level  ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level t ≡ t ∷Level       ⇔⟨ id⇔ ⟩
    Γ ⊩Level t ∷Level           □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩Levelzeroᵘ∷Level : ⊢ Γ → Γ ⊩Level zeroᵘ ∷Level
  ⊩Levelzeroᵘ∷Level ⊢Γ =
    Levelₜ₌ _ _ (id (zeroᵘⱼ ⊢Γ)) (id (zeroᵘⱼ ⊢Γ)) zeroᵘᵣ

  ⊩zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level ⇔ ⊢ Γ
  ⊩zeroᵘ∷Level⇔ =
      wfTerm ∘→ escape-⊩∷
    , ⊩∷Level⇔ .proj₂ ∘→ ⊩Levelzeroᵘ∷Level

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zeroᵘ≡zeroᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level ⇔ ⊢ Γ
  ⊩zeroᵘ≡zeroᵘ∷Level⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zeroᵘ ∷ Level         ⇔⟨ ⊩zeroᵘ∷Level⇔ ⟩
    ⊢ Γ                       □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩Levelsucᵘ≡sucᵘ∷Level : Γ ⊩Level t ≡ u ∷Level → Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level
  ⊩Levelsucᵘ≡sucᵘ∷Level
    t≡u@(Levelₜ₌ _ _ t⇒*t′ u⇒*u′ t′≡u′) =
    let t′-ok , u′-ok = lsplit t′≡u′ in
    Levelₜ₌ _ _
      (id (sucᵘⱼ (redFirst*Term t⇒*t′)))
      (id (sucᵘⱼ (redFirst*Term u⇒*u′)))
      (sucᵘᵣ t≡u)

  ⊩Levelsucᵘ≡sucᵘ∷Level⇔ :
    Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level ⇔
    Γ ⊩Level t ≡ u ∷Level
  ⊩Levelsucᵘ≡sucᵘ∷Level⇔ {Γ} {t} {u} = lemma₁ , ⊩Levelsucᵘ≡sucᵘ∷Level
    where
    lemma₀ : [Level]-prop Γ (sucᵘ t) (sucᵘ u) → Γ ⊩Level t ≡ u ∷Level
    lemma₀ (sucᵘᵣ t≡u)             = t≡u
    lemma₀ (ne (neLvlₜ₌ (ne ()) _ _))

    lemma₁ : Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level → Γ ⊩Level t ≡ u ∷Level
    lemma₁ (Levelₜ₌ _ _ sucᵘ-t⇒*t′ sucᵘ-u⇒*u′ t′≡u′) =
      case whnfRed*Term sucᵘ-t⇒*t′ sucᵘₙ of λ {
        PE.refl →
      case whnfRed*Term sucᵘ-u⇒*u′ sucᵘₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

  ⊩sucᵘ≡sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level
  ⊩sucᵘ≡sucᵘ∷Level⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ u ∷ Level  ⇔⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩Level sucᵘ t ≡ sucᵘ u ∷Level   ⇔⟨ ⊩Levelsucᵘ≡sucᵘ∷Level⇔ ⟩
    Γ ⊩Level t ≡ u ∷Level             ⇔˘⟨ ⊩≡∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Level            □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩Levelsucᵘ∷Level : Γ ⊩Level t ∷Level → Γ ⊩Level sucᵘ t ∷Level
  ⊩Levelsucᵘ∷Level = ⊩Levelsucᵘ≡sucᵘ∷Level

  ⊩sucᵘ∷Level⇔ :
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level ⇔
    Γ ⊩⟨ l ⟩ t ∷ Level
  ⊩sucᵘ∷Level⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level          ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ sucᵘ t ≡ sucᵘ t ∷ Level  ⇔⟨ ⊩sucᵘ≡sucᵘ∷Level⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Level          ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ∷ Level              □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zeroᵘ≡sucᵘ∷Level⇔ : Γ ⊩⟨ l ⟩ zeroᵘ ≡ sucᵘ t ∷ Level ⇔ ⊥
  ⊩zeroᵘ≡sucᵘ∷Level⇔ =
      (λ zeroᵘ≡sucᵘ →
         case ⊩≡∷Level⇔ .proj₁ zeroᵘ≡sucᵘ of λ {
           (Levelₜ₌ _ _ zeroᵘ⇒* sucᵘ⇒* rest) →
         case whnfRed*Term zeroᵘ⇒* zeroᵘₙ of λ {
           PE.refl →
         case whnfRed*Term sucᵘ⇒* sucᵘₙ of λ {
           PE.refl →
         case rest of λ where
           (ne (neLvlₜ₌ (ne ()) _ _)) }}})
    , ⊥-elim

opaque

  -- A characterisation lemma for _⊩Level_≡_∷Level.

  ⊩Levelmaxᵘ≡maxᵘ∷Level :
    Γ ⊩Level t₁ ≡ t₂ ∷Level →
    Γ ⊩Level u₁ ≡ u₂ ∷Level →
    Γ ⊩Level t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷Level
  ⊩Levelmaxᵘ≡maxᵘ∷Level {t₁} {t₂} {u₁} {u₂}
    t₁≡t₂@(Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ propt)
    u₁≡u₂@(Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu)
    =
    let ⊩t₁ , ⊩t₂ = wf-⊩Level t₁≡t₂
        ⊩u₁ , ⊩u₂ = wf-⊩Level u₁≡u₂
        ⊢t₁ = escapeLevel ⊩t₁
        ⊢t₂ = escapeLevel ⊩t₂
        ⊢u₁ = escapeLevel ⊩u₁
        ⊢u₂ = escapeLevel ⊩u₂
    in case propt of λ where
        zeroᵘᵣ → Levelₜ₌ u₁′ u₂′
          (t₁    maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
           zeroᵘ maxᵘ u₁  ⇒⟨ maxᵘ-zeroˡ ⊢u₁ ⟩
                      u₁  ⇒*⟨ u₁⇒ ⟩∎
                      u₁′ ∎)
          (t₂    maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
           zeroᵘ maxᵘ u₂  ⇒⟨ maxᵘ-zeroˡ ⊢u₂ ⟩
                      u₂  ⇒*⟨ u₂⇒ ⟩∎
                      u₂′ ∎)
          propu
        (sucᵘᵣ {k = t₁′} {k′ = t₂′} t₁′≡t₂′) →
          let ⊩t₁′ , ⊩t₂′ = wf-⊩Level t₁′≡t₂′
              ⊢t₁′ = escapeLevel ⊩t₁′
              ⊢t₂′ = escapeLevel ⊩t₂′
          in case propu of λ where
            zeroᵘᵣ → Levelₜ₌ (sucᵘ t₁′) (sucᵘ t₂′)
              (t₁       maxᵘ u₁    ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
               sucᵘ t₁′ maxᵘ u₁    ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ ⟩
               sucᵘ t₁′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₁′ ⟩∎
               sucᵘ t₁′            ∎)
              (t₂       maxᵘ u₂    ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
               sucᵘ t₂′ maxᵘ u₂    ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ ⟩
               sucᵘ t₂′ maxᵘ zeroᵘ ⇒⟨ maxᵘ-zeroʳ ⊢t₂′ ⟩∎
               sucᵘ t₂′            ∎)
              (sucᵘᵣ t₁′≡t₂′)
            (sucᵘᵣ {k = u₁′} {k′ = u₂′} u₁′≡u₂′) →
              let ⊩u₁′ , ⊩u₂′ = wf-⊩Level u₁′≡u₂′
                  ⊢u₁′ = escapeLevel ⊩u₁′
                  ⊢u₂′ = escapeLevel ⊩u₂′
              in Levelₜ₌ (sucᵘ (t₁′ maxᵘ u₁′)) (sucᵘ (t₂′ maxᵘ u₂′))
                (t₁       maxᵘ u₁       ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
                 sucᵘ t₁′ maxᵘ u₁       ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ ⟩
                 sucᵘ t₁′ maxᵘ sucᵘ u₁′ ⇒⟨ maxᵘ-sucᵘ ⊢t₁′ ⊢u₁′ ⟩∎
                 sucᵘ (t₁′ maxᵘ u₁′)    ∎)
                (t₂       maxᵘ u₂       ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
                 sucᵘ t₂′ maxᵘ u₂       ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ ⟩
                 sucᵘ t₂′ maxᵘ sucᵘ u₂′ ⇒⟨ maxᵘ-sucᵘ ⊢t₂′ ⊢u₂′ ⟩∎
                 sucᵘ (t₂′ maxᵘ u₂′)    ∎)
                (sucᵘᵣ (⊩Levelmaxᵘ≡maxᵘ∷Level t₁′≡t₂′ u₁′≡u₂′))
            (ne u₁′≡u₂′@(neLvlₜ₌ n₁ n₂ prop)) →
              Levelₜ₌ (sucᵘ t₁′ maxᵘ u₁′) (sucᵘ t₂′ maxᵘ u₂′)
                (t₁       maxᵘ u₁  ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩
                 sucᵘ t₁′ maxᵘ u₁  ⇒*⟨ maxᵘ-substʳ* ⊢t₁′ u₁⇒ ⟩∎
                 sucᵘ t₁′ maxᵘ u₁′ ∎)
                (t₂       maxᵘ u₂  ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩
                 sucᵘ t₂′ maxᵘ u₂  ⇒*⟨ maxᵘ-substʳ* ⊢t₂′ u₂⇒ ⟩∎
                 sucᵘ t₂′ maxᵘ u₂′ ∎)
                (ne (neLvlₜ₌ (maxᵘʳₙ n₁) (maxᵘʳₙ n₂) (maxᵘʳᵣ t₁′≡t₂′ u₁′≡u₂′)))
        (ne t₁′≡t₂′@(neLvlₜ₌ n₁ n₂ prop)) →
          Levelₜ₌ (t₁′ maxᵘ u₁) (t₂′ maxᵘ u₂)
            (t₁  maxᵘ u₁ ⇒*⟨ maxᵘ-substˡ* t₁⇒ ⊢u₁ ⟩∎
             t₁′ maxᵘ u₁ ∎)
            (t₂  maxᵘ u₂ ⇒*⟨ maxᵘ-substˡ* t₂⇒ ⊢u₂ ⟩∎
             t₂′ maxᵘ u₂ ∎)
            (ne (neLvlₜ₌ (maxᵘˡₙ n₁) (maxᵘˡₙ n₂) (maxᵘˡᵣ t₁′≡t₂′ u₁≡u₂)))

opaque
  unfolding ⊩Levelmaxᵘ≡maxᵘ∷Level ↑ᵘ′_

  ↑ᵘ′-maxᵘ≡maxᵘ :
    (t₁≡t₂ : Γ ⊩Level t₁ ≡ t₂ ∷Level) →
    (u₁≡u₂ : Γ ⊩Level u₁ ≡ u₂ ∷Level) →
    ↑ᵘ′ (⊩Levelmaxᵘ≡maxᵘ∷Level t₁≡t₂ u₁≡u₂) PE.≡ ↑ᵘ′ t₁≡t₂ ⊔ ↑ᵘ′ u₁≡u₂
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ zeroᵘᵣ) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (sucᵘᵣ x)) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ zeroᵘᵣ) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (sucᵘᵣ t₁′≡t₂′)) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ (sucᵘᵣ u₁′≡u₂′)) = PE.cong 1+ (↑ᵘ′-maxᵘ≡maxᵘ t₁′≡t₂′ u₁′≡u₂′)
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (sucᵘᵣ x)) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ (ne record{})) = PE.refl
  ↑ᵘ′-maxᵘ≡maxᵘ (Levelₜ₌ t₁′ t₂′ t₁⇒ t₂⇒ (ne record{})) (Levelₜ₌ u₁′ u₂′ u₁⇒ u₂⇒ propu) = PE.refl

  ↑ᵘ-maxᵘ≡maxᵘ :
    (t₁≡t₂ : Γ ⊩Level t₁ ≡ t₂ ∷Level) →
    (u₁≡u₂ : Γ ⊩Level u₁ ≡ u₂ ∷Level) →
    ↑ᵘ (⊩Levelmaxᵘ≡maxᵘ∷Level t₁≡t₂ u₁≡u₂) PE.≡ ↑ᵘ t₁≡t₂ ⊔ᵘ ↑ᵘ u₁≡u₂
  ↑ᵘ-maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂ = PE.cong 0ᵘ+_ (↑ᵘ′-maxᵘ≡maxᵘ t₁≡t₂ u₁≡u₂)

opaque

  -- A characterisation lemma for _⊩Level_∷Level.

  ⊩Levelmaxᵘ∷Level :
    Γ ⊩Level t ∷Level →
    Γ ⊩Level u ∷Level →
    Γ ⊩Level t maxᵘ u ∷Level
  ⊩Levelmaxᵘ∷Level ⊩t ⊩u = ⊩Levelmaxᵘ≡maxᵘ∷Level ⊩t ⊩u

  ↑ᵘ-maxᵘ :
    (⊩t : Γ ⊩Level t ∷Level) →
    (⊩u : Γ ⊩Level u ∷Level) →
    ↑ᵘ (⊩Levelmaxᵘ∷Level ⊩t ⊩u) PE.≡ ↑ᵘ ⊩t ⊔ᵘ ↑ᵘ ⊩u
  ↑ᵘ-maxᵘ ⊩t ⊩u = ↑ᵘ-maxᵘ≡maxᵘ ⊩t ⊩u

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩maxᵘ≡maxᵘ∷Level :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩⟨ l ⟩ t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷ Level
  ⊩maxᵘ≡maxᵘ∷Level t₁≡t₂ u₁≡u₂ =
    ⊩≡∷Level⇔ .proj₂ $ ⊩Levelmaxᵘ≡maxᵘ∷Level
      (⊩≡∷Level⇔ .proj₁ t₁≡t₂)
      (⊩≡∷Level⇔ .proj₁ u₁≡u₂)

opaque

  ⊩maxᵘ-zeroˡ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ zeroᵘ maxᵘ t ≡ t ∷ Level
  ⊩maxᵘ-zeroˡ ⊩t = ⊩∷-⇐* (redMany (maxᵘ-zeroˡ (escape-⊩∷ ⊩t))) ⊩t

opaque

  ⊩maxᵘ-zeroʳ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ t maxᵘ zeroᵘ ≡ t ∷ Level
  ⊩maxᵘ-zeroʳ ⊩t = ⊩∷-⇐* {!   !} ⊩t

------------------------------------------------------------------------
-- Level

opaque

  -- Validity of Level, seen as a type former.

  Levelᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ Level
  Levelᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ  →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ               →⟨ Levelⱼ ⟩
          (Δ ⊢ Level)           →⟨ id ⟩
          Δ ⊢ Level ⇒* Level        ⇔˘⟨ ⊩Level≡⇔ ⟩→
          Δ ⊩⟨ l ⟩ Level ≡ Level    □
      )

------------------------------------------------------------------------
-- The constructors zeroᵘ and sucᵘ

opaque

  -- Reducibility of zeroᵘ.

  ⊩zeroᵘ :
    ⊢ Γ →
    Γ ⊩⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  ⊩zeroᵘ = ⊩zeroᵘ∷Level⇔ .proj₂

opaque

  -- Validity of zeroᵘ.

  zeroᵘᵛ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ 0ᵘ ⟩ zeroᵘ ∷ Level
  zeroᵘᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( Levelᵛ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                 →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                              ⇔˘⟨ ⊩zeroᵘ≡zeroᵘ∷Level⇔ ⟩→
          Δ ⊩⟨ 0ᵘ ⟩ zeroᵘ ≡ zeroᵘ ∷ Level  □
      )

opaque

  -- Reducibility of sucᵘ.

  ⊩sucᵘ :
    Γ ⊩⟨ l ⟩ t ∷ Level →
    Γ ⊩⟨ l ⟩ sucᵘ t ∷ Level
  ⊩sucᵘ = ⊩sucᵘ∷Level⇔ .proj₂

opaque

  -- Reducibility of equality between applications of sucᵘ.

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
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Levelᵛ (wf-⊩ᵛ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁)
      , ⊩sucᵘ≡sucᵘ ∘→ R.⊩≡∷→ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u
      )

opaque

  -- Validity of sucᵘ.

  sucᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ sucᵘ t ∷ Level
  sucᵘᵛ ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    sucᵘ-congᵛ (refl-⊩ᵛ≡∷ ⊩t)

opaque

  maxᵘ-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t₁ maxᵘ u₁ ≡ t₂ maxᵘ u₂ ∷ Level
  maxᵘ-congᵛ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ σ₁≡σ₂ → ⊩maxᵘ≡maxᵘ∷Level
          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
          (level-⊩≡∷ (⊩Level⇔ .proj₂ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁))
            (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂))
      )

opaque

  maxᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t maxᵘ u ∷ Level
  maxᵘᵛ ⊩t ⊩u = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (maxᵘ-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩t) (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩u))

opaque

  maxᵘ-zeroˡᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ zeroᵘ maxᵘ t ≡ t ∷ Level
  maxᵘ-zeroˡᵛ ⊩t =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ → {!    !}
      )

opaque

  maxᵘ-zeroʳᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l ⟩ t maxᵘ zeroᵘ ≡ t ∷ Level
  maxᵘ-zeroʳᵛ ⊩t = {!   !}

opaque

  maxᵘ-sucᵘᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ {!   !} ⟩ sucᵘ t maxᵘ sucᵘ u ≡ sucᵘ (t maxᵘ u) ∷ Level
  maxᵘ-sucᵘᵛ ⊩t ⊩u = {!   !}

opaque
  unfolding ↑ᵘ′_

  ↑ᵘ′-<-sucᵘ
    : ∀ {t u v} ([t] : Γ ⊩Level t ≡ u ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ≡ v ∷Level)
    → ↑ᵘ′ [t] <′ ↑ᵘ′ [t+1]
  ↑ᵘ′-<-sucᵘ [t] (Levelₜ₌ _ _ t+1⇒ _ prop′) with whnfRed*Term t+1⇒ sucᵘₙ
  ↑ᵘ′-<-sucᵘ [t] (Levelₜ₌ _ _ t+1⇒ _ (ne (neLvlₜ₌ (ne ()) _ _))) | PE.refl
  ↑ᵘ′-<-sucᵘ [t] [t+1]@(Levelₜ₌ _ _ t+1⇒ _ (sucᵘᵣ [t]′)) | PE.refl
    = PE.subst (↑ᵘ′ [t] <′_) (PE.cong 1+ (↑ᵘ′-irrelevance [t] [t]′)) ≤′-refl

  ↑ᵘ-<-sucᵘ
    : ∀ {t u v} ([t] : Γ ⊩Level t ≡ u ∷Level) ([t+1] : Γ ⊩Level sucᵘ t ≡ v ∷Level)
    → ↑ᵘ [t] <ᵘ ↑ᵘ [t+1]
  ↑ᵘ-<-sucᵘ [t] [t+1] = <ᵘ-nat (↑ᵘ′-<-sucᵘ [t] [t+1])
