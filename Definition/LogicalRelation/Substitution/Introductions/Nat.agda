------------------------------------------------------------------------
-- Validity for natural numbers
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Var R
open import Definition.LogicalRelation.Substitution.Introductions.Level R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                               : Con Term _
  A A₁ A₂ B l l′ l″ t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                             : Subst _ _
  ℓ                                 : Universe-level
  p q r                             : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ℕ⇔ : Γ ⊩⟨ l ⟩ ℕ ⇔ Γ ⊩Level l ∷Level
  ⊩ℕ⇔ =
      wfᵘ-⊩
    , λ ⊩l → ⊩l , ℕᵣ (id (ℕⱼ (wfTerm (escapeLevel ⊩l))))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩ℕ∷U⇔ : Γ ⊩⟨ ↓ᵘ 1 ⟩ ℕ ∷ U zeroᵘ ⇔ ⊢ Γ
  ⊩ℕ∷U⇔ =
      (λ ⊩ℕ →
         case ⊩∷U⇔ .proj₁ ⊩ℕ of λ
           (_ , _ , _ , ℕ⇒* , _ , _) →
         wfEqTerm (subset*Term ℕ⇒*))
    , (λ ⊢Γ →
         ⊩∷U⇔ .proj₂
           ( <-sucᵘ (⊩Levelzeroᵘ∷Level ⊢Γ) , ⊩ℕ⇔ .proj₂ (⊩Levelzeroᵘ∷Level ⊢Γ)
           , (_ , id (ℕⱼ ⊢Γ) , ℕₙ , ≅ₜ-ℕrefl ⊢Γ)
           ))

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷ℕ⇔ : Γ ⊩⟨ l ⟩ t ∷ ℕ ⇔ (Γ ⊩Level l ∷Level × Γ ⊩ℕ t ∷ℕ)
  ⊩∷ℕ⇔ =
      (λ ((⊩l , ⊩ℕ) , ⊩t) →
        case ℕ-elim ⊩ℕ of λ {
          (ℕᵣ _) →
        ⊩l , ⊩t })
    , (λ (⊩l , ⊩t) →
        (⊩l , ℕᵣ (id (ℕⱼ (wfEqTerm (subset*Term (_⊩ℕ_∷ℕ.d ⊩t)))))) , ⊩t)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩zero∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ∷ ℕ ⇔ Γ ⊩Level l ∷Level
  ⊩zero∷ℕ⇔ =
      wfᵘ-⊩∷
    , (λ ⊩l →
         let ⊢Γ = wfTerm (escapeLevel ⊩l) in
         ⊩∷ℕ⇔ .proj₂ $
         ⊩l , ℕₜ _ (id (zeroⱼ ⊢Γ)) (≅ₜ-zerorefl ⊢Γ) zeroᵣ)

opaque

  -- A characterisation lemma for _⊩ℕ_∷ℕ.

  ⊩ℕsuc∷ℕ⇔ :
    Γ ⊩ℕ suc t ∷ℕ ⇔
    Γ ⊩ℕ t ∷ℕ
  ⊩ℕsuc∷ℕ⇔ {Γ} {t} =
    (λ { (ℕₜ _ suc-t⇒*u _ u-ok) →
          case whnfRed*Term suc-t⇒*u sucₙ of λ {
            PE.refl →
          lemma u-ok }})
    , (λ ⊩t@(ℕₜ _ t⇒*u u≅u u-ok) →
        let ⊢Γ  = wfEqTerm (subset*Term t⇒*u)
            t↘u = t⇒*u , naturalWhnf (natural u-ok)
        in
        ℕₜ _ (id (sucⱼ (redFirst*Term t⇒*u)))
          (≅-suc-cong $ ≅ₜ-red (id (ℕⱼ ⊢Γ) , ℕₙ) t↘u t↘u u≅u)
          (sucᵣ ⊩t))
    where
    lemma : Natural-prop Γ (suc t) → Γ ⊩ℕ t ∷ℕ
    lemma (sucᵣ ⊩t)         = ⊩t
    lemma (ne (neNfₜ () _))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩suc∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ ⇔
    Γ ⊩⟨ l ⟩ t ∷ ℕ
  ⊩suc∷ℕ⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ                  ⇔⟨ ⊩∷ℕ⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩ℕ suc t ∷ℕ   ⇔⟨ id⇔ ×-cong-⇔ ⊩ℕsuc∷ℕ⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩ℕ t ∷ℕ       ⇔˘⟨ ⊩∷ℕ⇔ ⟩
    Γ ⊩⟨ l ⟩ t ∷ ℕ                      □⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ℕ≡⇔ : Γ ⊩⟨ l ⟩ ℕ ≡ A ⇔ (Γ ⊩Level l ∷Level × Γ ⊩ℕ ℕ ≡ A)
  ⊩ℕ≡⇔ =
      (λ ((⊩l , ⊩ℕ) , _ , ℕ≡A) →
        case ℕ-elim ⊩ℕ of λ {
          (ℕᵣ _) →
        ⊩l , ℕ≡A })
    , (λ (⊩l , ℕ≡A) →
         case id (ℕⱼ (wfEq (subset* ℕ≡A))) of λ
           ℕ⇒*ℕ →
         let ⊩ℕ = ℕᵣ ℕ⇒*ℕ in
           (⊩l , ⊩ℕ)
         , (⊩l , (redSubst* ℕ≡A ⊩ℕ) .proj₁)
         , ℕ≡A)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩ℕ≡ℕ∷U⇔ : Γ ⊩⟨ ↓ᵘ 1 ⟩ ℕ ≡ ℕ ∷ U zeroᵘ ⇔ ⊢ Γ
  ⊩ℕ≡ℕ∷U⇔ =
      (λ ℕ≡ℕ →
         case ⊩≡∷U⇔ .proj₁ ℕ≡ℕ of λ
           (_ , _ , _ , _ , _ , ℕ⇒* , _) →
         wfEqTerm (subset*Term ℕ⇒*))
    , (λ ⊢Γ →
         case id (ℕⱼ ⊢Γ) of λ
           ℕ⇒*ℕ →
         ⊩≡∷U⇔ .proj₂
           ( zeroᵘ<oneᵘ ⊢Γ , ⊩ℕ≡⇔ .proj₂ (⊩Levelzeroᵘ∷Level ⊢Γ , id (ℕⱼ ⊢Γ))
           , (_ , _ , ℕ⇒*ℕ , ℕ⇒*ℕ , ℕₙ , ℕₙ , ≅ₜ-ℕrefl ⊢Γ)
           ))

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ ⇔
    (Γ ⊩Level l ∷Level × Γ ⊩ℕ t ∷ℕ × Γ ⊩ℕ u ∷ℕ × Γ ⊩ℕ t ≡ u ∷ℕ)
  ⊩≡∷ℕ⇔ =
      (λ ((⊩l , ⊩ℕ) , ⊩t , ⊩u , t≡u) →
        case ℕ-elim ⊩ℕ of λ {
          (ℕᵣ _) →
        ⊩l , ⊩t , ⊩u , t≡u })
    , (λ (⊩l , ⊩t , ⊩u , t≡u) →
         (⊩l , ℕᵣ (id (ℕⱼ (wfEqTerm (subset*Term (_⊩ℕ_≡_∷ℕ.d t≡u))))))
       , ⊩t , ⊩u , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zero≡zero∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ ⇔ Γ ⊩Level l ∷Level
  ⊩zero≡zero∷ℕ⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ  ⇔⟨ proj₁ ∘→ wf-⊩≡∷ , refl-⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zero ∷ ℕ         ⇔⟨ ⊩zero∷ℕ⇔ ⟩
    Γ ⊩Level l ∷Level         □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩suc≡suc∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ
  ⊩suc≡suc∷ℕ⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ
      ⇔⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩Level l ∷Level × Γ ⊩ℕ suc t ∷ℕ × Γ ⊩ℕ suc u ∷ℕ × Γ ⊩ℕ suc t ≡ suc u ∷ℕ
      ⇔⟨ id⇔ ×-cong-⇔ ⊩ℕsuc∷ℕ⇔ ×-cong-⇔ ⊩ℕsuc∷ℕ⇔ ×-cong-⇔ (lemma₁ , lemma₂) ⟩
    Γ ⊩Level l ∷Level × Γ ⊩ℕ t ∷ℕ × Γ ⊩ℕ u ∷ℕ × Γ ⊩ℕ t ≡ u ∷ℕ
      ⇔˘⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ  □⇔
    where
    lemma₀ : [Natural]-prop Γ (suc t) (suc u) → Γ ⊩ℕ t ≡ u ∷ℕ
    lemma₀ (sucᵣ t≡u)           = t≡u
    lemma₀ (ne (neNfₜ₌ () _ _))

    lemma₁ : Γ ⊩ℕ suc t ≡ suc u ∷ℕ → Γ ⊩ℕ t ≡ u ∷ℕ
    lemma₁ (ℕₜ₌ _ _ suc-t⇒*t′ suc-u⇒*u′ _ t′≡u′) =
      case whnfRed*Term suc-t⇒*t′ sucₙ of λ {
        PE.refl →
      case whnfRed*Term suc-u⇒*u′ sucₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

    lemma₂ : Γ ⊩ℕ t ≡ u ∷ℕ → Γ ⊩ℕ suc t ≡ suc u ∷ℕ
    lemma₂
      t≡u@(ℕₜ₌ _ _ t⇒*t′ u⇒*u′ t′≅u′ t′≡u′) =
      let t′-ok , u′-ok = split t′≡u′ in
      ℕₜ₌ _ _ (id (sucⱼ (redFirst*Term t⇒*t′)))
        (id (sucⱼ (redFirst*Term u⇒*u′)))
        (≅-suc-cong $
         ≅ₜ-red (id (ℕⱼ (wfEqTerm (≅ₜ-eq t′≅u′))) , ℕₙ)
           (t⇒*t′ , naturalWhnf t′-ok) (u⇒*u′ , naturalWhnf u′-ok)
           t′≅u′)
        (sucᵣ t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zero≡suc∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ ⇔ ⊥
  ⊩zero≡suc∷ℕ⇔ =
      (λ zero≡suc →
         case ⊩≡∷ℕ⇔ .proj₁ zero≡suc of λ {
           (_ , _ , _ , ℕₜ₌ _ _ zero⇒* suc⇒* _ rest) →
         case whnfRed*Term zero⇒* zeroₙ of λ {
           PE.refl →
         case whnfRed*Term suc⇒* sucₙ of λ {
           PE.refl →
         case rest of λ where
           (ne (neNfₜ₌ () _ _)) }}})
    , ⊥-elim

------------------------------------------------------------------------
-- ℕ

opaque

  -- Validity of ℕ, seen as a type former.

  ℕᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ zeroᵘ ⟩ ℕ
  ℕᵛ {Γ} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( zeroᵘᵛᵘ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ    →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                 →⟨ (λ ⊢Δ → ⊩ℕ≡⇔ .proj₂ (⊩Levelzeroᵘ∷Level ⊢Δ , id (ℕⱼ ⊢Δ))) ⟩
          Δ ⊩⟨ zeroᵘ ⟩ ℕ ≡ ℕ  □
      )

opaque

  -- Validity of ℕ, seen as a term former.

  ℕᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ↓ᵘ 1 ⟩ ℕ ∷ U zeroᵘ
  ℕᵗᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ ⊩Γ)
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                             ⇔˘⟨ ⊩ℕ≡ℕ∷U⇔ ⟩→
          Δ ⊩⟨ ↓ᵘ 1 ⟩ ℕ ≡ ℕ ∷ U zeroᵘ  □
      )

------------------------------------------------------------------------
-- The constructors zero and suc

opaque

  -- Reducibility of zero.

  ⊩zero :
    Γ ⊩Level l ∷Level →
    Γ ⊩⟨ l ⟩ zero ∷ ℕ
  ⊩zero = ⊩zero∷ℕ⇔ .proj₂

opaque

  -- Validity of zero.

  zeroᵛ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ zeroᵘ ⟩ zero ∷ ℕ
  zeroᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ℕᵛ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ              →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                           →⟨ (λ ⊢Δ → ⊩zero≡zero∷ℕ⇔ .proj₂ (⊩Levelzeroᵘ∷Level ⊢Δ)) ⟩
          Δ ⊩⟨ zeroᵘ ⟩ zero ≡ zero ∷ ℕ  □
      )

opaque

  -- Reducibility of suc.

  ⊩suc :
    Γ ⊩⟨ l ⟩ t ∷ ℕ →
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ
  ⊩suc = ⊩suc∷ℕ⇔ .proj₂

opaque

  -- Reducibility of equality between applications of suc.

  ⊩suc≡suc :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ →
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ
  ⊩suc≡suc = ⊩suc≡suc∷ℕ⇔ .proj₂

opaque

  -- Validity of equality preservation for suc.

  suc-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ suc t ≡ suc u ∷ ℕ
  suc-congᵛ t≡u =
    ⊩ᵛ≡∷⇔ .proj₂
      ( wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁)
      , ⊩suc≡suc ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u
      )

opaque

  -- Validity of suc.

  sucᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ suc t ∷ ℕ
  sucᵛ ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    suc-congᵛ (refl-⊩ᵛ≡∷ ⊩t)

{-
------------------------------------------------------------------------
-- The eliminator natrec

private opaque

  -- A lemma used to prove ⊩natrec≡natrec.

  ⊩natrec≡natrec′ :
    Γ ∙ ℕ ⊢ A₁ ≅ A₂ →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₁ [ v₁ ]₀ ≡ A₁ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₂ [ v₁ ]₀ ≡ A₂ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₁ [ v₁ ]₀ ≡ A₂ [ v₂ ]₀) →
    Γ ⊢ t₁ ∷ A₁ [ zero ]₀ →
    Γ ⊢ t₂ ∷ A₂ [ zero ]₀ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ∙ A₁ ⊢ u₁ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ∙ ℕ ∙ A₂ ⊢ u₂ ∷ A₂ [ suc (var x1) ]↑² →
    Γ ∙ ℕ ∙ A₁ ⊢ u₁ ≅ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    (∀ {v₁ v₂ w₁ w₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ w₁ ≡ w₂ ∷ A₁ [ v₁ ]₀ →
     Γ ⊩⟨ l ⟩ u₁ [ v₁ , w₁ ]₁₀ ≡ u₂ [ v₂ , w₂ ]₁₀ ∷ A₁ [ suc v₁ ]₀) →
    Γ ⊩ℕ v₁ ∷ℕ →
    Γ ⊩ℕ v₂ ∷ℕ →
    Γ ⊩ℕ v₁ ≡ v₂ ∷ℕ →
    Γ ⊩⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ ≡
      natrec p q r A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  ⊩natrec≡natrec′
    {A₁} {A₂} {l} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂} {p} {q} {r}
    A₁≅A₂ A₁≡A₁ A₂≡A₂ A₁≡A₂ ⊢t₁ ⊢t₂ t₁≡t₂ ⊢u₁ ⊢u₂ u₁≅u₂ u₁≡u₂
    ⊩ℕ-v₁@(ℕₜ v₁′′ v₁⇒*v₁′′ _ v₁′′-prop)
    ⊩ℕ-v₂@(ℕₜ v₂′′ v₂⇒*v₂′′ _ v₂′′-prop)
    ⊩ℕ-v₁≡v₂@(ℕₜ₌ v₁′ v₂′ v₁⇒*v₁′ v₂⇒*v₂′ v₁′≅v₂′ v₁′∼v₂′) =
    -- The terms v₁′ and v₁′′ are equal, as are the terms v₂′
    -- and v₂′′.
    case Σ.map naturalWhnf naturalWhnf $ split v₁′∼v₂′ of λ
      (v₁′-whnf , v₂′-whnf) →
    case whrDet*Term (v₁⇒*v₁′ , v₁′-whnf)
           (v₁⇒*v₁′′ , naturalWhnf (natural v₁′′-prop)) of λ {
      PE.refl →
    case whrDet*Term (v₂⇒*v₂′ , v₂′-whnf)
           (v₂⇒*v₂′′ , naturalWhnf (natural v₂′′-prop)) of λ {
      PE.refl →

    -- Some definitions related to v₁ and v₂.
    case ⊩≡∷ℕ⇔ {l = l} .proj₂ (⊩ℕ-v₁ , ⊩ℕ-v₂ , ⊩ℕ-v₁≡v₂) of λ
      v₁≡v₂ →
    case wf-⊩≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →

    -- Some definitions related to v₁′ and v₂′.
    case ⊩∷-⇒* v₁⇒*v₁′ ⊩v₁ of λ
      v₁≡v₁′ →
    case ⊩∷-⇒* v₂⇒*v₂′ ⊩v₂ of λ
      v₂≡v₂′ →
    case
      v₁′  ≡˘⟨ v₁≡v₁′ ⟩⊩∷
      v₁   ≡⟨ v₁≡v₂ ⟩⊩∷
      v₂   ≡⟨ v₂≡v₂′ ⟩⊩∷∎
      v₂′  ∎
    of λ
      v₁′≡v₂′ →
    case A₁≡A₂ v₁′≡v₂′ of λ
      A₁[v₁′]≡A₂[v₂′] →
    case ≅-eq $ escape-⊩≡ A₁[v₁′]≡A₂[v₂′] of λ
      ⊢A₁[v₁′]≡A₂[v₂′] →

    -- The two applications of natrec are equal if applications of
    -- natrec to v₁′ and v₂′ are equal.
    case
      (λ (hyp : _ ⊩⟨ l ⟩ _ ≡ _ ∷ _) →
         natrec p q r A₁ t₁ u₁ v₁ ∷ A₁ [ v₁ ]₀    ⇒*⟨ natrec-subst* ⊢t₁ ⊢u₁ v₁⇒*v₁′ ⟩⊩∷∷
                                                    ⟨ A₁≡A₁ v₁≡v₁′ ⟩⊩∷
         natrec p q r A₁ t₁ u₁ v₁′ ∷ A₁ [ v₁′ ]₀  ≡⟨ hyp ⟩⊩∷∷⇐*
                                                   ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
                                   ∷ A₂ [ v₂′ ]₀  ˘⟨ ≅-eq $ escape-⊩≡ $ A₂≡A₂ v₂≡v₂′ ⟩⇐
         natrec p q r A₂ t₂ u₂ v₂′ ∷ A₂ [ v₂ ]₀   ⇐*⟨ natrec-subst* ⊢t₂ ⊢u₂ v₂⇒*v₂′ ⟩∎∷
         natrec p q r A₂ t₂ u₂ v₂                 ∎)
    of λ
      lemma →

    lemma
      (case v₁′∼v₂′ of λ where
         -- If v₁′ and v₂′ are equal neutral terms, then one can
         -- conclude by using the fact that the applications of natrec
         -- to v₁′ and v₂′ are equal neutral terms.
         (ne (neNfₜ₌ v₁′-ne v₂′-ne v₁′~v₂′)) →
           neutral-⊩≡∷ (wf-⊩≡ A₁[v₁′]≡A₂[v₂′] .proj₁)
             (natrecₙ v₁′-ne) (natrecₙ v₂′-ne) $
           ~-natrec A₁≅A₂ (escape-⊩≡∷ t₁≡t₂) u₁≅u₂ v₁′~v₂′

         -- If v₁′ and v₂′ are both zero, then one can conclude by
         -- using the rule natrec-zero and the fact that t₁ is equal
         -- to t₂.
         zeroᵣ →
           natrec p q r A₁ t₁ u₁ zero  ⇒⟨ natrec-zero ⊢t₁ ⊢u₁ ⟩⊩∷
           t₁ ∷ A₁ [ zero ]₀           ≡⟨ t₁≡t₂ ⟩⊩∷∷⇐*
                                        ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
           t₂ ∷ A₂ [ zero ]₀           ⇐⟨ natrec-zero ⊢t₂ ⊢u₂ ⟩∎∷
           natrec p q r A₂ t₂ u₂ zero  ∎

         -- If v₁′ and v₂′ are applications of suc to equal terms,
         -- then one can conclude by using the rule natrec-suc and an
         -- inductive hypothesis.
         (sucᵣ {n = v₁″} {n′ = v₂″} ⊩ℕ-v₁″≡v₂″) →
           case v₁′′-prop of λ {
             (ne suc-ne) → case _⊩neNf_∷_.neK suc-ne of λ ();
             (sucᵣ ⊩ℕ-v₁″) →
           case v₂′′-prop of λ {
             (ne suc-ne) → case _⊩neNf_∷_.neK suc-ne of λ ();
             (sucᵣ ⊩ℕ-v₂″) →
           case ⊩≡∷ℕ⇔ .proj₂ (⊩ℕ-v₁″ , ⊩ℕ-v₂″ , ⊩ℕ-v₁″≡v₂″) of λ
             v₁″≡v₂″ →
           case wf-⊩≡∷ v₁″≡v₂″ of λ
             (⊩v₁″ , ⊩v₂″) →

           natrec p q r A₁ t₁ u₁ (suc v₁″)                             ⇒⟨ natrec-suc ⊢t₁ ⊢u₁ (escape-⊩∷ ⊩v₁″) ⟩⊩∷
           u₁ [ v₁″ , natrec p q r A₁ t₁ u₁ v₁″ ]₁₀ ∷ A₁ [ suc v₁″ ]₀  ≡⟨ u₁≡u₂ v₁″≡v₂″ $
                                                                          ⊩natrec≡natrec′ A₁≅A₂ A₁≡A₁ A₂≡A₂ A₁≡A₂ ⊢t₁ ⊢t₂ t₁≡t₂
                                                                            ⊢u₁ ⊢u₂ u₁≅u₂ u₁≡u₂ ⊩ℕ-v₁″ ⊩ℕ-v₂″ ⊩ℕ-v₁″≡v₂″ ⟩⊩∷∷⇐*
                                                                        ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
           u₂ [ v₂″ , natrec p q r A₂ t₂ u₂ v₂″ ]₁₀ ∷ A₂ [ suc v₂″ ]₀  ⇐⟨ natrec-suc ⊢t₂ ⊢u₂ (escape-⊩∷ ⊩v₂″)
                                                                        ⟩∎∷
           natrec p q r A₂ t₂ u₂ (suc v₂″)                             ∎ }}) }}

opaque

  -- Reducibility of equality between applications of natrec.

  ⊩natrec≡natrec :
    Γ ∙ ℕ ⊩ᵛ A₁ ≡ A₂ →
    Γ ⊩ᵛ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ∙ A₁ ⊩ᵛ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ⊩ᵛ v₁ ≡ v₂ ∷ ℕ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ [ σ₁ ] ≡
      natrec p q r A₂ t₂ u₂ v₂ [ σ₂ ] ∷ A₁ [ v₁ ]₀ [ σ₁ ]
  ⊩natrec≡natrec {A₁} {A₂} {σ₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (_ , ⊩t₂) →
    case conv-⊩ᵛ∷
           (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂ $
            refl-⊩ᵛ≡∷ $ zeroᵛ $ wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t₂))
           ⊩t₂ of λ
      ⊩t₂ →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case conv-∙-⊩ᵛ∷ A₁≡A₂ $
         conv-⊩ᵛ∷
           (⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² A₁≡A₂ $
            sucᵛ (varᵛ (there here) (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩u₁))))
         ⊩u₂ of λ
      ⊩u₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →

    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂ .proj₂ of λ
      A₁[σ₁⇑]≡A₂[σ₂⇑] →
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift A₁ _) $
         ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ σ₁≡σ₂ .proj₂ of λ
      t₁[σ₁]≡t₂[σ₂] →
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (natrecSucCase _ A₁) $
         ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ u₁≡u₂ σ₁≡σ₂ .proj₂ of λ
      u₁[σ₁⇑⇑]≡u₂[σ₂⇑⇑] →

    case ⊩≡∷ℕ⇔ .proj₁ $
         ⊩ᵛ≡∷⇔ .proj₁ v₁≡v₂ .proj₂ σ₁≡σ₂ .proj₂ of λ
      (⊩ℕ-v₁ , ⊩ℕ-v₂ , ⊩ℕ-v₁≡v₂) →

    ω+0 , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ singleSubstLift A₁ _) (⊩natrec≡natrec′
      (escape-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑])
      (λ x → emb-⊩≡ ≤ᵘ-ω (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁) x .proj₂))
      (λ x → emb-⊩≡ ≤ᵘ-ω (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂) x .proj₂))
      (λ x → emb-⊩≡ ≤ᵘ-ω (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ x .proj₂))
      (escape-⊩∷ $ wf-⊩≡∷ t₁[σ₁]≡t₂[σ₂] .proj₁)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A₂ _) $
       escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂ .proj₂)
      {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !})
    -- PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
    -- ⊩natrec≡natrec′
    --   (escape-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑])
    --   (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁))
    --   (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂))
    --   (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂)
    --   (escape-⊩∷ $ wf-⊩≡∷ t₁[σ₁]≡t₂[σ₂] .proj₁)
    --   (PE.subst (_⊢_∷_ _ _) (singleSubstLift A₂ _) $
    --    escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂)
    --   (level-⊩≡∷
    --      (wf-⊩≡
    --         (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
    --          refl-⊩≡∷ $ ⊩zero {l = l} $ escape-⊩ˢ∷ ⊩σ₁ .proj₁)
    --         .proj₁)
    --      t₁[σ₁]≡t₂[σ₂])
    --   (escape-⊩∷ $ wf-⊩≡∷ u₁[σ₁⇑⇑]≡u₂[σ₂⇑⇑] .proj₁)
    --   (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A₂) $
    --    escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩u₂ ⊩σ₂)
    --   (escape-⊩≡∷ u₁[σ₁⇑⇑]≡u₂[σ₂⇑⇑])
    --   (λ {v₁ = v₁} {v₂ = _} {w₁ = w₁} v₁≡v₂ w₁≡w₂ →
    --      level-⊩≡∷
    --        (wf-⊩≡
    --           (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
    --            ⊩suc≡suc v₁≡v₂)
    --           .proj₁) $
    --      PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
    --        (A₁ [ suc (var x1) ]↑² [ σ₁ ⇑ ⇑ ] [ v₁ , w₁ ]₁₀  ≡⟨ PE.cong _[ _ , _ ]₁₀ $ natrecSucCase _ A₁ ⟩
    --         A₁ [ σ₁ ⇑ ] [ suc (var x1) ]↑² [ v₁ , w₁ ]₁₀    ≡˘⟨ substComp↑² (A₁ [ _ ]) _ ⟩
    --         A₁ [ σ₁ ⇑ ] [ suc v₁ ]₀                         ∎) $
    --      ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ u₁≡u₂ σ₁≡σ₂ v₁≡v₂ w₁≡w₂)
    --   ⊩ℕ-v₁ ⊩ℕ-v₂ ⊩ℕ-v₁≡v₂
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- Validity of equality preservation for natrec.

  natrec-congᵛ :
    Γ ∙ ℕ ⊩ᵛ A₁ ≡ A₂ →
    Γ ⊩ᵛ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ∙ A₁ ⊩ᵛ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ⊩ᵛ v₁ ≡ v₂ ∷ ℕ →
    Γ ⊩ᵛ natrec p q r A₁ t₁ u₁ v₁ ≡ natrec p q r A₂ t₂ u₂ v₂ ∷
      A₁ [ v₁ ]₀
  natrec-congᵛ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ v₁≡v₂ .proj₁)
      , ⊩natrec≡natrec A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂
      )

opaque

  -- Validity of natrec.

  natrecᵛ :
    Γ ∙ ℕ ⊩ᵛ A →
    Γ ⊩ᵛ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊩ᵛ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ v ∷ ℕ →
    Γ ⊩ᵛ natrec p q r A t u v ∷ A [ v ]₀
  natrecᵛ ⊩A ⊩t ⊩u ⊩v =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    natrec-congᵛ (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)
      (refl-⊩ᵛ≡∷ ⊩v)

opaque

  -- Validity of the equality rule called natrec-zero.

  natrec-zeroᵛ :
    Γ ⊩ᵛ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊩ᵛ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ natrec p q r A t u zero ≡ t ∷ A [ zero ]₀
  natrec-zeroᵛ {A} ⊩t ⊩u =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         natrec-zero
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ .proj₂)
           (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩u ⊩σ .proj₂))
      ⊩t

opaque

  -- Validity of the equality rule called natrec-suc.

  natrec-sucᵛ :
    Γ ∙ ℕ ⊩ᵛ A →
    Γ ⊩ᵛ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊩ᵛ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ v ∷ ℕ →
    Γ ⊩ᵛ natrec p q r A t u (suc v) ≡
      u [ v , natrec p q r A t u v ]₁₀ ∷ A [ suc v ]₀
  natrec-sucᵛ {A} {u} ⊩A ⊩t ⊩u ⊩v =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym $ [,]-[]-commute u)
           (PE.sym $ singleSubstLift A _) $
         natrec-suc
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ .proj₂)
           (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩u ⊩σ .proj₂)
           (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩v ⊩σ .proj₂))
      (PE.subst (_⊩ᵛ_∷_ _ _) (PE.sym $ substComp↑² A _) $
       ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩u ⊩v (natrecᵛ ⊩A ⊩t ⊩u ⊩v))
-}
