------------------------------------------------------------------------
-- Validity for Π- and Σ-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R {{eqrel}}
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Level R {{eqrel}}
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
import Definition.LogicalRelation.Weakening R as W

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as TW using (_∷ʷ_⊇_)
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  n                         : Nat
  Γ Δ                       : Con Term _
  A A₁ A₂ B B₁ B₂ C l l′ l₁ l₂ t t₁ t₂ u : Term _
  σ σ₁ σ₂                   : Subst _ _
  p p₁ p₂ q q₁ q₂           : M
  b b₁ b₂                   : BinderMode
  ℓ                         : Universe-level

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ΠΣ⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q ×
     Γ ⊩Level l ∷Level ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷ Δ ⊇ Γ →
      Δ ⊩⟨ wk ρ l ⟩ wk ρ A ×
      (∀ {t u} →
       Δ ⊩⟨ wk ρ l ⟩ t ≡ u ∷ wk ρ A →
       Δ ⊩⟨ wk ρ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀)))
  ⊩ΠΣ⇔ {n} {Γ} {l} {b} {p} {q} {A} {B} =
      (λ (⊩l , ⊩AB) →
        case B-elim _ ⊩AB of λ {
          (Bᵣ _ (Bᵣ _ _ ⇒*ΠΣ _ ⊩wk-A ⊩wk-B wk-B≡wk-B ok)) →
        case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
          (PE.refl , PE.refl , PE.refl) →
          ok , ⊩l
        , λ ρ⊇ →
          let ⊩wk-ρ-A = ⊩wk-A ρ⊇ in
            ⊩-intro-wk ρ⊇ ⊩wk-ρ-A
          , λ ((⊩l , ⊩wk-ρ-A′) , ⊩t , ⊩u , t≡u) →
              let ⊩t = irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩t
                  ⊩u = irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩u
                  t≡u = irrelevanceEqTerm ⊩wk-ρ-A′ ⊩wk-ρ-A t≡u
              in ⊩≡-intro-wk ρ⊇
                (⊩wk-B ρ⊇ ⊩t) (⊩wk-B ρ⊇ ⊩u) (wk-B≡wk-B ρ⊇ ⊩t ⊩u t≡u) }})
    , (λ (ok , ⊩l , rest) →
         let ⊢Γ = wfTerm (escapeLevel ⊩l) in
         case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) $
              rest (TW.idʷ ⊢Γ) .proj₁ of λ
           ⊩A →
         case escape-⊩ ⊩A of λ
           ⊢A →
         case TW.stepʷ TW.id ⊢A of λ
           step-id →
         case var (∙ ⊢A) here of λ
           ⊢x0 →
         case PE.subst (λ B → _ ⊩⟨ _ ⟩ B ≡ B) (wkSingleSubstId _) $
              rest step-id .proj₂ $
              refl-⊩≡∷ $
              neutral-⊩∷ (PE.subst₂ (_ ⊩⟨_⟩_) (wk1-wk _ _) (wk1-wk _ _) (wk-⊩ step-id (rest (TW.idʷ ⊢Γ) .proj₁))) (var _) (~-var ⊢x0) of λ
           (B≡B : Γ ∙ A ⊩⟨ wk1 l ⟩ B ≡ B) →
         case escape-⊩ (wf-⊩≡ B≡B .proj₁) of λ
           ⊢B →
         let ⊩wk-A = λ {m} {ρ} {Δ} ρ⊇ →
               PE.subst (_ ⊩′⟨_⟩ _) (W.wk-↑ᵘ ρ⊇ ⊩l _) (rest ρ⊇ .proj₁ .proj₂)
             ⊩wk-B = λ {m} {ρ} {Δ} {t} ρ⊇ ⊩t →
               PE.subst (_ ⊩′⟨_⟩ _) (W.wk-↑ᵘ ρ⊇ ⊩l _)
                 (wf-⊩≡ (rest ρ⊇ .proj₂ (refl-⊩≡∷ (⊩∷-intro-wk ρ⊇ (⊩wk-A ρ⊇) ⊩t))) .proj₁ .proj₂)
         in
         ⊩l ,
         Bᵣ (BM b p q)
           (Bᵣ _ _ (id (ΠΣⱼ ⊢B ok))
              (≅-ΠΣ-cong (escape-⊩≡ $ refl-⊩≡ ⊩A) (escape-⊩≡ B≡B) ok)
              (λ {m} {ρ} {Δ} → ⊩wk-A {m} {ρ} {Δ})
              (λ {m} {ρ} {Δ} {t} ρ⊇ ⊩t → ⊩wk-B {m} {ρ} {Δ} {t} ρ⊇ ⊩t)
              (λ ρ⊇ ⊩t ⊩u t≡u → ⊩≡→⊩≡/ (⊩wk-B ρ⊇ ⊩t)
                (rest ρ⊇ .proj₂
                  ( rest ρ⊇ .proj₁
                  , irrelevanceTerm (⊩wk-A ρ⊇) (rest ρ⊇ .proj₁ .proj₂) ⊩t
                  , irrelevanceTerm (⊩wk-A ρ⊇) (rest ρ⊇ .proj₁ .proj₂) ⊩u
                  , irrelevanceEqTerm (⊩wk-A ρ⊇) (rest ρ⊇ .proj₁ .proj₂) t≡u
                  )))
              ok))

opaque

  -- A variant of ⊩ΠΣ⇔.

  ⊩ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q × Γ ⊩⟨ l ⟩ A × Γ ∙ A ⊩⟨ wk1 l ⟩ B
  ⊩ΠΣ→ ⊩ΠΣ =
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ of λ
      (ok , ⊩l , rest) →
    case wfTerm (escapeLevel ⊩l) of λ
      ⊢Γ →
    case rest (TW.idʷ ⊢Γ) of λ
      (⊩wk-id-A , _) →
    case PE.subst₂ (_ ⊩⟨_⟩_) (wk-id _) (wk-id _) ⊩wk-id-A of λ
      ⊩A →
    case rest (TW.stepʷ TW.id (escape-⊩ ⊩A)) of λ
      (⊩wk₁-A , wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀) →
      ok , ⊩A
    , PE.subst (_⊩⟨_⟩_ _ _) (wkSingleSubstId _)
        (proj₁ $ wf-⊩≡ $
         wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀ $
         refl-⊩≡∷ (⊩var here ⊩wk₁-A))

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡⇔ :
    {C : Term n} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ C ×
     ∃₂ λ A′ B′ → Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷ Δ ⊇ Γ →
      Δ ⊩⟨ wk ρ l ⟩ wk ρ A ≡ wk ρ A′ ×
      (∀ {t} →
       Δ ⊩⟨ wk ρ l ⟩ t ∷ wk ρ A →
       Δ ⊩⟨ wk ρ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀)))
  ⊩ΠΣ≡⇔ =
      (λ ((⊩l , ⊩ΠΣ) , ⊩C , ΠΣ≡C) →
         case B-elim _ ⊩ΠΣ of λ
           ⊩ΠΣ′ →
          --  ⊩ΠΣ , ⊩C
        --  , lemma₁ ≤ᵘ-refl ⊩ΠΣ′ ⊩C
        --      (irrelevanceEq ⊩ΠΣ (B-intr _ ⊩ΠΣ′) ΠΣ≡C))
        {!   !})
    , (λ ((⊩l , ⊩ΠΣ) , ⊩C , _ , _ , C⇒* , rest) →
         case B-elim _ ⊩ΠΣ of λ
           ⊩ΠΣ′ →
        --  B-intr _ ⊩ΠΣ′ , ⊩C , lemma₂ ⊩ΠΣ′ C⇒* rest)
        {!   !})
    -- where
    -- lemma₁ :
    --   l′ ≤ᵘ l →
    --   (⊩ΠΣ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) →
    --   Γ ⊩⟨ l ⟩ C →
    --   Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C / B-intr _ ⊩ΠΣ →
    --   ∃₂ λ A′ B′ → Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
    --   (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
    --    ρ ∷ʷ Δ ⊇ Γ →
    --    Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
    --    (∀ {t} →
    --     Δ ⊩⟨ l ⟩ t ∷ wk ρ A →
    --     Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀))
    -- lemma₁ l′≤l (emb l″<l′ ⊩ΠΣ₁) ⊩ΠΣ₂ ΠΣ≡ΠΣ =
    --   lemma₁ (≤ᵘ-trans (<ᵘ→≤ᵘ l″<l′) l′≤l) ⊩ΠΣ₁ ⊩ΠΣ₂
    --     (irrelevanceEq (B-intr _ (emb l″<l′ ⊩ΠΣ₁)) (B-intr _ ⊩ΠΣ₁)
    --        ΠΣ≡ΠΣ)
    -- lemma₁
    --   l′≤l (noemb (Bᵣ _ _ ⇒*ΠΣ _ ⊩wk-A ⊩wk-B _ ok)) ⊩C
    --   (B₌ _ _ ⇒*ΠΣ′ _ wk-A≡wk-A′ wk-B≡wk-B′) =
    --   case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
    --     (PE.refl , PE.refl , _) →
    --     _ , _ , ⇒*ΠΣ′
    --   , λ ρ⊇ →
    --       case ⊩ΠΣ⇔ .proj₁ (wf-⊩≡ (⊩-⇒* ⇒*ΠΣ′ ⊩C) .proj₂)
    --              .proj₂ .proj₂ ρ⊇ of λ
    --         (⊩wk-ρ-A′ , wk-ρ⇑-B′≡wk-ρ⇑-B′) →
    --       case   emb-≤-⊩ l′≤l (⊩wk-A ρ⊇)
    --            , ⊩wk-ρ-A′
    --            , emb-≤-⊩≡ (wk-A≡wk-A′ ρ⊇) of λ
    --         wk-ρ-A≡wk-ρ-A′ →
    --         wk-ρ-A≡wk-ρ-A′
    --       , λ ⊩t@(⊩wk-ρ-A , ⊩t′) →
    --           let ⊩wk-ρ⇑-B[t] =
    --                 ⊩wk-B ρ⊇ (irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩t′)
    --               ⊩wk-ρ⇑-B[t]′ = emb-≤-⊩ l′≤l ⊩wk-ρ⇑-B[t]
    --           in
    --             ⊩wk-ρ⇑-B[t]′
    --           , wf-⊩≡
    --               (wk-ρ⇑-B′≡wk-ρ⇑-B′ $
    --                refl-⊩≡∷ (conv-⊩∷ wk-ρ-A≡wk-ρ-A′ ⊩t))
    --               .proj₁
    --           , irrelevanceEq ⊩wk-ρ⇑-B[t] ⊩wk-ρ⇑-B[t]′
    --               (wk-B≡wk-B′ ρ⊇ $
    --                irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩t′) }

    -- lemma₂ :
    --   (⊩ΠΣ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) →
    --   Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    --   (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
    --    ρ ∷ʷ Δ ⊇ Γ →
    --    Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
    --    (∀ {t} →
    --     Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
    --     Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)) →
    --   Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ C / B-intr _ ⊩ΠΣ
    -- lemma₂ (emb ≤ᵘ-refl     ⊩ΠΣ₁) = lemma₂ ⊩ΠΣ₁
    -- lemma₂ (emb (≤ᵘ-step p) ⊩ΠΣ₁) = lemma₂ (emb p ⊩ΠΣ₁)
    -- lemma₂
    --   {B₁} {B₂} (noemb ⊩ΠΣ₁@(Bᵣ _ _ ⇒*ΠΣ₁ _ ⊩wk-A₁ ⊩wk-B₁ _ ok))
    --   C⇒* rest =
    --   case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ₁ ΠΣₙ of λ {
    --     (PE.refl , PE.refl , _) →
    --   let ⊢A₁ , _ = inversion-ΠΣ (wf-⊢≡ (subset* ⇒*ΠΣ₁) .proj₁) in
    --   case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _) $
    --        rest (TW.idʷ (wf ⊢A₁)) .proj₁ of λ
    --     A₁≡A₂ →
    --   case TW.stepʷ TW.id ⊢A₁ of λ
    --     step-id →
    --   case var (∙ ⊢A₁) here of λ
    --     ⊢x0 →
    --   case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) {y = B₁} {v = B₂}
    --          (wkSingleSubstId _) (wkSingleSubstId _) $
    --        rest step-id .proj₂ $
    --        neutral-⊩∷ (W.wk step-id (wf-⊩≡ A₁≡A₂ .proj₁)) (var _)
    --          (~-var ⊢x0) of λ
    --     B₁≡B₂ →
    --   _ ⊩⟨ _ ⟩ _ ≡ _ / Bᵣ _ ⊩ΠΣ₁ ∋
    --   B₌ _ _ C⇒* (≅-ΠΣ-cong (escape-⊩≡ A₁≡A₂) (escape-⊩≡ B₁≡B₂) ok)
    --     (λ ρ⊇ → ⊩≡→⊩≡/ (⊩wk-A₁ ρ⊇) (rest ρ⊇ .proj₁))
    --     (λ ρ⊇ ⊩t →
    --        case rest ρ⊇ of λ
    --          (wk-ρ-A₁≡wk-ρ-A₂ , wk-ρ⇑-B₁≡wk-ρ⇑-B₂) →
    --        case wf-⊩≡ wk-ρ-A₁≡wk-ρ-A₂ .proj₁ of λ
    --          ⊩wk-ρ-A₁ →
    --        ⊩≡→⊩≡/ (⊩wk-B₁ ρ⊇ ⊩t) $
    --        wk-ρ⇑-B₁≡wk-ρ⇑-B₂
    --          ( ⊩wk-ρ-A₁
    --          , irrelevanceTerm (⊩wk-A₁ ρ⊇) ⊩wk-ρ-A₁ ⊩t
    --          )) }

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ⇔ :
    {A₁ A₂ : Term n} {B₁ B₂ : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷ Δ ⊇ Γ →
      Δ ⊩⟨ wk ρ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t} →
       Δ ⊩⟨ wk ρ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ wk ρ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)))
  ⊩ΠΣ≡ΠΣ⇔
    {n} {Γ} {l} {b₁} {p₁} {q₁} {b₂} {p₂} {q₂} {A₁} {A₂} {B₁} {B₂} =
    {!   !}
    {-

    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂  ⇔⟨ ⊩ΠΣ≡⇔ ⟩

    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     ∃₂ λ A B →
     Γ ⊢ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇒* ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B [ t ]₀)))    ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ ⊩ΠΣ₂ →
                                                                         (λ (_ , _ , ΠΣ⇒*ΠΣ , rest) →
                                                                            case whnfRed* ΠΣ⇒*ΠΣ ΠΣₙ of λ {
                                                                              PE.refl →
                                                                            PE.refl , PE.refl , PE.refl , rest })
                                                                       , λ { (PE.refl , PE.refl , PE.refl , rest) →
                                                                             _ , _ , id (escape-⊩ ⊩ΠΣ₂) , rest }) ⟩
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
     ρ ∷ʷ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
     (∀ {t} →
      Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
      Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀))     □⇔
    -}

opaque

  -- A variant of ⊩ΠΣ≡ΠΣ⇔.

  ⊩ΠΣ≡ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    ΠΣ-allowed b₁ p₁ q₁ × b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ × Γ ∙ A₁ ⊩⟨ wk1 l ⟩ B₁ ≡ B₂
  ⊩ΠΣ≡ΠΣ→ ΠΣ≡ΠΣ =
    {!   !}
    {-
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , rest) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (ok , ⊢Γ , _) →
    case rest (TW.idʷ ⊢Γ) of λ
      (wk-id-A₁≡wk-id-A₂ , _) →
    case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
           wk-id-A₁≡wk-id-A₂ of λ
      A₁≡A₂ →
    case rest (TW.stepʷ TW.id (escape-⊩ (wf-⊩≡ A₁≡A₂ .proj₁))) of λ
      (wk₁-A₁≡wk₁-A₂ , wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀) →
      ok , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , A₁≡A₂
    , PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _) (wkSingleSubstId _)
        (wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ $
         ⊩var here (wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁))
    -}

-- See also ⊩ᵛΠΣ⇔ below.

------------------------------------------------------------------------
-- Some substitution lemmas

opaque

  -- A substitution lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ ≡ B₂ [ t₂ ]₀
  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ {l} {B₁} {B₂} {t₁} {t₂} ΠΣ≡ΠΣ t₁≡t₂ =
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , _ , _ , _ , rest) →
    case ⊩ΠΣ→ ⊩ΠΣ₁ of λ
      (_ , ⊩A₁ , _) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (_ , ⊩l , rest₁) →
    case wfTerm (escapeLevel ⊩l) of λ
      ⊢Γ →
    B₁ [ t₁ ]₀  ≡⟨ PE.subst₃ (_ ⊩⟨_⟩_≡_)
                     (wk-id _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁) $
                   rest₁ (TW.idʷ ⊢Γ) .proj₂ $
                   PE.subst₂ (_ ⊩⟨_⟩ _ ≡ _ ∷_) (PE.sym $ wk-id _) (PE.sym $ wk-id _) $
                   level-⊩≡∷ ⊩A₁ t₁≡t₂ ⟩⊩
    B₁ [ t₂ ]₀  ≡⟨ PE.subst₃ (_ ⊩⟨_⟩_≡_)
                     (wk-id _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₂) $
                   rest (TW.idʷ ⊢Γ) .proj₂ $
                   PE.subst₂ (_ ⊩⟨_⟩ _ ∷_) (PE.sym $ wk-id _) (PE.sym $ wk-id _) $
                   level-⊩∷ ⊩A₁ $
                   wf-⊩≡∷ t₁≡t₂ .proj₂ ⟩⊩∎
    B₂ [ t₂ ]₀  ∎

opaque

  -- A substitution lemma for _⊩⟨_⟩_.

  ⊩ΠΣ→⊩∷→⊩[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ΠΣ→⊩∷→⊩[]₀ ⊩ΠΣ ⊩t =
    wf-⊩≡ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΠΣ) (refl-⊩≡∷ ⊩t)) .proj₁

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as type formers

opaque

  -- Reducibility for Π and Σ, seen as type formers.

  ⊩ΠΣ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ wk1 l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l [ σ ] ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ]
  ⊩ΠΣ {l} {A} {B} ok ⊩A ⊩B ⊩σ =
    ⊩ΠΣ⇔ .proj₂
      ( ok
      , ⊩ᵛᵘ→⊩ˢ∷→⊩[] (wfᵘ-⊩ᵛ ⊩A) ⊩σ
      , λ ρ⊇ →
            PE.subst₂ (_⊩⟨_⟩_ _) (PE.sym $ wk-subst l) (PE.sym $ wk-subst A)
              (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ ⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
          , λ t≡u →
              PE.subst₃ (_ ⊩⟨_⟩_≡_)
                (PE.sym $ PE.trans (wk-subst l) (PE.sym (wk1-tail l)))
                (PE.sym $ singleSubstWkComp _ _ B)
                (PE.sym $ singleSubstWkComp _ _ B) $
              ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
                , _ , ⊩A
                , PE.subst₂ (_ ⊩⟨_⟩ _ ≡ _ ∷_) (wk-subst l) (wk-subst A) t≡u
                )
      )

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as type
  -- formers.

  ⊩ΠΣ≡ΠΣ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ wk1 l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l [ σ₁ ] ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ]
  ⊩ΠΣ≡ΠΣ {l} {A₁} {A₂} {B₁} {B₂} ok A₁≡A₂ B₁≡B₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wfᵘ-⊩ᵛ≡ A₁≡A₂ of λ
      ⊩l →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩ΠΣ ok ⊩A₁ ⊩B₁ ⊩σ₁
      , level-conv-⊩ (⊩ᵛᵘ→⊩ˢ≡∷→⊩[]≡[] ⊩l (sym-⊩ˢ≡∷ σ₁≡σ₂)) (⊩ΠΣ ok ⊩A₂ ⊩B₂ ⊩σ₂)
      , PE.refl , PE.refl , PE.refl
      , λ ρ⊇ →
            PE.subst₃ (_ ⊩⟨_⟩_≡_) (PE.sym $ wk-subst l)
              (PE.sym $ wk-subst A₁)
              (PE.sym $ wk-subst A₂)
              (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ $
               ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂)
          , λ ⊩t →
              PE.subst₃ (_ ⊩⟨_⟩_≡_)
                (PE.sym $ PE.trans (wk-subst l) (PE.sym (wk1-tail l)))
                (PE.sym $ singleSubstWkComp _ _ B₁)
                (PE.sym $ singleSubstWkComp _ _ B₂) $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
                , _ , ⊩A₁
                , refl-⊩≡∷
                    (PE.subst₂ (_ ⊩⟨_⟩ _ ∷_) (wk-subst l) (wk-subst A₁) ⊩t)
                )
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as type
  -- formers.

  ΠΣ-congᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ wk1 l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-congᵛ ok A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡⇔ .proj₂
      ( wfᵘ-⊩ᵛ≡ A₁≡A₂
      , ⊩ΠΣ≡ΠΣ ok A₁≡A₂ B₁≡B₂
      )

opaque

  -- Validity of Π and Σ, seen as type formers.

  ΠΣᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ wk1 l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣᵛ ok ⊩A ⊩B =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ΠΣ-congᵛ ok (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡ ⊩B)

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛΠΣ⇔ :
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q × Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ wk1 l ⟩ B)
  ⊩ᵛΠΣ⇔ {l} {B} =
      (λ ⊩ΠΣAB →
         case ⊩ᵛ⇔ .proj₁ ⊩ΠΣAB of λ
           (⊩l , ΠΣAB≡ΠΣAB) →
         case wf-⊩ᵛᵘ ⊩l of λ
           ⊩Γ →
         case ⊩ᵛ⇔ .proj₂
                ( ⊩l
                , proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
                  ⊩ΠΣ≡ΠΣ→ ∘→ ΠΣAB≡ΠΣAB
                ) of λ
           ⊩A →
           ⊩ΠΣ⇔ .proj₁
             (wf-⊩≡ (ΠΣAB≡ΠΣAB (refl-⊩ˢ≡∷ $ ⊩ˢ∷-idSubst ⊩Γ)) .proj₁)
             .proj₁
         , ⊩A
         , ⊩ᵛ⇔ .proj₂
             ( wk1-⊩ᵛᵘ ⊩A ⊩l
             , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
                 case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
                   (tail-σ₁≡tail-σ₂ , _ , _ , head-σ₁≡head-σ₂) →
                 PE.subst (_ ⊩⟨_⟩ _ ≡ _) (PE.sym $ wk1-tail l)
                  (B [ σ₁ ]                             ≡˘⟨ substVar-to-subst consSubst-η B ⟩⊩≡
                   B [ consSubst (tail σ₁) (head σ₁) ]  ≡˘⟨ singleSubstComp _ _ B ⟩⊩≡
                   B [ tail σ₁ ⇑ ] [ head σ₁ ]₀         ≡⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (ΠΣAB≡ΠΣAB tail-σ₁≡tail-σ₂) head-σ₁≡head-σ₂ ⟩⊩∎≡
                   B [ tail σ₂ ⇑ ] [ head σ₂ ]₀         ≡⟨ singleSubstComp _ _ B ⟩
                   B [ consSubst (tail σ₂) (head σ₂) ]  ≡⟨ substVar-to-subst consSubst-η B ⟩
                   B [ σ₂ ]                             ∎)
             ))
    , (λ (ok , ⊩A , ⊩B) → ΠΣᵛ ok ⊩A ⊩B)
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as term formers

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as term
  -- formers.

  ⊩ΠΣ≡ΠΣ∷U :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U l₁ →
    Γ ∙ A₁ ⊩ᵛ⟨ l′ ⟩ B₁ ≡ B₂ ∷ U (wk1 l₂) →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ (sucᵘ (l₁ maxᵘ l₂)) [ σ₁ ] ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ] ∷ U (l₁ maxᵘ l₂) [ σ₁ ]
  ⊩ΠΣ≡ΠΣ∷U {l} {l₁} {l₂} {Δ} {σ₁} ok A₁≡A₂∷U B₁≡B₂∷U σ₁≡σ₂ =
    case ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ B₁≡B₂∷U of λ
      B₁≡B₂ →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ A₁≡A₂∷U σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂]∷U →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ B₁≡B₂∷U σ₁≡σ₂ of λ
      B₁[σ₁⇑]≡B₂[σ₂⇑]∷U →
    case wf-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U of λ
      (⊩A₁[σ₁] , ⊩A₂[σ₂]) →
    case wf-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U of λ
      (⊩B₁[σ₁] , _) →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ (conv-∙-⊩ᵛ∷ A₁≡A₂ (wf-⊩ᵛ≡∷ B₁≡B₂∷U .proj₂)) $
         wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ of λ
      ⊩B₂[σ₂] →
    let ⊩m : Δ ⊩Level (l₁ maxᵘ l₂) [ σ₁ ] ∷Level
        ⊩m = {!   !}
    in
    Type→⊩≡∷U⇔ ΠΣₙ ΠΣₙ .proj₂
      ( -- PE.subst (_ <ᵘ_) ⊔ᵘ-idem
          -- (⊔ᵘ-mono (⊩∷U⇔ .proj₁ ⊩A₁[σ₁] .proj₁)
          --    (⊩∷U⇔ .proj₁ ⊩B₁[σ₁] .proj₁))
        <-sucᵘ ⊩m
      , ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[]
          -- (ΠΣ-congᵛ ok (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘʳ A₁≡A₂) (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘˡ B₁≡B₂))
          (ΠΣ-congᵛ ok (emb-⊩ᵛ≡ {!   !} A₁≡A₂) {!   !})
          σ₁≡σ₂
      -- , ≅ₜ-ΠΣ-cong (escape-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U)
      --     (escape-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U) ok
      , ≅ₜ-ΠΣ-cong {!   !} {!   !} {!escape-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U!} {! escape-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U  !} ok
      )

{-
opaque

  -- Validity of equality preservation for Π and Σ, seen as term
  -- formers.

  ΠΣ-congᵗᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U l₁ →
    Γ ∙ A₁ ⊩ᵛ⟨ wk1 l ⟩ B₁ ≡ B₂ ∷ U (wk1 l₂) →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡
      ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U (l₁ maxᵘ l₂)
  ΠΣ-congᵗᵛ ok A₁≡A₂ B₁≡B₂ =
    {!   !}
    {-
    case wf-⊩ᵛ≡∷ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ∷ (⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂) ⊩B₂ of λ
      ⊩B₂ →
    ⊩ᵛ≡∷⇔ .proj₂
      ( PE.subst (_ ⊩ᵛ⟨_⟩ _) ⊔ᵘ-idem
          (emb-⊩ᵛ
             (⊔ᵘ-mono (⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ ⊩A₁) .proj₁)
                (⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ ⊩B₁) .proj₁))
             (⊩ᵛU (wf-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ A₁≡A₂ .proj₁)))))
      , ⊩ΠΣ≡ΠΣ∷U ok A₁≡A₂ B₁≡B₂
      )
    -}

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- Validity of Π and Σ, seen as term formers.

  ΠΣᵗᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U l₁ →
    Γ ∙ A ⊩ᵛ⟨ wk1 l ⟩ B ∷ U (wk1 l₂) →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (l₁ maxᵘ l₂)
  ΠΣᵗᵛ ok ⊩A ⊩B =
    {!   !}
    {-
    ⊩ᵛ∷⇔ .proj₂
      ( PE.subst (_ ⊩ᵛ⟨_⟩ _) ⊔ᵘ-idem
          (emb-⊩ᵛ
             (⊔ᵘ-mono (⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ ⊩A) .proj₁)
                (⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ ⊩B) .proj₁))
             (⊩ᵛU (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩A))))
      , ⊩ΠΣ≡ΠΣ∷U ok (refl-⊩ᵛ≡∷ ⊩A) (refl-⊩ᵛ≡∷ ⊩B)
      )
    -}
-}
