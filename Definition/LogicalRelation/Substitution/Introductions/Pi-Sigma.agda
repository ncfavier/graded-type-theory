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

open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Level R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Var R
import Definition.LogicalRelation.Weakening R as W
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
import Definition.Typed.Weakening R as TW
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  n                         : Nat
  Γ Δ                       : Con Term _
  A A₁ A₂ B B₁ B₂ C t t₁ t₂ u : Term _
  σ σ₁ σ₂                   : Subst _ _
  p p₁ p₂ q q₁ q₂           : M
  l l′ l₁ l₁′ l₂ l₂′        : Universe-level
  b b₁ b₂                   : BinderMode

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_ wf-⊩≡∷

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ΠΣ⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (Γ ⊢≅ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A ×
      (∀ {t u} →
       Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀)))
  ⊩ΠΣ⇔ {n} {b} {p} {q} {A} {B} =
      (λ ⊩AB →
        case B-view ⊩AB of λ {
          (Bᵣ (Bᵣ _ _ ⇒*ΠΣ ΠΣ≅ΠΣ ⊩wk-A ⊩wk-B wk-B≡wk-B _)) →
        case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
          (PE.refl , PE.refl , _) →
          ΠΣ≅ΠΣ
        , λ ρ⊇ →
            let ⊩wk-ρ-A = ⊩wk-A ρ⊇ in
              ⊩wk-ρ-A
            , λ t≡u′@(⊩wk-ρ-A′ , t≡u) →
                let (_ , ⊩t) , (_ , ⊩u) = wf-⊩≡∷ t≡u′
                    ⊩t = irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩t
                    ⊩u = irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩u
                in
                  ⊩wk-B ρ⊇ ⊩t
                , ⊩wk-B ρ⊇ ⊩u
                , wk-B≡wk-B ρ⊇ ⊩t ⊩u
                    (irrelevanceEqTerm ⊩wk-ρ-A′ ⊩wk-ρ-A t≡u) }})
    , (λ (ΠΣ≅ΠΣ , rest) →
         let ⊢ΠΣ , _    = wf-⊢≡ (≅-eq ΠΣ≅ΠΣ)
             _ , _ , ok = inversion-ΠΣ ⊢ΠΣ
         in
         Bᵣ (BM b p q)
           (Bᵣ _ _ (id ⊢ΠΣ) ΠΣ≅ΠΣ
              (λ ρ⊇ → rest ρ⊇ .proj₁)
              (λ ρ⊇ ⊩t →
                 wf-⊩≡
                   (rest ρ⊇ .proj₂ $
                    refl-⊩≡∷ (rest _ .proj₁ , ⊩t))
                   .proj₁)
              (λ ρ⊇ ⊩t _ t≡u →
                 ⊩≡→⊩≡/
                   (wf-⊩≡
                      (rest ρ⊇ .proj₂ $
                       refl-⊩≡∷ (rest _ .proj₁ , ⊩t))
                      .proj₁) $
                 rest ρ⊇ .proj₂ (rest _ .proj₁ , t≡u))
              ok))

opaque

  -- A variant of ⊩ΠΣ⇔.

  ⊩ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q ×
    Γ ⊩⟨ l ⟩ A × (⦃ inc : Neutrals-included ⦄ → Γ ∙ A ⊩⟨ l ⟩ B)
  ⊩ΠΣ→ ⊩ΠΣ =
    let ⊢A , _ , ok  = inversion-ΠΣ (escape-⊩ ⊩ΠΣ)
        _ , hyp      = ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ
        ⊩wk-id-A , _ = hyp (id (wf ⊢A))
        ⊩A           = PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-id-A
    in
        ok , ⊩A
      , (case hyp (includedʷʳ (TW.stepʷ TW.id (escape-⊩ ⊩A))) of λ
           (⊩wk₁-A , wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀) →
         PE.subst (_⊩⟨_⟩_ _ _) (wkSingleSubstId _)
           (proj₁ $ wf-⊩≡ $
            wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀ $
            refl-⊩≡∷ (⊩var here ⊩wk₁-A)))

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡⇔ :
    {C : Term n} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ C ×
     ∃₂ λ A′ B′ → Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≅ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀)))
  ⊩ΠΣ≡⇔ =
      (λ (⊩ΠΣ , ⊩C , ΠΣ≡C) →
         case B-view ⊩ΠΣ of λ {
           (Bᵣ (Bᵣ _ _ ⇒*ΠΣ _ ⊩wk-A ⊩wk-B _ ok)) →
         case ΠΣ≡C of λ
           (B₌ _ _ ⇒*ΠΣ′ ΠΣ≅ΠΣ wk-A≡wk-A′ wk-B≡wk-B′) →
         case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
           ⊩ΠΣ , ⊩C
          , _ , _ , ⇒*ΠΣ′ , ΠΣ≅ΠΣ
          , λ ρ⊇ →
              case ⊩ΠΣ⇔ .proj₁ (wf-⊩≡ (⊩-⇒* ⇒*ΠΣ′ ⊩C) .proj₂)
                    .proj₂ ρ⊇ of λ
                (⊩wk-ρ-A′ , wk-ρ⇑-B′≡wk-ρ⇑-B′) →
              case ⊩wk-A ρ⊇ , ⊩wk-ρ-A′ , wk-A≡wk-A′ ρ⊇ of λ
                wk-ρ-A≡wk-ρ-A′ →
                wk-ρ-A≡wk-ρ-A′
              , λ ⊩t@(⊩wk-ρ-A , ⊩t′) →
                  let ⊩wk-ρ⇑-B[t] =
                        ⊩wk-B ρ⊇ (irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩t′)
                      ⊩wk-ρ⇑-B[t]′ = ⊩wk-ρ⇑-B[t]
                  in
                    ⊩wk-ρ⇑-B[t]′
                  , wf-⊩≡
                      (wk-ρ⇑-B′≡wk-ρ⇑-B′ $
                      refl-⊩≡∷ (conv-⊩∷ wk-ρ-A≡wk-ρ-A′ ⊩t))
                      .proj₁
                  , irrelevanceEq ⊩wk-ρ⇑-B[t] ⊩wk-ρ⇑-B[t]′
                      (wk-B≡wk-B′ ρ⊇ $
                      irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩t′) }})
    , (λ (⊩ΠΣ , ⊩C , _ , _ , C⇒* , ΠΣ≅ΠΣ , rest) →
         case B-view ⊩ΠΣ of λ {
           (Bᵣ ⊩ΠΣ₁@(Bᵣ _ _ ⇒*ΠΣ₁ _ ⊩wk-A₁ ⊩wk-B₁ _ ok)) →
         case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ₁ ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
         Bᵣ _ ⊩ΠΣ₁ , ⊩C ,
         (_ ⊩⟨ _ ⟩ _ ≡ _ / Bᵣ _ ⊩ΠΣ₁ ∋
         B₌ _ _ C⇒* ΠΣ≅ΠΣ
           (λ ρ⊇ → ⊩≡→⊩≡/ (⊩wk-A₁ ρ⊇) (rest ρ⊇ .proj₁))
           (λ ρ⊇ ⊩t →
             case rest ρ⊇ of λ
               (wk-ρ-A₁≡wk-ρ-A₂ , wk-ρ⇑-B₁≡wk-ρ⇑-B₂) →
             case wf-⊩≡ wk-ρ-A₁≡wk-ρ-A₂ .proj₁ of λ
               ⊩wk-ρ-A₁ →
             ⊩≡→⊩≡/ (⊩wk-B₁ ρ⊇ ⊩t) $
             wk-ρ⇑-B₁≡wk-ρ⇑-B₂
               ( ⊩wk-ρ-A₁
               , irrelevanceTerm (⊩wk-A₁ ρ⊇) ⊩wk-ρ-A₁ ⊩t
               ))) }})

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ⇔ :
    {A₁ A₂ : Term n} {B₁ B₂ : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)))
  ⊩ΠΣ≡ΠΣ⇔
    {n} {Γ} {l} {b₁} {p₁} {q₁} {b₂} {p₂} {q₂} {A₁} {A₂} {B₁} {B₂} =

    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂  ⇔⟨ ⊩ΠΣ≡⇔ ⟩

    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     ∃₂ λ A B →
     Γ ⊢ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇒* ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B [ t ]₀)))       ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ ⊩ΠΣ₂ →
                                                                            (λ (_ , _ , ΠΣ⇒*ΠΣ , ΠΣ≅ΠΣ , rest) →
                                                                               case whnfRed* ΠΣ⇒*ΠΣ ΠΣₙ of λ {
                                                                                 PE.refl →
                                                                               ΠΣ≅ΠΣ , PE.refl , PE.refl , PE.refl , rest })
                                                                          , (λ { (ΠΣ≅ΠΣ , PE.refl , PE.refl , PE.refl , rest) →
                                                                                  _ , _ , id (escape-⊩ ⊩ΠΣ₂) , ΠΣ≅ΠΣ , rest })) ⟩
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
     ρ ∷ʷʳ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
     (∀ {t} →
      Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
      Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀))        □⇔

opaque

  -- A variant of ⊩ΠΣ≡ΠΣ⇔.

  ⊩ΠΣ≡ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    ΠΣ-allowed b₁ p₁ q₁ × b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ ×
    (⦃ inc : Neutrals-included ⦄ → Γ ∙ A₁ ⊩⟨ l ⟩ B₁ ≡ B₂)
  ⊩ΠΣ≡ΠΣ→ ΠΣ≡ΠΣ =
    let ⊩ΠΣ₁ , _ , ΠΣ≅ΠΣ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , rest =
          ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ
        ok , ⊩A₁ , _ = ⊩ΠΣ→ ⊩ΠΣ₁
    in
      ok , b₁≡b₂ , p₁≡p₂ , q₁≡q₂
    , PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
        (rest (id (wfEq (≅-eq ΠΣ≅ΠΣ))) .proj₁)
    , let wk₁-A₁≡wk₁-A₂ ,
            wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ =
            rest (includedʷʳ (TW.stepʷ TW.id (escape ⊩A₁)))
      in
      PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _) (wkSingleSubstId _)
        (wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ $
         ⊩var here (wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁))

-- See also ⊩ᵛΠΣ→ and ⊩ᵛΠΣ⇔ below.

------------------------------------------------------------------------
-- Some substitution lemmas

opaque

  -- A substitution lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ ≡ B₂ [ t₂ ]₀
  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ {B₁} {B₂} {t₁} {t₂} ΠΣ≡ΠΣ t₁≡t₂ =
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , _ , _ , _ , _ , rest) →
    case ⊩ΠΣ→ ⊩ΠΣ₁ of λ
      (_ , ⊩A₁ , _) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (ΠΣ≅ΠΣ , rest₁) →
    case wf (wf-⊢≡ (≅-eq ΠΣ≅ΠΣ) .proj₁) of λ
      ⊢Γ →
    B₁ [ t₁ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁) $
                   rest₁ (id ⊢Γ) .proj₂ $
                   PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩≡∷ ⊩A₁ t₁≡t₂ ⟩⊩
    B₁ [ t₂ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₂) $
                   rest (id ⊢Γ) .proj₂ $
                   PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) $
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
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ]
  ⊩ΠΣ {A} {B} ⊢ΠΣ ⊩A ⊩B ⊩σ =
    ⊩ΠΣ⇔ .proj₂
      ( with-inc-⊢≅ (refl $ subst-⊢ ⊢ΠΣ (escape-⊩ˢ∷ ⊩σ .proj₂))
          (≅-ΠΣ-cong
             (R.escape-⊩≡ $
              R.refl-⊩≡ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ)
             (R.escape-⊩≡ ⦃ inc = included ⦄ $
              R.refl-⊩≡ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩B (⊩ˢ∷-liftSubst ⊩A ⊩σ)))
             (inversion-ΠΣ ⊢ΠΣ .proj₂ .proj₂))
      , λ ρ⊇ →
          let instance
                inc = wk-Neutrals-included-or-empty← ρ⊇
              ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
          in
            PE.subst (_⊩⟨_⟩_ _ _) (PE.sym $ wk-subst A)
              (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ ⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
          , λ t≡u →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B)
                (PE.sym $ singleSubstWkComp _ _ B) $
              R.⊩≡→ $
              ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A
                  , (R.→⊩≡∷ $
                     PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) t≡u)
                  )
                , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
                )
      )

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as type
  -- formers.

  ⊩ΠΣ≡ΠΣ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ]
  ⊩ΠΣ≡ΠΣ {A₁} {B₁} {A₂} {B₂} ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ ⦃ inc ⦄ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case wf-⊢≡ ΠΣ≡ΠΣ of λ
      (⊢ΠΣ₁ , ⊢ΠΣ₂) →
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩ΠΣ ⊢ΠΣ₁ ⊩A₁ ⊩B₁ ⊩σ₁
      , ⊩ΠΣ ⊢ΠΣ₂ ⊩A₂ ⊩B₂ ⊩σ₂
      , with-inc-⊢≅ (subst-⊢≡ ΠΣ≡ΠΣ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂))
          (≅-ΠΣ-cong
             (R.escape-⊩≡ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
             (R.escape-⊩≡ ⦃ inc = included ⦄ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
              ⊩ˢ≡∷-liftSubst ⊩A₁ σ₁≡σ₂)
             (inversion-ΠΣ ⊢ΠΣ₁ .proj₂ .proj₂))
      , PE.refl , PE.refl , PE.refl
      , λ ρ⊇ →
          let instance
                inc = wk-Neutrals-included-or-empty← ρ⊇
              ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
          in
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
              (PE.sym $ wk-subst A₁) (PE.sym $ wk-subst A₂)
              (R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ $ ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂)
          , λ ⊩t →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B₁)
                (PE.sym $ singleSubstWkComp _ _ B₂) $
              R.⊩≡→ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A₁
                  , (R.refl-⊩≡∷ $
                     PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁) $
                     R.→⊩∷ ⊩t)
                  )
                , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
                )
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as type
  -- formers.

  ΠΣ-congᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-congᵛ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁)
      , ⊩ΠΣ≡ΠΣ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂
      )

opaque

  -- Validity of Π and Σ, seen as type formers.

  ΠΣᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣᵛ ⊢ΠΣ ⊩A ⊩B =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ΠΣ-congᵛ (refl ⊢ΠΣ) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡ ⊩B)

opaque

  -- A kind of inversion lemma for Π- and Σ-types.

  ⊩ᵛΠΣ→ :
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → ΠΣ-allowed b p q) ×
    Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ l ⟩ B
  ⊩ᵛΠΣ→ {B} ⊩ΠΣAB =
    case ⊩ᵛ⇔ʰ .proj₁ ⊩ΠΣAB of λ
      (⊩Γ , ΠΣAB≡ΠΣAB) →
    case ⊩ᵛ⇔ʰ .proj₂
           ( ⊩Γ
           , proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
             ⊩ΠΣ≡ΠΣ→ ∘→ ΠΣAB≡ΠΣAB
           ) of λ
      ⊩A →
      ⊩ΠΣ→ (R.⊩→ (⊩ᵛ→⊩ ⊩ΠΣAB)) .proj₁
    , ⊩A
    , ⊩ᵛ⇔ʰ .proj₂
        ( ⊩ᵛ-∙-intro ⊩A
        , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
            case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
              ((_ , _ , head-σ₁≡head-σ₂) , tail-σ₁≡tail-σ₂) →
            B [ σ₁ ]                             ≡˘⟨ substVar-to-subst consSubst-η B ⟩⊩≡
            B [ consSubst (tail σ₁) (head σ₁) ]  ≡˘⟨ singleSubstComp _ _ B ⟩⊩≡
            B [ tail σ₁ ⇑ ] [ head σ₁ ]₀         ≡⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (ΠΣAB≡ΠΣAB tail-σ₁≡tail-σ₂) (R.⊩≡∷→ head-σ₁≡head-σ₂) ⟩⊩∎≡
            B [ tail σ₂ ⇑ ] [ head σ₂ ]₀         ≡⟨ singleSubstComp _ _ B ⟩
            B [ consSubst (tail σ₂) (head σ₂) ]  ≡⟨ substVar-to-subst consSubst-η B ⟩
            B [ σ₂ ]                             ∎
        )
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛΠΣ⇔ :
    ⦃ inc : Neutrals-included ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q × Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ l ⟩ B)
  ⊩ᵛΠΣ⇔ {B} =
      Σ.map (λ ok → ok ⦃ inc = included ⦄) idᶠ ∘→ ⊩ᵛΠΣ→
    , (λ (ok , ⊩A , ⊩B) →
         ΠΣᵛ (ΠΣⱼ (escape-⊩ᵛ ⦃ inc = included ⦄ ⊩B) ok) ⊩A ⊩B)
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as term formers

opaque

  -- Validity of Π and Σ, seen as term formers.

  ⊩ΠΣ∷U :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (t maxᵘ u) →
    Γ ⊩ᵛ⟨ l₁ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l₂ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A ∷ U t →
    Γ ∙ A ⊩ᵛ⟨ l₂′ ⟩ B ∷ U (wk1 u) →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ ωᵘ ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ] ∷ U (t maxᵘ u) [ σ ]
  ⊩ΠΣ∷U {A} {B} {t} {u} ⊢ΠΣ∷U ⊩t ⊩u ⊩A∷U ⊩B∷U ⊩σ =
    case R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩A∷U ⊩σ of λ
      ⊩A[σ] →
    case ⊩∷Level⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ of λ
      ⊩t[σ] →
    case ⊩∷Level⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ of λ
      ⊩u[σ] →
    case inversion-ΠΣ-U ⊢ΠΣ∷U of λ
      (_ , _ , _ , _ , _ , ok) →
    let ⊢ΠΣ[] = refl $ subst-⊢∷ ⊢ΠΣ∷U $ escape-⊩ˢ∷ ⊩σ .proj₂
        ⊢≅ΠΣ[] = with-inc-⊢≅∷ ⊢ΠΣ[] $ ≅ₜ-ΠΣ-cong
            (escapeLevel ⊩t[σ]) (escapeLevel ⊩u[σ])
            (escape-⊩≡∷ (refl-⊩≡∷ ⊩A[σ]))
            (PE.subst (_⊢_≅_∷_ _ _ _) (wk1-liftSubst (U u)) $
              R.escape-⊩≡∷ ⦃ inc = included ⦄ $ R.refl-⊩≡∷ $
                ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩B∷U (⊩ˢ∷-liftSubst (⊩ᵛ∷U→⊩ᵛ ⊩A∷U) ⊩σ))
            ok
    in Type→⊩∷U⇔ ΠΣₙ .proj₂
      ( ⊩Levelmaxᵘ∷Level ⊩t[σ] ⊩u[σ]
      , <ᵘ-ωᵘ
      , ⊩ΠΣ⇔ .proj₂
        ( ≅-univ ⊢≅ΠΣ[]
        , λ ρ⊇ →
            let instance
                  inc = wk-Neutrals-included-or-empty← ρ⊇
                ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
                ([t] , t< , ⊩A , _) = ⊩∷U⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩A∷U $ ⊩ˢ∷-•ₛ ρ⊇ ⊩σ
            in
              emb-⊩ (PE.subst₂ _≤ᵘ_ (PE.sym $ W.wk-↑ᵘ ρ⊇ ⊩t[σ] [t] (PE.sym $ wk-subst t)) (PE.sym $ ↑ᵘ-maxᵘ ⊩t[σ] ⊩u[σ]) ≤ᵘ⊔ᵘʳ) (PE.subst (_⊩⟨_⟩_ _ _) (PE.sym $ wk-subst A) ⊩A)
            , λ t≡u →
                let ([u] , u< , B≡B , _) = ⊩≡∷U⇔ .proj₁ $ R.⊩≡∷→ $
                      ⊩ᵛ∷⇔ .proj₁ ⊩B∷U .proj₂ $ ⊩ˢ≡∷∙⇔ .proj₂ $
                          ( _ , ⊩ᵛ∷U→⊩ᵛ ⊩A∷U
                          , (R.→⊩≡∷ $ emb-⊩≡∷ ≤ᵘ-ωᵘ $ PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) t≡u))
                        , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
                in emb-⊩≡ (PE.subst₂ _≤ᵘ_ (PE.sym $ W.wk-↑ᵘ ρ⊇ ⊩u[σ] [u] (PE.trans (wk1-tail u) (PE.sym $ wk-subst u))) (PE.sym $ ↑ᵘ-maxᵘ ⊩t[σ] ⊩u[σ]) ≤ᵘ⊔ᵘˡ) $ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                    (PE.sym $ singleSubstWkComp _ _ B)
                    (PE.sym $ singleSubstWkComp _ _ B)
                    B≡B
        )
      , ⊢≅ΠΣ[]
      )

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as term
  -- formers.

  ⊩ΠΣ≡ΠΣ∷U :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
      U (t maxᵘ u) →
    Γ ⊩ᵛ⟨ l₁ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l₂ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A₁ ≡ A₂ ∷ U t →
    Γ ∙ A₁ ⊩ᵛ⟨ l₂′ ⟩ B₁ ≡ B₂ ∷ U (wk1 u) →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ ωᵘ ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ] ∷ U (t maxᵘ u) [ σ₁ ]
  ⊩ΠΣ≡ΠΣ∷U {A₁} {B₁} {A₂} {B₂} {t} {u} {Δ} {σ₁} ΠΣ≡ΠΣ ⊩t ⊩u A₁≡A₂∷U B₁≡B₂∷U σ₁≡σ₂ =
    case wf-⊢≡∷ ΠΣ≡ΠΣ of λ
      (_ , ⊢ΠΣ₁ , ⊢ΠΣ₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂ of λ
      t[σ₁]≡t[σ₂] →
    case ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂ of λ
      u[σ₁]≡u[σ₂] →
    case ⊩∷Level⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ₁ of λ
      ⊩t[σ₁] →
    case ⊩∷Level⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ₁ of λ
      ⊩u[σ₁] →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ B₁≡B₂∷U of λ
      B₁≡B₂ →
    case ⊩ᵛ≡∷⇔ .proj₁ A₁≡A₂∷U .proj₂ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂]∷U →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ B₁≡B₂∷U σ₁≡σ₂ of λ
      B₁[σ₁⇑]≡B₂[σ₂⇑]∷U →
    case Type→⊩∷U⇔ ΠΣₙ .proj₁ $
        ⊩ΠΣ∷U ⊢ΠΣ₁ ⊩t ⊩u (wf-⊩ᵛ≡∷ A₁≡A₂∷U .proj₁) (wf-⊩ᵛ≡∷ B₁≡B₂∷U .proj₁) ⊩σ₁ of λ
      (_ , _ , ⊩ΠΣ₁ , _) →
    case Type→⊩∷U⇔ ΠΣₙ .proj₁ $
        ⊩ΠΣ∷U ⊢ΠΣ₂ ⊩t ⊩u (wf-⊩ᵛ≡∷ A₁≡A₂∷U .proj₂)
        (conv-∙-⊩ᵛ∷ A₁≡A₂ (wf-⊩ᵛ≡∷ B₁≡B₂∷U .proj₂)) ⊩σ₂ of λ
      (_ , _ , ⊩ΠΣ₂ , _) →
    let _ , _ , ok = inversion-ΠΣ (wf-⊢≡ (univ ΠΣ≡ΠΣ) .proj₁)
        ΠΣ[]≡ΠΣ[] = subst-⊢≡∷ ΠΣ≡ΠΣ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂)
        ΠΣ[]≅ΠΣ[] = with-inc-⊢≅∷ ΠΣ[]≡ΠΣ[] $ ≅ₜ-ΠΣ-cong
            (escapeLevel ⊩t[σ₁]) (escapeLevel ⊩u[σ₁])
            (R.escape-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U)
            (PE.subst (_⊢_≅_∷_ _ _ _) (wk1-liftSubst (U u))
              (R.escape-⊩≡∷ ⦃ inc = included ⦄ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U))
            ok
    in Type→⊩≡∷U⇔ ΠΣₙ ΠΣₙ .proj₂
      ( ⊩Levelmaxᵘ∷Level ⊩t[σ₁] ⊩u[σ₁]
      , <ᵘ-ωᵘ
      , ⊩ΠΣ≡ΠΣ⇔ .proj₂
        ( PE.subst (flip (_⊩⟨_⟩_ _) _) (↑ᵘ-irrelevance _ _) ⊩ΠΣ₁
        , PE.subst (flip (_⊩⟨_⟩_ _) _)
            (↑ᵘ-cong _ _ $ symLevel $ ⊩Levelmaxᵘ≡maxᵘ∷Level t[σ₁]≡t[σ₂] u[σ₁]≡u[σ₂]) ⊩ΠΣ₂
        , ≅-univ ΠΣ[]≅ΠΣ[]
        , PE.refl , PE.refl , PE.refl
        , λ ρ⊇ →
            let instance
                  inc = wk-Neutrals-included-or-empty← ρ⊇
                ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
                ([t] , t< , A≡A , _) = ⊩≡∷U⇔ .proj₁ $ R.⊩≡∷→ $
                  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ A₁≡A₂∷U $ ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
            in
              emb-⊩≡ (PE.subst₂ _≤ᵘ_ (PE.sym $ W.wk-↑ᵘ ρ⊇ ⊩t[σ₁] [t] (PE.sym $ wk-subst t)) (PE.sym $ ↑ᵘ-maxᵘ ⊩t[σ₁] ⊩u[σ₁]) ≤ᵘ⊔ᵘʳ) (PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ wk-subst A₁) (PE.sym $ wk-subst A₂) A≡A)
            , λ ⊩t →
                let ([u] , u< , B≡B , _) = ⊩≡∷U⇔ .proj₁ $ R.⊩≡∷→ $
                      ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ B₁≡B₂∷U $ ⊩ˢ≡∷∙⇔ .proj₂ $
                          ( _ , wf-⊩ᵛ≡ A₁≡A₂ .proj₁
                          , (R.emb-⊩≡∷ ≤ᵘ-ωᵘ $ R.refl-⊩≡∷ $ PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁) $ R.→⊩∷ ⊩t))
                        , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
                in emb-⊩≡ (PE.subst₂ _≤ᵘ_ (PE.sym $ W.wk-↑ᵘ ρ⊇ ⊩u[σ₁] [u] (PE.trans (wk1-tail u) (PE.sym $ wk-subst u))) (PE.sym $ ↑ᵘ-maxᵘ ⊩t[σ₁] ⊩u[σ₁]) ≤ᵘ⊔ᵘˡ) $ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                    (PE.sym $ singleSubstWkComp _ _ B₁)
                    (PE.sym $ singleSubstWkComp _ _ B₂)
                    B≡B
        )
      , ΠΣ[]≅ΠΣ[]
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as term
  -- formers.

  ΠΣ-congᵗᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
      U (t maxᵘ u) →
    Γ ⊩ᵛ⟨ l₁ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l₂ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A₁ ≡ A₂ ∷ U t →
    Γ ∙ A₁ ⊩ᵛ⟨ l₂′ ⟩ B₁ ≡ B₂ ∷ U (wk1 u) →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡
      ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U (t maxᵘ u)
  ΠΣ-congᵗᵛ ΠΣ≡ΠΣ ⊩t ⊩u A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (maxᵘᵛ ⊩t ⊩u)
      , ⊩ΠΣ≡ΠΣ∷U ΠΣ≡ΠΣ ⊩t ⊩u A₁≡A₂ B₁≡B₂
      )

opaque

  -- Validity of Π and Σ, seen as term formers.

  ΠΣᵗᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (t maxᵘ u) →
    Γ ⊩ᵛ⟨ l₁ ⟩ t ∷ Level →
    Γ ⊩ᵛ⟨ l₂ ⟩ u ∷ Level →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A ∷ U t →
    Γ ∙ A ⊩ᵛ⟨ l₂′ ⟩ B ∷ U (wk1 u) →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (t maxᵘ u)
  ΠΣᵗᵛ ⊢ΠΣ ⊩t ⊩u ⊩A ⊩B =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (maxᵘᵛ ⊩t ⊩u)
      , ⊩ΠΣ≡ΠΣ∷U (refl ⊢ΠΣ) ⊩t ⊩u (refl-⊩ᵛ≡∷ ⊩A) (refl-⊩ᵛ≡∷ ⊩B)
      )
