------------------------------------------------------------------------
-- Validity for unit types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Properties.Primitive R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Level R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (inj₂)

private
  variable
    n : Nat
    Γ Δ : Con Term n
    σ σ₁ σ₂ : Subst _ _
    s s₁ s₂ : Strength
    ℓ : Universe-level
    A A₁ A₂ l l′ l″ l‴ l₁ l₂ t t₁ t₂ u u₁ u₂ : Term n
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding _⊩_≤_∷Level _⊩⟨_⟩_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Unit⇔ :
    Γ ⊩⟨ l′ ⟩ Unit s l ⇔
    (Γ ⊩ l ≤ l′ ∷Level × Unit-allowed s)
  ⊩Unit⇔ {Γ} {l′} {l} =
      (λ (⊩l′ , ⊩Unit) →
        case Unit-elim ⊩Unit of λ {
          (Unitᵣ (Unitᵣ k ⊩k k≤ Unit⇒*Unit ok)) →
        case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
          (PE.refl , PE.refl) →
        (⊩k , ⊩l′ , k≤) , ok }})
    , (λ ((⊩l , ⊩l′ , l≤l′) , ok) →
        ⊩l′ , Unitᵣ′ _ ⊩l l≤l′ (id (Unitⱼ (escapeLevel ⊩l) ok)) ok)

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Unit⇔ :
    Γ ⊩⟨ l′ ⟩ t ∷ Unit s l ⇔
    (Γ ⊩ l ≤ l′ ∷Level × Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷ Unit s l / l)
  ⊩∷Unit⇔ {Γ} {l′} {l} =
      (λ ((⊩l′ , ⊩Unit) , ⊩t) →
        case Unit-elim ⊩Unit of λ {
          (Unitᵣ (Unitᵣ k ⊩k k≤ Unit⇒*Unit ok)) →
        case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
          (PE.refl , PE.refl) →
        (⊩k , ⊩l′ , k≤) , ok , ⊩t }})
    , (λ (l≤l′ , ok , ⊩t) →
        ⊩Unit⇔ .proj₂ (l≤l′ , ok) , ⊩t)

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_ _⊩_≤_∷Level

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡⇔ :
    Γ ⊩⟨ l′ ⟩ Unit s l ≡ A ⇔
    (Γ ⊩ l ≤ l′ ∷Level × Unit-allowed s × ∃ λ k → Γ ⊢ A ⇒* Unit s k × Γ ⊩Level l ≡ k ∷Level)
  ⊩Unit≡⇔ {Γ} {l′} {s} {l} {A} =
      (λ ((⊩l′ , ⊩Unit₁) , ⊩A , Unit₁≡A) →
        case Unit-elim ⊩Unit₁ of λ {
          (Unitᵣ (Unitᵣ l ⊩l l≤ Unit⇒*Unit ok)) →
        case Unit₁≡A of λ
          (Unit₌ k A⇒*Unit l≡k) →
        case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
          (PE.refl , PE.refl) →
        (⊩l , ⊩l′ , l≤) , ok , k , A⇒*Unit , l≡k }})
      , (λ (l≤l′@(⊩l , ⊩l′ , p) , ok , k , A⇒*Unit , l≡k) →
        let ⊩k = wf-⊩Level l≡k .proj₂
            Unitl≡Unitk
              = (⊩l′ , Unitᵣ′ _ ⊩l p (id (Unitⱼ (escapeLevel ⊩l) ok)) ok)
              , (⊩l′ , Unitᵣ′ _ ⊩k (PE.subst (_≤ᵘ ↑ᵘ ⊩l′) (↑ᵘ-cong ⊩l ⊩k l≡k) p) (id (Unitⱼ (escapeLevel ⊩k) ok)) ok)
              , Unit₌ _ (id (Unitⱼ (escapeLevel ⊩k) ok)) l≡k
        in sym-⊩≡
           (A         ⇒*⟨ A⇒*Unit ⟩⊩
            Unit s k  ≡⟨ sym-⊩≡ Unitl≡Unitk ⟩⊩
            Unit s l  ∎⟨ ⊩Unit⇔ .proj₂ (l≤l′ , ok) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s₁ l₁ ≡ Unit s₂ l₂ ⇔
    (Γ ⊩ l₁ ≤ l ∷Level × Unit-allowed s₁ × s₁ PE.≡ s₂ × Γ ⊩Level l₁ ≡ l₂ ∷Level)
  ⊩Unit≡Unit⇔ {Γ} {l} {s₁} {l₁} {s₂} {l₂} =
      (λ Unit≡Unit →
        case ⊩Unit≡⇔ .proj₁ Unit≡Unit of λ
          (l₁≤l , ok , k , D , l₁≡k) →
        case Unit-PE-injectivity (whnfRed* D Unitₙ) of λ {
          (s₂≡s₁ , PE.refl) → l₁≤l , ok , PE.sym s₂≡s₁ , l₁≡k })
    , λ { (l₁≤l , ok , PE.refl , l₁≡l₂) →
          ⊩Unit≡⇔ .proj₂
            ( l₁≤l , ok , _
            , id (Unitⱼ (escapeLevel (wf-⊩Level l₁≡l₂ .proj₂)) ok)
            , l₁≡l₂
            ) }

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Unit⇔ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ Unit s l ⇔
    (Γ ⊩ l ≤ l′ ∷Level ×
     Unit-allowed s ×
     Γ ⊩Unit⟨ s ⟩ t ∷ Unit s l / l ×
     Γ ⊩Unit⟨ s ⟩ u ∷ Unit s l / l ×
     Γ ⊩Unit⟨ s ⟩ t ≡ u ∷ Unit s l / l)
  ⊩≡∷Unit⇔ {Γ} {l′} {s} {l} =
      (λ ((⊩l′ , ⊩Unit) , ⊩t , ⊩u , t≡u) →
        case Unit-elim ⊩Unit of λ {
          (Unitᵣ (Unitᵣ k ⊩k k≤ Unit⇒*Unit ok)) →
        case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
          (PE.refl , PE.refl) →
        (⊩k , ⊩l′ , k≤) , ok , ⊩t , ⊩u , t≡u }})
    , (λ (l≤l′ , ok , ⊩t , ⊩u , t≡u) →
        ⊩Unit⇔ .proj₂ (l≤l′ , ok) , ⊩t , ⊩u , t≡u)

------------------------------------------------------------------------
-- Unit

opaque

  -- If the type Unit s l is valid, then it is allowed.

  ⊩ᵛUnit→Unit-allowed :
    Γ ⊩ᵛ⟨ l′ ⟩ Unit s l →
    Unit-allowed s
  ⊩ᵛUnit→Unit-allowed {Γ} {l′} {s} {l} =
    Γ ⊩ᵛ⟨ l′ ⟩ Unit s l                 →⟨ ⊩ᵛ→⊩ ⟩
    Γ ⊩⟨ l′ ⟩ Unit s l                  ⇔⟨ ⊩Unit⇔ ⟩→
    Γ ⊩ l ≤ l′ ∷Level × Unit-allowed s  →⟨ proj₂ ⟩
    Unit-allowed s                      □

opaque

  -- Reducibility for Unit.

  ⊩Unit :
    Γ ⊩Level l ∷Level →
    Unit-allowed s →
    Γ ⊩⟨ l ⟩ Unit s l
  ⊩Unit ⊩l ok = ⊩Unit⇔ .proj₂ (≤-reflᵘ ⊩l , ok)

opaque

  -- Validity for Unit, seen as a type former.

  Unitᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ l ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ l ⟩ Unit s l
  Unitᵛ {Γ} {l′} {l} {s} ⊩l ok =
    let ⊩ᵛᵘl = ⊩ᵛ∷Level⇔ .proj₁ ⊩l .proj₂ in
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛᵘl
      , λ σ₁≡σ₂ →
          let l[σ₁]≡l[σ₂] = ⊩ᵛᵘ→⊩ˢ≡∷→⊩[]≡[] ⊩ᵛᵘl σ₁≡σ₂ in
          ⊩Unit≡Unit⇔ .proj₂
            ( ≤-reflᵘ (wf-⊩Level l[σ₁]≡l[σ₂] .proj₁)
            , ok , PE.refl , l[σ₁]≡l[σ₂]
            )
      )

opaque

  -- Validity for Unit, seen as a term former.

  Unitᵗᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ l ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ sucᵘ l ⟩ Unit s l ∷ U l
  Unitᵗᵛ ⊩l ok =
    let ⊩ᵛᵘl = ⊩ᵛ∷Level⇔ .proj₁ ⊩l .proj₂ in
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩l
      , λ σ₁≡σ₂ →
          case ⊩ᵛᵘ→⊩ˢ≡∷→⊩[]≡[] ⊩ᵛᵘl σ₁≡σ₂ of λ
            l[σ₁]≡l[σ₂] →
          Type→⊩≡∷U⇔ Unitₙ Unitₙ .proj₂
            ( <-sucᵘ (wf-⊩Level l[σ₁]≡l[σ₂] .proj₁)
            , ⊩ᵛ⇔ .proj₁ (Unitᵛ ⊩l ok) .proj₂ σ₁≡σ₂
            , ≅ₜ-Unit-cong (escapeLevelEq l[σ₁]≡l[σ₂]) ok
            )
      )

------------------------------------------------------------------------
-- The constructor star

opaque

  -- Reducibility for star.

  ⊩star :
    Γ ⊩Level l ∷Level →
    Unit-allowed s →
    Γ ⊩⟨ l ⟩ star s l ∷ Unit s l
  ⊩star ⊩l ok =
    let ⊢l = escapeLevel ⊩l in
    ⊩∷Unit⇔ .proj₂
      ( ≤-reflᵘ ⊩l
      , ok
      , Unitₜ _ (id (starⱼ ⊢l ok)) (≅ₜ-starrefl ⊢l ok) (starᵣ (reflLevel ⊩l))
      )

{-
opaque

  -- Validity of star.

  starᵛ :
    ⊩ᵛ Γ →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ l ⟩ star s l ∷ Unit s l
  starᵛ {Γ} {s} {l} ⊩Γ ok =
    ⊩ᵛ∷⇔ .proj₂
      ( Unitᵛ ⊩Γ ok
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                         →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                                      →⟨ flip ⊩star ok ⟩
          Δ ⊩⟨ l ⟩ star s l ∷ Unit s l             →⟨ refl-⊩≡∷ ⟩
          Δ ⊩⟨ l ⟩ star s l ≡ star s l ∷ Unit s l  □
      )

------------------------------------------------------------------------
-- The typing rule η-unit

opaque

  -- Validity of η-unit.

  η-unitᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unit s l →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ Unit s l →
    Unit-with-η s →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ Unit s l
  η-unitᵛ ⊩t ⊩u η =
    ⊩ᵛ≡∷⇔ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊩σ₁ , ⊩σ₂) →
          case ⊩∷Unit⇔ .proj₁ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ₁) of λ
            (l≤l′ , ok , ⊩t@(Unitₜ _ t⇒*t′ _ _)) →
          case ⊩∷Unit⇔ .proj₁ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ₂) of λ
            (_ , _ , ⊩u@(Unitₜ _ u⇒*u′ _ _)) →
          ⊩≡∷Unit⇔ .proj₂
            (l≤l′ , ok , ⊩t , ⊩u ,
             Unitₜ₌ˢ (redFirst*Term t⇒*t′) (redFirst*Term u⇒*u′) η)
      )

------------------------------------------------------------------------
-- The eliminator unitrec

opaque

  -- Reducibility of equality between applications of unitrec.

  ⊩unitrec≡unitrec :
    Γ ∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ l ]₀ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ unitrec l p q A₁ t₁ u₁ [ σ₁ ] ≡
      unitrec l p q A₂ t₂ u₂ [ σ₂ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]
  ⊩unitrec≡unitrec
    {l} {l′} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {Δ} {σ₁} {σ₂} {p} {q}
    A₁≡A₂ t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩ᵛ≡∷⇔″ .proj₁ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case ⊩ᵛ∷⇔ .proj₁ ⊩t₁ .proj₁ of λ
      ⊩Unit →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₁ ⊩σ₁ of λ
      ⊩t₁[σ₁] →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂ of λ
      ⊩t₂[σ₂] →
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂ of λ
      A₁[σ₁⇑]≡A₂[σ₂⇑] →
    case Σ.map escape escape (wf-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑]) of λ
      (⊢A₁[σ₁⇑] , ⊢A₂[σ₂⇑]) →
    case refl-⊩≡∷ $
         ⊩star (escape-⊩ˢ∷ ⊩σ₁ .proj₁) $
         ⊩ᵛUnit→Unit-allowed ⊩Unit of λ
      ⋆≡⋆ →
    case PE.subst₂ (_⊢_≡_ _) (substConsId A₁) (substConsId A₂) $
         ≅-eq $ escape-⊩≡ $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] A₁≡A₂ σ₁≡σ₂ ⋆≡⋆ of λ
      A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] →
    case escape-⊩∷ $
         PE.subst (_⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ (starʷ _)) $
         ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁ of λ
      ⊢u₁[σ₁] →
    case escape-⊩∷ $
         conv-⊩∷
           (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ (refl-⊩ˢ≡∷ ⊩σ₂) ⋆≡⋆) $
         PE.subst (_⊩⟨_⟩_∷_ _ _ _) (singleSubstLift A₁ (starʷ _)) $
         ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂ of λ
      ⊢u₂[σ₂] →
    case ⊩≡∷Unit⇔ .proj₁ (t₁≡t₂ σ₁≡σ₂) of λ where
      (_ , ok , _ , _ , Unitₜ₌ˢ ⊢t₁ ⊢t₂ (inj₂ η)) →
        case starᵛ (wf-⊩ᵛ ⊩Unit) ok of λ
          ⊩⋆ →
        unitrec l p q A₁ t₁ u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $
                                                                     unitrec-β-η ⊢A₁[σ₁⇑] (escape-⊩∷ ⊩t₁[σ₁]) ⊢u₁[σ₁] ok η ⟩⊩∷∷
                                                                   ⟨ ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] (refl-⊩ᵛ≡ ⊩A₁)
                                                                       (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₁ ⊩⋆ (inj₂ η)) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₁)
                                                                       (refl-⊩ˢ≡∷ ⊩σ₁) ⟩⊩∷
        u₁ [ σ₁ ]                     ∷ A₁ [ starʷ l ]₀ [ σ₁ ]    ≡⟨ u₁≡u₂ σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                   ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                                      ∷ A₂ [ starʷ l ]₀ [ σ₂ ]     ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
        u₂ [ σ₂ ]                     ∷ A₂ [ σ₂ ⇑ ] [ starʷ l ]₀  ⇐⟨ conv (unitrec-β-η ⊢A₂[σ₂⇑] (escape-⊩∷ ⊩t₂[σ₂]) ⊢u₂[σ₂] ok η)
                                                                       (≅-eq $ escape-⊩≡ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂) $
                                                                        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (η-unitᵛ ⊩t₂ ⊩⋆ (inj₂ η)) $
                                                                        refl-⊩ˢ≡∷ ⊩σ₂)
                                                                   ⟩∎∷
        unitrec l p q A₂ t₂ u₂ [ σ₂ ]                             ∎

      (_ , ok , _ , _ ,
       Unitₜ₌ʷ t₁′ t₂′ t₁[σ₁]⇒*t₁′ t₂[σ₂]⇒*t₂′ _ rest no-η) →
        case PE.subst (_⊢_⇒*_∷_ _ _ _)
               (PE.sym $ singleSubstLift A₁ t₁) $
             unitrec-subst* {p = p} {q = q} t₁[σ₁]⇒*t₁′ ⊢A₁[σ₁⇑] ⊢u₁[σ₁]
               no-η of λ
          unitrec⇒*₁ →
        case PE.subst (_⊢_⇒*_∷_ _ _ _)
               (PE.sym $ singleSubstLift A₂ t₂) $
             unitrec-subst* {p = p} {q = q} t₂[σ₂]⇒*t₂′ ⊢A₂[σ₂⇑] ⊢u₂[σ₂]
               no-η of λ
          unitrec⇒*₂ →
        case PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
               (PE.sym $ singleSubstLift A₁ t₁) PE.refl $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁)
               (⊩∷-⇒* t₁[σ₁]⇒*t₁′ ⊩t₁[σ₁]) of λ
          A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ →
        case ≅-eq $ escape-⊩≡ $
             PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
               (PE.sym $ singleSubstLift A₂ t₂) PE.refl $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂)
               (⊩∷-⇒* t₂[σ₂]⇒*t₂′ ⊩t₂[σ₂]) of λ
          ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ →
        case rest of λ where
          starᵣ →
            unitrec l p q A₁ t₁        u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                               ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
            unitrec l p q A₁ (starʷ l) u₁ [ σ₁ ] ∷ A₁ [ σ₁ ⇑ ] [ starʷ l ]₀  ⇒⟨ unitrec-β ⊢A₁[σ₁⇑] ⊢u₁[σ₁] ok no-η ⟩⊩∷∷
                                                                             ˘⟨ singleSubstLift A₁ (starʷ _) ⟩⊩∷≡
            u₁ [ σ₁ ]                            ∷ A₁ [ starʷ l ]₀ [ σ₁ ]    ≡⟨ u₁≡u₂ σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                              ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                                                 ∷ A₂ [ starʷ l ]₀ [ σ₂ ]     ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
            u₂ [ σ₂ ]                            ∷ A₂ [ σ₂ ⇑ ] [ starʷ l ]₀  ⇐⟨ unitrec-β ⊢A₂[σ₂⇑] ⊢u₂[σ₂] ok no-η ⟩∷
                                                                             ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
            unitrec l p q A₂ (starʷ l) u₂ [ σ₂ ] ∷ A₂ [ t₂ ]₀ [ σ₂ ]         ⇐*⟨ unitrec⇒*₂ ⟩∎∷
            unitrec l p q A₂ t₂        u₂ [ σ₂ ]                             ∎

          (ne (neNfₜ₌ t₁′-ne t₂′-ne t₁′~t₂′)) →
            Δ ⊩⟨ l′ ⟩
              unitrec l p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ]) ≡
              unitrec l p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∷
              A₁ [ t₁ ]₀ [ σ₁ ] ∋
            (unitrec l p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ])
               ∷ A₁ [ t₁ ]₀ [ σ₁ ]                                ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                    ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
             unitrec l p q (A₁ [ σ₁ ⇑ ]) t₁′         (u₁ [ σ₁ ])
               ∷ A₁ [ σ₁ ⇑ ] [ t₁′ ]₀                             ≡⟨ neutral-⊩≡∷ (wf-⊩≡ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ .proj₂)
                                                                       (unitrecₙ no-η t₁′-ne) (unitrecₙ no-η t₂′-ne)
                                                                       (~-unitrec (escape-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑]) t₁′~t₂′
                                                                          (PE.subst (_⊢_≅_∷_ _ _ _) (singleSubstLift A₁ _) $
                                                                           escape-⊩≡∷ (u₁≡u₂ σ₁≡σ₂))
                                                                          ok no-η) ⟩⊩∷∷⇐*
                                                                    ⟨ ≅-eq $ escape-⊩≡ $
                                                                      ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
                                                                      neutral-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩Unit ⊩σ₁)
                                                                        t₁′-ne t₂′-ne t₁′~t₂′ ⟩⇒
               ∷ A₂ [ σ₂ ⇑ ] [ t₂′ ]₀                              ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒

             unitrec l p q (A₂ [ σ₂ ⇑ ]) t₂′         (u₂ [ σ₂ ])
               ∷ A₂ [ t₂ ]₀ [ σ₂ ]                                ⇐*⟨ unitrec⇒*₂ ⟩∎∷

             unitrec l p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ])  ∎)

opaque

  -- Validity of equality between applications of unitrec.

  unitrec-congᵛ :
    Γ ∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ l ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A₁ t₁ u₁ ≡ unitrec l p q A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec-congᵛ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , ⊩unitrec≡unitrec A₁≡A₂ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of unitrec.

  unitrecᵛ :
    Γ ∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ l ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A t u ∷ A [ t ]₀
  unitrecᵛ ⊩A ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    unitrec-congᵛ (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of the unitrec β rule.

  unitrec-βᵛ :
    Γ ∙ Unitʷ l ⊩ᵛ⟨ l″ ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ starʷ l ]₀ →
    ¬ Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A (starʷ l) t ≡ t ∷ A [ starʷ l ]₀
  unitrec-βᵛ {A} ⊩A ⊩t no-η =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β
           (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (⊩ᵛUnit→Unit-allowed (wf-∙-⊩ᵛ ⊩A .proj₂)) no-η)
      ⊩t

opaque

  -- Validity of the rule called unitrec-β-η.

  unitrec-β-ηᵛ :
    Γ ∙ Unitʷ l ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ l →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ l ]₀ →
    Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec l p q A t u ≡ u ∷ A [ t ]₀
  unitrec-β-ηᵛ {A = A} ⊩A ⊩t ⊩u η =
    case wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t) of λ
      ⊩Γ →
    case ⊩ᵛUnit→Unit-allowed (wf-∙-⊩ᵛ ⊩A .proj₂) of λ
      ok →
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β-η
           (escape $
            ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $
            ⊩ˢ∷-liftSubst (Unitᵛ ⊩Γ ok) ⊩σ)
           (escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ))
           ok η)
      (conv-⊩ᵛ∷
         (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩A) $
          η-unitᵛ (starᵛ ⊩Γ ok) ⊩t (inj₂ η))
         ⊩u)
-}
