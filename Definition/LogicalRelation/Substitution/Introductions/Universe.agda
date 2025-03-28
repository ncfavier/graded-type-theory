------------------------------------------------------------------------
-- Validity of the universe type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation.Hidden R {{eqrel}} as H
open import Definition.LogicalRelation.Irrelevance R {{eqrel}}
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R {{eqrel}}
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Level R {{eqrel}}

open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product as Σ
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    n            : Nat
    Γ            : Con Term n
    A B l l′ t u : Term n
    k            : LogRelKit
    ℓ            : Universe-level

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

  U⇒*U→≡ : Γ ⊢ U l ⇒* U l′ → l PE.≡ l′
  U⇒*U→≡ {Γ} {l} {l′} =
    Γ ⊢ U l ⇒* U l′  →⟨ flip whnfRed* Uₙ ⟩
    U l PE.≡ U l′    →⟨ (λ { PE.refl → PE.refl }) ⟩
    l PE.≡ l′        □

opaque
  unfolding _⊩⟨_⟩_ _⊩_<_∷Level

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U t ⇔
    Γ ⊩ t < l ∷Level
  ⊩U⇔ =
      (λ (⊩l , ⊩Ut) →
        case U-elim ⊩Ut of λ {
          (Uᵣ (Uᵣ l′ [l′] l′< U⇒*U)) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
        [l′] , ⊩l , l′< }})
    , λ ([t] , [l] , t<l) →
        [l] , Uᵣ′ _ [t] t<l (id (Uⱼ (escapeLevel [t])))

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩_<_∷Level

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    (Γ ⊩ t < l ∷Level × Γ ⊩⟨ t ⟩ A ×
    ∃ λ B → Γ ⊢ A ⇒* B ∷ U t × Type B × Γ ⊢≅ B ∷ U t)
  ⊩∷U⇔ =
      (λ ((⊩l , ⊩U) , ⊩A) →
        case U-elim ⊩U of λ {
          (Uᵣ (Uᵣ k [k] k< U⇒*U)) →
        case ⊩A of λ
          (Uₜ _ A⇒*B B-type B≅B ⊩A) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
          ([k] , ⊩l , k<)
        , ⊩-intro-< k< ⊩A , _ , A⇒*B , B-type , B≅B }})
    , (λ (([t] , [l] , t<l) , ⊩A , _ , A⇒*B , B-type , B≅B) →
          ([l] , Uᵣ′ _ [t] t<l (id (Uⱼ (escapeLevel [t]))))
          , Uₜ _ A⇒*B B-type B≅B (⊩→⊩< t<l ⊩A))

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    (Γ ⊩ t < l ∷Level × (Γ ⊩⟨ t ⟩ A) ×
    Γ ⊢≅ A ∷ U t)
  Type→⊩∷U⇔ {A} {Γ} {l} {t} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U t                                        ⇔⟨ ⊩∷U⇔ ⟩
    (Γ ⊩ t < l ∷Level × Γ ⊩⟨ t ⟩ A ×
     ∃ λ B → Γ ⊢ A ⇒* B ∷ U t × Type B × Γ ⊢≅ B ∷ U t) ⇔⟨
      id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
        ((λ (_ , A⇒*B , _ , B≅B) → case whnfRed*Term A⇒*B (typeWhnf A-type) of λ where
          PE.refl → B≅B)
        , λ A≅A → _ , id (wf-⊢≡∷ (≅ₜ-eq A≅A) .proj₂ .proj₁) , A-type , A≅A) ⟩
    (Γ ⊩ t < l ∷Level × (Γ ⊩⟨ t ⟩ A) × Γ ⊢≅ A ∷ U t) □⇔

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩_<_∷Level

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    Γ ⊩⟨ l ⟩ U t ≡ A ⇔
    (Γ ⊩ t < l ∷Level ×
    ∃ λ u → Γ ⊢ A ⇒* U u × Γ ⊩Level t ≡ u ∷Level × Γ ⊩⟨ l ⟩ A)
  ⊩U≡⇔ {Γ} {t} {A} =
      (λ ((⊩l , ⊩U) , ⊩A , U≡A) →
        case U-elim ⊩U of λ {
          (Uᵣ (Uᵣ k [k] k< U⇒*U)) →
        case U≡A of λ
          (U₌ k′ D k≡k′) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
        ([k] , ⊩l , k<) , k′ , D , k≡k′ , ⊩A }})
      , λ (([t] , [l] , t<l) , u , A⇒*U , t≡u , ⊩A) →
        ([l] , Uᵣ′ _ [t] t<l (id (Uⱼ (escapeLevel [t]))))
        , ⊩A
        , U₌ u A⇒*U t≡u

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_ _⊩_<_∷Level

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    (Γ ⊩ t < l ∷Level × Γ ⊩⟨ t ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U t ×
     Γ ⊢ B ⇒* B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t)
  ⊩≡∷U⇔ {Γ} {A} {B} {t} =
      (λ ((⊩l , ⊩U) , _ , _ , A≡B) →
        case U-elim ⊩U of λ {
          (Uᵣ (Uᵣ k [k] k< U⇒*U)) →
        case A≡B of λ
          (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
          ([k] , ⊩l , k<)
        , ⊩≡-intro-< k< ⊩A ⊩B A≡B
        , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′ }})
    , (λ (([t] , [l] , t<l) , A≡B@(⊩A , ⊩B , _) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
         let ⊩A< = ⊩→⊩< t<l ⊩A
             ⊩B< = ⊩→⊩< t<l ⊩B
             A≡B< = ⊩≡→⊩<≡/ t<l ⊩A< A≡B
             ≅A′ , ≅B′ = wf-⊢≅∷ A′≅B′
         in
           ([l] , Uᵣ′ _ [t] t<l (id (Uⱼ (escapeLevel [t]))))
         , Uₜ _ A⇒*A′ A′-type ≅A′ ⊩A<
         , Uₜ _ B⇒*B′ B′-type ≅B′ ⊩B<
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A< ⊩B< A≡B<
      )

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    (Γ ⊩ t < l ∷Level × (Γ ⊩⟨ t ⟩ A ≡ B) ×
     Γ ⊢ A ≅ B ∷ U t)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {t} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t          ⇔⟨ ⊩≡∷U⇔ ⟩
    (Γ ⊩ t < l ∷Level × Γ ⊩⟨ t ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U t ×
     Γ ⊢ B ⇒* B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t)
      ⇔⟨ id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
        ( (λ (A′ , B′ , A⇒*A′ , B⇒*B′ , _ , _ , A′≅B′) →
          case whnfRed*Term A⇒*A′ (typeWhnf A-type) of λ {
            PE.refl →
          case whnfRed*Term B⇒*B′ (typeWhnf B-type) of λ {
            PE.refl →
          A′≅B′ } })
        , λ A≅B →
          let _ , ⊢A , ⊢B = wf-⊢≡∷ (≅ₜ-eq A≅B)
          in
          _ , _ , id ⊢A , id ⊢B , A-type , B-type , A≅B) ⟩
    (Γ ⊩ t < l ∷Level × (Γ ⊩⟨ t ⟩ A ≡ B) ×
     Γ ⊢ A ≅ B ∷ U t) □⇔

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level → Γ ⊩ᵛ⟨ sucᵘ t ⟩ U t
  ⊩ᵛU {Γ} {t} ⊩t =
    ⊩ᵛ⇔ .proj₂
      ( sucᵘᵛᵘ (⊩ᵛ∷Level⇔ .proj₁ ⊩t .proj₂)
      , λ {_} {Δ} {σ₁} {σ₂} →
          λ σ₁≡σ₂ →
            let (_ , ⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
                ⊢Δ = escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁
            in
            ⊩U≡⇔ .proj₂ $
                <-sucᵘ ⊩t[σ₁]
              , t [ σ₂ ]
              , id (Uⱼ (escapeLevel ⊩t[σ₂]))
              , ⊩t≡
              , ⊩U⇔ .proj₂ (≡-<-Level (symLevel ⊩t≡) (<-sucᵘ ⊩t[σ₁]))
      )

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level → Γ ⊩ᵛ⟨ sucᵘ (sucᵘ t) ⟩ U t ∷ U (sucᵘ t)
  ⊩ᵛU∷U {Γ} {t} ⊩t =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU (sucᵘᵛ ⊩t)
      , λ {_} {Δ} {σ₁} {σ₂} σ₁≡σ₂ →
          let ⊩t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂
              (_ , ⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ ⊩t[σ₁]≡t[σ₂]
          in
            Type→⊩≡∷U⇔ Uₙ Uₙ .proj₂ $
              <-sucᵘ (⊩Levelsucᵘ∷Level ⊩t[σ₁])
            , ⊩ᵛ⇔ .proj₁ (⊩ᵛU ⊩t) .proj₂ σ₁≡σ₂
            , ≅ₜ-U-cong (escapeLevelEq ⊩t≡)
      )

opaque

  -- An inversion lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛU→⊩ᵛᵘ : Γ ⊩ᵛ⟨ l ⟩ U t → Γ ⊩ᵛᵘ t
  ⊩ᵛU→⊩ᵛᵘ ⊩U =
    ⊩ᵛᵘ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
          case ⊩U≡⇔ .proj₁ (⊩ᵛ⇔ .proj₁ ⊩U .proj₂ σ₁≡σ₂) of λ
            (_ , _ , D , t[σ₁]≡t[σ₂] , _) →
          case U⇒*U→≡ D of λ where
            PE.refl → t[σ₁]≡t[σ₂]
      )

opaque
  unfolding _⊩ᵛᵘ_<_

  -- Another inversion lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛU→⊩ᵛᵘ< : Γ ⊩ᵛ⟨ l ⟩ U t → Γ ⊩ᵛᵘ t < l
  ⊩ᵛU→⊩ᵛᵘ< ⊩U =
      ⊩ᵛU→⊩ᵛᵘ ⊩U
    , wfᵘ-⊩ᵛ ⊩U
    , ⊩U⇔ .proj₁ ∘→ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩U

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U t →
    Γ ⊩ᵛ⟨ t ⟩ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛU→⊩ᵛᵘ ⊩U
      , λ σ₁≡σ₂ →
        let (_ , A≡A , _) = ⊩≡∷U⇔ .proj₁ (A≡A∷U σ₁≡σ₂) in
        A≡A
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ∷ U t →
    Γ ⊩ᵛ⟨ t ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩ᵛU→⊩ᵛᵘ ⊩U
      , λ σ₁≡σ₂ →
        let (_ , A≡B , _) = ⊩≡∷U⇔ .proj₁ (A≡B∷U σ₁≡σ₂) in
        A≡B
      )
