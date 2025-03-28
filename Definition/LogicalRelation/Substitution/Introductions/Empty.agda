------------------------------------------------------------------------
-- Validity of the empty type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Empty
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Level R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product

private variable
  Γ Δ : Con Term _
  A B l t u : Term _
  ℓ : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_

  --  A characterisation lemma for _⊩⟨_⟩_.

  ⊩Empty⇔ :
    Γ ⊩⟨ l ⟩ Empty ⇔ Γ ⊩Level l ∷Level
  ⊩Empty⇔ =
      wfᵘ-⊩
    , λ ⊩l → ⊩l , Emptyᵣ (id (Emptyⱼ (wfTerm (escapeLevel ⊩l))))

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Empty⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Empty ⇔ (Γ ⊩Level l ∷Level × Γ ⊩Empty t ∷Empty)
  ⊩∷Empty⇔ =
      (λ ((⊩l , ⊩Empty′) , ⊩t) →
        case Empty-elim ⊩Empty′ of λ {
          (Emptyᵣ _) →
        ⊩l , ⊩t })
    , (λ (⊩l , ⊩t@(Emptyₜ n d n≡n prop)) →
        ⊩Empty⇔ .proj₂ ⊩l , ⊩t)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Empty≡⇔ : Γ ⊩⟨ l ⟩ Empty ≡ A ⇔ (Γ ⊩Level l ∷Level × Γ ⊩Empty Empty ≡ A)
  ⊩Empty≡⇔ =
      (λ ((⊩l , ⊩Empty) , _ , Empty≡A) →
        case Empty-elim ⊩Empty of λ {
          (Emptyᵣ _) →
        ⊩l , Empty≡A })
    , (λ (⊩l , Empty≡A) →
         case id (Emptyⱼ (wfEq (subset* Empty≡A))) of λ
           Empty⇒*Empty →
         let ⊩Empty = Emptyᵣ Empty⇒*Empty in
          (⊩l , ⊩Empty)
        , (⊩l , (redSubst* Empty≡A ⊩Empty) .proj₁)
        , Empty≡A)

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Empty⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Empty ⇔ (Γ ⊩Level l ∷Level × Γ ⊩Empty t ≡ u ∷Empty)
  ⊩≡∷Empty⇔ =
      (λ ((⊩l , ⊩Empty′) , _ , _ , t≡u) →
        case Empty-elim ⊩Empty′ of λ {
          (Emptyᵣ _) →
        ⊩l , t≡u })
    , λ (⊩l , t≡u@(Emptyₜ₌ _ _ t⇒*t′ u⇒*u′ t′≅u′ prop)) →
        case prop of λ where
          (ne (neNfₜ₌ t′-ne u′-ne t′~u′)) →
            let ≅t′ , ≅u′ = wf-⊢≅∷ t′≅u′
                ~t′ , ~u′ = wf-⊢~∷ t′~u′
            in
              ⊩Empty⇔ .proj₂ ⊩l
            , Emptyₜ _ t⇒*t′ ≅t′ (ne (neNfₜ t′-ne ~t′))
            , Emptyₜ _ u⇒*u′ ≅u′ (ne (neNfₜ u′-ne ~u′))
            , t≡u

------------------------------------------------------------------------
-- Empty

opaque

  -- Reducibility for Empty.

  ⊩Empty : Γ ⊩Level l ∷Level → Γ ⊩⟨ l ⟩ Empty
  ⊩Empty = ⊩Empty⇔ .proj₂

opaque

  -- Validity for Empty, seen as a type formerr.

  Emptyᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ zeroᵘ ⟩ Empty
  Emptyᵛ {Γ} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( zeroᵘᵛᵘ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          refl-⊩≡ (⊩Empty (⊩Levelzeroᵘ∷Level (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)))
      )

opaque

  -- Validity for Empty, seen as a term former.

  Emptyᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ sucᵘ zeroᵘ ⟩ Empty ∷ U zeroᵘ
  Emptyᵗᵛ ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ ⊩Γ)
      , λ σ₁≡σ₂ →
          case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊢Δ , _) →
          Type→⊩≡∷U⇔ Emptyₙ Emptyₙ .proj₂
            (zeroᵘ<oneᵘ ⊢Δ , refl-⊩≡ (⊩Empty (⊩Levelzeroᵘ∷Level ⊢Δ)) , ≅ₜ-Emptyrefl ⊢Δ)
      )
