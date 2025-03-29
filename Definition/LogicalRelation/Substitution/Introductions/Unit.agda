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
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Level R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Unary R

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    n : Nat
    Γ Δ : Con Term n
    σ σ₁ σ₂ : Subst _ _
    s s₁ s₂ : Strength
    l l′ l″ l‴ l₁ l₂ : Universe-level
    A A₁ A₂ k k′ t t₁ t₂ u u₁ u₂ : Term n
    p q : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding emb-⊩

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s k ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s)
  ⊩Unit⇔ =
      (λ ⊩Unit →
        case Unit-view ⊩Unit of λ {
          (Unitᵣ (Unitᵣ k [k] k≤ Unit⇒*Unit ok)) →
      case Unit-PE-injectivity $
           whnfRed* Unit⇒*Unit Unitₙ of λ {
        (_ , PE.refl) →
      [k] , k≤ , ok }})
    , (λ ([k] , k≤ , ok) →
         Unitᵣ′ _ [k] k≤ (id (Unitⱼ (escapeLevel [k]) ok)) ok)

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡⇔ :
    Γ ⊩⟨ l ⟩ Unit s k ≡ A ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s × Γ ⊩Unit⟨ s ⟩ Unit s k ≡ A / k)
  ⊩Unit≡⇔ {l} {s} {k} {A} =
      (λ (⊩Unit , _ , Unit≡A) →
         case Unit-view ⊩Unit of λ {
           (Unitᵣ (Unitᵣ k [k] k≤ Unit⇒*Unit ok)) →
         case Unit-PE-injectivity $
              whnfRed* Unit⇒*Unit Unitₙ of λ {
           (_ , PE.refl) →
        [k] , k≤ , ok , Unit≡A }})
    , (λ ([k] , k≤ , ok , Unit₌ k′ A⇒*Unit k≡k′) →
         let [k′] = wf-⊩Level k≡k′ .proj₂
             ⊢Unitk = Unitⱼ (escapeLevel [k]) ok
             ⊢Unitk′ = Unitⱼ (escapeLevel [k′]) ok
             Unitk≡Unitk′
               = Unitᵣ′ _ [k] k≤ (id ⊢Unitk) ok
               , Unitᵣ′ _ [k′] (PE.subst (_≤ᵘ l) (↑ᵘ-cong [k] [k′] k≡k′) k≤) (id ⊢Unitk′) ok
               , Unit₌ _ (id ⊢Unitk′) k≡k′
         in sym-⊩≡
           (A         ⇒*⟨ A⇒*Unit ⟩⊩
            Unit s k′ ≡⟨ sym-⊩≡ Unitk≡Unitk′ ⟩⊩
            Unit s k  ∎⟨ ⊩Unit⇔ .proj₂ ([k] , k≤ , ok) ⟩⊩))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Unit≡Unit⇔ :
    Γ ⊩⟨ l ⟩ Unit s₁ k ≡ Unit s₂ k′ ⇔
    (∃ λ (k≡k′ : Γ ⊩Level k ≡ k′ ∷Level) → ↑ᵘ k≡k′ ≤ᵘ l × Unit-allowed s₁ × s₁ PE.≡ s₂)
  ⊩Unit≡Unit⇔ {Γ} {l} {s₁} {k} {s₂} {k′} =
    Γ ⊩⟨ l ⟩ Unit s₁ k ≡ Unit s₂ k′  ⇔⟨ ⊩Unit≡⇔ ⟩
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s₁ × Γ ⊩Unit⟨ s₁ ⟩ Unit s₁ k ≡ Unit s₂ k′ / k)
      ⇔⟨ ((λ { ([k] , k≤ , ok , Unit₌ _ Unit⇒*Unit k≡k′) →
            case Unit-PE-injectivity $ whnfRed* Unit⇒*Unit Unitₙ of λ {
              (PE.refl , PE.refl) →
            k≡k′ , PE.subst (_≤ᵘ l) (↑ᵘ-irrelevance [k] k≡k′) k≤ , ok , PE.refl }})
        , λ { (k≡k′ , k≤ , ok , PE.refl) →
              wf-⊩Level k≡k′ .proj₁
            , PE.subst (_≤ᵘ l) (↑ᵘ-irrelevance k≡k′ _) k≤
            , ok
            , Unit₌ _ (id (Unitⱼ (escapeLevel (wf-⊩Level k≡k′ .proj₂)) ok)) k≡k′ }) ⟩
    (∃ λ (k≡k′ : Γ ⊩Level k ≡ k′ ∷Level) → ↑ᵘ k≡k′ ≤ᵘ l × Unit-allowed s₁ × s₁ PE.≡ s₂)       □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Unit⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Unit s k ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit/ k)
  ⊩≡∷Unit⇔ {s} =
      (λ (⊩Unit , t≡u) →
         case Unit-view ⊩Unit of λ {
            (Unitᵣ (Unitᵣ k [k] k≤ Unit⇒*Unit ok)) →
         case Unit-PE-injectivity $
              whnfRed* Unit⇒*Unit Unitₙ of λ {
           (_ , PE.refl) →
         [k] , k≤ , ok , t≡u }})
    , (λ ([k] , k≤ , ok , t≡u) →
        ⊩Unit⇔ .proj₂ ([k] , k≤ , ok) , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Unit⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Unit s k ⇔
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷Unit/ k)
  ⊩∷Unit⇔ {Γ} {l} {t} {s} {k} =
    Γ ⊩⟨ l ⟩ t ∷ Unit s k                                                                         ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Unit s k                                                                     ⇔⟨ ⊩≡∷Unit⇔ ⟩
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ≡ t ∷Unit/ k)  ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ⊩Unit∷Unit⇔⊩Unit≡∷Unit) ⟩
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s × Γ ⊩Unit⟨ s ⟩ t ∷Unit/ k)      □⇔

------------------------------------------------------------------------
-- Unit

opaque

  -- If the type Unit s l is valid, then it is allowed (given a
  -- certain assumption).

  ⊩ᵛUnit→Unit-allowed :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ Unit s k →
    Unit-allowed s
  ⊩ᵛUnit→Unit-allowed {Γ} {l} {s} {k} =
    Γ ⊩ᵛ⟨ l ⟩ Unit s k                                              →⟨ R.⊩→ ∘→ ⊩ᵛ→⊩ ⟩
    Γ ⊩⟨ l ⟩ Unit s k                                               ⇔⟨ ⊩Unit⇔ ⟩→
    (∃ λ ([k] : Γ ⊩Level k ∷Level) → ↑ᵘ [k] ≤ᵘ l × Unit-allowed s)  →⟨ proj₂ ∘→ proj₂ ⟩
    Unit-allowed s                                                  □

opaque

  -- Reducibility for Unit.

  ⊩Unit :
    ([k] : Γ ⊩Level k ∷Level) →
    Unit-allowed s →
    Γ ⊩⟨ ↑ᵘ [k] ⟩ Unit s k
  ⊩Unit [k] ok = ⊩Unit⇔ .proj₂ ([k] , ≤ᵘ-refl , ok)

opaque

  -- Validity for equality preservation for Unit, seen as a term former.

  Unit-congᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k ≡ Unit s k′ ∷ U k
  Unit-congᵗᵛ k≡k′ ok =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (wf-⊩ᵛ≡∷ k≡k′ .proj₁)
      , λ σ₁≡σ₂ →
          let k[σ₁]≡k′[σ₂] = ⊩≡∷Level⇔ .proj₁ (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ k≡k′ σ₁≡σ₂)
              ⊩k[σ₁] , ⊩k[σ₂] = wf-⊩Level k[σ₁]≡k′[σ₂]
          in Type→⊩≡∷U⇔ Unitₙ Unitₙ .proj₂
            ( ⊩k[σ₁]
            , <ᵘ-ωᵘ
            , ⊩Unit≡Unit⇔ .proj₂
              ( k[σ₁]≡k′[σ₂]
              , PE.subst (↑ᵘ k[σ₁]≡k′[σ₂] ≤ᵘ_) (↑ᵘ-irrelevance k[σ₁]≡k′[σ₂] ⊩k[σ₁]) ≤ᵘ-refl
              , ok
              , PE.refl
              )
            , ≅ₜ-Unit-cong (escapeLevelEq k[σ₁]≡k′[σ₂]) ok
            )
      )

opaque

  -- Validity for equality preservation for Unit, seen as a type former.

  Unit-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k ≡ Unit s k′
  Unit-congᵛ k≡k′ ok = ⊩ᵛ≡∷U→⊩ᵛ≡ (Unit-congᵗᵛ k≡k′ ok)

opaque

  -- Validity for Unit, seen as a type former.

  Unitᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k
  Unitᵛ ⊩k ok = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (Unit-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩k) ok)

opaque

  -- Validity for Unit, seen as a term former.

  Unitᵗᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ Unit s k ∷ U k
  Unitᵗᵛ ⊩k ok = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (Unit-congᵗᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩k) ok)

------------------------------------------------------------------------
-- The constructor star

opaque

  -- Reducibility for star.

  ⊩star :
    (⊩k : Γ ⊩Level k ∷Level) →
    Unit-allowed s →
    Γ ⊩⟨ ↑ᵘ ⊩k ⟩ star s k ∷ Unit s k
  ⊩star ⊩k ok =
    ⊩∷Unit⇔ .proj₂
      ( ⊩k
      , ≤ᵘ-refl
      , ok
      , Unitₜ _ (id (starⱼ (escapeLevel ⊩k) ok) , starₙ) (Unit-prop′→Unit-prop (starᵣ ⊩k))
      )

opaque

  -- Validity of equality preservation for star.

  star-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ star s k ≡ star s k′ ∷ Unit s k
  star-congᵛ {Γ} {l} {k} {k′} {s} k≡k′ ok =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Unitᵛ (wf-⊩ᵛ≡∷ k≡k′ .proj₁) ok
      , λ σ₁≡σ₂ →
          let k[σ₁]≡k′[σ₂] = ⊩≡∷Level⇔ .proj₁ (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ k≡k′ σ₁≡σ₂)
              ⊩k[σ₁] , ⊩k[σ₂] = wf-⊩Level k[σ₁]≡k′[σ₂]
          in ⊩≡∷Unit⇔ .proj₂
            ( ⊩k[σ₁]
            , ≤ᵘ-ωᵘ
            , ok
            , Unitₜ₌ _ _
                (id (starⱼ (escapeLevel ⊩k[σ₁]) ok) , starₙ)
                (id (conv (starⱼ (escapeLevel ⊩k[σ₂]) ok) (≅-eq (≅-sym (≅-Unit-cong (escapeLevelEq k[σ₁]≡k′[σ₂]) ok)))) , starₙ)
                (case Unit-with-η? s of λ {
                  (inj₁ η) → Unitₜ₌ˢ η ;
                  (inj₂ (PE.refl , ¬η)) → Unitₜ₌ʷ (starᵣ ⊩k[σ₁] k[σ₁]≡k′[σ₂]) ¬η })
            )
      )

opaque

  -- Validity of star.

  starᵛ :
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Unit-allowed s →
    Γ ⊩ᵛ⟨ ωᵘ ⟩ star s k ∷ Unit s k
  starᵛ ⊩k ok = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (star-congᵛ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ ⊩k) ok)

------------------------------------------------------------------------
-- The typing rule η-unit

opaque

  -- Validity of η-unit.

  η-unitᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Unit s k →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ Unit s k →
    Unit-with-η s →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ Unit s k
  η-unitᵛ ⊩t ⊩u η =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , λ σ₁≡σ₂ →
          let ⊩σ₁ , ⊩σ₂ = wf-⊩ˢ≡∷ σ₁≡σ₂
              [k] , k≤ , ok , Unitₜ _ t[σ₁]↘t′ _ =
                ⊩∷Unit⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ₁
              _ , _ , _ , Unitₜ _ u[σ₂]↘u′ _ =
                ⊩∷Unit⇔ .proj₁ $ R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ₂
              k[σ₁]≡k[σ₂] = proj₁ $ ⊩Unit≡Unit⇔ .proj₁ $ R.⊩≡→ $
                ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (⊩ᵛ⇔⊩ᵛ≡ .proj₁ (wf-⊩ᵛ∷ ⊩t)) σ₁≡σ₂
          in
          ⊩≡∷Unit⇔ .proj₂
            ([k] , k≤ , ok ,
             Unitₜ₌ _ _ t[σ₁]↘t′
              (conv↘∷ u[σ₂]↘u′ (≅-eq (≅-sym (≅-Unit-cong (escapeLevelEq k[σ₁]≡k[σ₂]) ok))))
              (Unitₜ₌ˢ η))
      )

------------------------------------------------------------------------
-- The eliminator unitrec

opaque


  ⊩unitrec≡unitrec′ :
    Γ ∙ Unitʷ k ⊢ A₁ ≡ A₂ →
    Γ ⊩Level k ≡ k′ ∷Level →
    Γ ∙ Unitʷ k R.⊩⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ k →
    Γ ⊩⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ k ]₀ →
    Γ ⊩⟨ l′ ⟩ unitrec p q k A₁ t₁ u₁ ≡ unitrec p q k′ A₂ t₂ u₂ ∷ A₁ [ t₁ ]₀
  ⊩unitrec≡unitrec′ {k} {A₁} {A₂} {k′} {t₁} {t₂} {u₁} {u₂} {p} {q} ⊢A₁≡A₂ k≡k′ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case ⊩≡∷Unit⇔ .proj₁ t₁≡t₂ of λ {
      ([k] , k≤ , ok , Unitₜ₌ _ _ _ _ prop) →
    case prop of λ {
      (Unitₜ₌ˢ η) →
        unitrec p q k A₁ t₁ u₁ ∷ A₁ [ t₁ ]₀        ⇒⟨ unitrec-β-η (escapeLevel [k]) (wf-⊢≡ ⊢A₁≡A₂ .proj₁) (escape-⊩∷ (wf-⊩≡∷ t₁≡t₂ .proj₁)) (escape-⊩∷ (wf-⊩≡∷ u₁≡u₂ .proj₁)) ok (Unit-with-η-𝕨→Unitʷ-η η) ⟩⊩∷∷
                                                                   ⟨ {! η-unitᵛ  !} ⟩⊩∷
        u₁                      ∷ A₁ [ starʷ k ]₀    ≡⟨ u₁≡u₂ ⟩⊩∷∷⇐*
                                                                   ⟨ substTypeEq ⊢A₁≡A₂ (star-cong (≅ₜ-eq (escapeLevelEq k≡k′)) ok) ⟩⇒
        u₂                     ∷ A₂ [ starʷ k′ ]₀  ⇐⟨ conv (unitrec-β-η (escapeLevel (wf-⊩Level k≡k′ .proj₂)) {! wf-⊢≡ ⊢A₁≡A₂ .proj₂  !} {!   !} {!   !} ok (Unit-with-η-𝕨→Unitʷ-η η)) {!   !} ⟩∎∷
        unitrec p q k′ A₂ t₂ u₂                            ∎
        ;
      (Unitₜ₌ʷ rest no-η) → {! x  !} }}

opaque

  -- Reducibility of equality between applications of unitrec.

  ⊩unitrec≡unitrec :
    Γ ∙ Unitʷ k ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ k →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ k ]₀ →
    ⦃ inc : Neutrals-included or-empty Δ ⦄ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ unitrec p q k A₁ t₁ u₁ [ σ₁ ] ≡
      unitrec p q k′ A₂ t₂ u₂ [ σ₂ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]
  ⊩unitrec≡unitrec {A₁} ⊢A₁≡A₂ k≡k′ A₁≡A₂ t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    case ⊩ᵛ≡∷⇔″ .proj₁ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    case ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ k≡k′ σ₁≡σ₂ of λ
      k[σ₁]≡k′[σ₂] →
    case ⊩≡∷Level⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁ $ wf-⊩ᵛ≡∷ k≡k′ .proj₁) σ₁≡σ₂ of λ
      k[σ₁]≡k[σ₂] →
    case wf-⊩Level k[σ₁]≡k′[σ₂] of λ
      (⊩k[σ₁] , ⊩k′[σ₂]) →
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂ of λ
      A₁[σ₁⇑]≡A₂[σ₂⇑] →
    case ⊩≡∷Unit⇔ .proj₁ (R.⊩≡∷⇔ .proj₁ (t₁≡t₂ σ₁≡σ₂)) of λ {
      (_ , _ , ok ,
       Unitₜ₌ t₁′ t₂′ (t₁[σ₁]⇒*t₁′ , _) (t₂[σ₂]⇒*t₂′ , _) prop) →
    case subst-⊢≡ ⊢A₁≡A₂ $
         ⊢ˢʷ≡∷-⇑ (Unit-cong (≅ₜ-eq (escapeLevelEq k[σ₁]≡k[σ₂])) ok) $ escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ of λ
      ⊢A₁[]≡A₂[] →
    PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
      ⊩unitrec≡unitrec′ ⊢A₁[]≡A₂[] k[σ₁]≡k′[σ₂] A₁[σ₁⇑]≡A₂[σ₂⇑]
        (R.⊩≡∷→ $ t₁≡t₂ σ₁≡σ₂)
        (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift A₁ (star _ _)) $ R.⊩≡∷→ $ u₁≡u₂ σ₁≡σ₂) }
    {-
    case prop of λ where
      (Unitₜ₌ˢ η)  →
        case starᵛ (wf-⊩ᵛ≡∷ k≡k′ .proj₁) ok of λ
          ⊩⋆ →
        unitrec p q k A₁ t₁ u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ t₁) $ unitrec-β-η ⊢k[σ₁] ⊢A₁[σ₁⇑] (R.escape-⊩∷ ⊩t₁[σ₁]) {!   !} ok (Unit-with-η-𝕨→Unitʷ-η η) ⟩⊩∷∷
                                                                   ⟨ {!   !} ⟩⊩∷
        u₁ [ σ₁ ]                     ∷ A₁ [ starʷ k ]₀ [ σ₁ ]    ≡⟨ {!   !} ⟩⊩∷∷⇐*
                                                                   ⟨ {!   !} ⟩⇒
                                      ∷ A₂ [ starʷ k′ ]₀ [ σ₂ ]     ⟨ {!   !} ⟩⇐≡
        u₂ [ σ₂ ]                     ∷ A₂ [ σ₂ ⇑ ] [ starʷ (k′ [ σ₂ ]) ]₀  ⇐⟨ {!   !} ⟩∎∷
        unitrec p q k′ A₂ t₂ u₂ [ σ₂ ]                             ∎

      (Unitₜ₌ʷ rest no-η) →
        {!   !}
        {-
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
             R.⊩≡→ $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁)
               (R.→⊩≡∷ $ ⊩∷-⇒* t₁[σ₁]⇒*t₁′ $ R.⊩∷→ ⊩t₁[σ₁]) of λ
          A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ →
        case ≅-eq $ escape-⊩≡ $
             PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
               (PE.sym $ singleSubstLift A₂ t₂) PE.refl $
             R.⊩≡→ $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂)
               (R.→⊩≡∷ $ ⊩∷-⇒* t₂[σ₂]⇒*t₂′ $ R.⊩∷→ ⊩t₂[σ₂]) of λ
          ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ →
        case rest of λ where
          starᵣ →
            unitrec l p q A₁ t₁        u₁ [ σ₁ ] ∷ A₁ [ t₁ ]₀ [ σ₁ ]         ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                               ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
            unitrec l p q A₁ (starʷ l) u₁ [ σ₁ ] ∷ A₁ [ σ₁ ⇑ ] [ starʷ l ]₀  ⇒⟨ unitrec-β ⊢A₁[σ₁⇑] ⊢u₁[σ₁] ok no-η ⟩⊩∷∷
                                                                             ˘⟨ singleSubstLift A₁ (starʷ _) ⟩⊩∷≡
            u₁ [ σ₁ ]                            ∷ A₁ [ starʷ l ]₀ [ σ₁ ]    ≡⟨ R.⊩≡∷→ $ u₁≡u₂ σ₁≡σ₂ ⟩⊩∷∷⇐*
                                                                              ⟨ A₁[⋆]₀[σ₁]≡A₂[⋆]₀[σ₂] ⟩⇒
                                                 ∷ A₂ [ starʷ l ]₀ [ σ₂ ]     ⟨ singleSubstLift A₂ (starʷ _) ⟩⇐≡
            u₂ [ σ₂ ]                            ∷ A₂ [ σ₂ ⇑ ] [ starʷ l ]₀  ⇐⟨ unitrec-β ⊢A₂[σ₂⇑] ⊢u₂[σ₂] ok no-η ⟩∷
                                                                             ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒
            unitrec l p q A₂ (starʷ l) u₂ [ σ₂ ] ∷ A₂ [ t₂ ]₀ [ σ₂ ]         ⇐*⟨ unitrec⇒*₂ ⟩∎∷
            unitrec l p q A₂ t₂        u₂ [ σ₂ ]                             ∎

          (ne (neNfₜ₌ inc t₁′-ne t₂′-ne t₁′~t₂′)) →
            Δ ⊩⟨ l′ ⟩
              unitrec l p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ]) ≡
              unitrec l p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ]) ∷
              A₁ [ t₁ ]₀ [ σ₁ ] ∋
            (unitrec l p q (A₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ]) (u₁ [ σ₁ ])
               ∷ A₁ [ t₁ ]₀ [ σ₁ ]                                ⇒*⟨ unitrec⇒*₁ ⟩⊩∷∷
                                                                    ⟨ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ ⟩⊩∷
             unitrec l p q (A₁ [ σ₁ ⇑ ]) t₁′         (u₁ [ σ₁ ])
               ∷ A₁ [ σ₁ ⇑ ] [ t₁′ ]₀                             ≡⟨ neutral-⊩≡∷ inc (wf-⊩≡ A₁[t₁]₀[σ₁]≡A₁[σ₁⇑][t₁′]₀ .proj₂)
                                                                       (unitrecₙ no-η t₁′-ne) (unitrecₙ no-η t₂′-ne)
                                                                       (~-unitrec
                                                                          (escape-⊩≡ $
                                                                           R.⊩≡→ ⦃ inc = included ⦃ inc = inc ⦄ ⦄ A₁[σ₁⇑]≡A₂[σ₂⇑])
                                                                          t₁′~t₂′
                                                                          (PE.subst (_⊢_≅_∷_ _ _ _) (singleSubstLift A₁ _) $
                                                                           escape-⊩≡∷ (R.⊩≡∷→ $ u₁≡u₂ σ₁≡σ₂))
                                                                          ok no-η) ⟩⊩∷∷⇐*
                                                                    ⟨ ≅-eq $ escape-⊩≡ $ R.⊩≡→ $
                                                                      ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $ R.→⊩≡∷ $
                                                                      neutral-⊩≡∷ inc (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩Unit ⊩σ₁)
                                                                        t₁′-ne t₂′-ne t₁′~t₂′ ⟩⇒
               ∷ A₂ [ σ₂ ⇑ ] [ t₂′ ]₀                              ˘⟨ ⊢A₂[t₂]₀[σ₂]≡A₂[σ₂⇑][t₂′]₀ ⟩⇒

             unitrec l p q (A₂ [ σ₂ ⇑ ]) t₂′         (u₂ [ σ₂ ])
               ∷ A₂ [ t₂ ]₀ [ σ₂ ]                                ⇐*⟨ unitrec⇒*₂ ⟩∎∷

             unitrec l p q (A₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ]) (u₂ [ σ₂ ])  ∎) -}}
             -}

opaque

  -- Validity of equality between applications of unitrec.

  unitrec-congᵛ :
    Γ ∙ Unitʷ k ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l ⟩ k ≡ k′ ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ Unitʷ k →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ A₁ [ starʷ k ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A₁ t₁ u₁ ≡ unitrec p q k′ A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec-congᵛ ⊢A₁≡A₂ k≡k′ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , ⊩unitrec≡unitrec ⊢A₁≡A₂ k≡k′ A₁≡A₂ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of unitrec.

  unitrecᵛ :
    Γ ∙ Unitʷ k ⊢ A →
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ k →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ k ]₀ →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A t u ∷ A [ t ]₀
  unitrecᵛ ⊢A ⊩k ⊩A ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    unitrec-congᵛ (refl ⊢A) (refl-⊩ᵛ≡∷ ⊩k) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of the unitrec β rule.

  unitrec-βᵛ :
    Γ ∙ Unitʷ k ⊢ A →
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l″ ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ starʷ k ]₀ →
    ¬ Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A (starʷ k) t ≡ t ∷ A [ starʷ k ]₀
  unitrec-βᵛ {A} ⊢A ⊩k ⊩A ⊩t no-η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A) in
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩k ⊩σ)
           (subst-⊢ ⊢A (⊢ˢʷ∷-⇑′ ⊢Unit (escape-⊩ˢ∷ ⊩σ .proj₂)))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (inversion-Unit-allowed ⊢Unit) no-η)
      ⊩t

opaque

  -- Validity of the rule called unitrec-β-η.

  unitrec-β-ηᵛ :
    Γ ∙ Unitʷ k ⊢ A →
    Γ ⊩ᵛ⟨ l ⟩ k ∷ Level →
    Γ ∙ Unitʷ k ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ Unitʷ k →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ A [ starʷ k ]₀ →
    Unitʷ-η →
    Γ ⊩ᵛ⟨ l′ ⟩ unitrec p q k A t u ≡ u ∷ A [ t ]₀
  unitrec-β-ηᵛ {A} ⊢A ⊩k ⊩A ⊩t ⊩u η =
    let ⊢Unit = ⊢∙→⊢ (wf ⊢A)
        ok    = inversion-Unit-allowed ⊢Unit
    in
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         unitrec-β-η
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩k ⊩σ)
           (subst-⊢ ⊢A (⊢ˢʷ∷-⇑′ ⊢Unit (escape-⊩ˢ∷ ⊩σ .proj₂)))
           (R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ))
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ))
           ok η)
      (conv-⊩ᵛ∷
         (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩A) $
          η-unitᵛ (starᵛ ⊩k ok) ⊩t (inj₂ η))
         ⊩u)
