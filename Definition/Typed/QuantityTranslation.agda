------------------------------------------------------------------------
-- The quantity translation functions preserve various things related
-- to typing (assuming that type restrictions are preserved in a
-- certain way)
------------------------------------------------------------------------

open import Graded.Modality.Morphism.Type-restrictions
open import Definition.Typed.Restrictions

module Definition.Typed.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (R₁ : Type-restrictions M₁)
  (R₂ : Type-restrictions M₂)
  (tr tr-Σ : M₁ → M₂)
  (pres : Are-preserving-type-restrictions R₁ R₂ tr tr-Σ)
  where

open Are-preserving-type-restrictions pres

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open import Definition.Typed
open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.QuantityTranslation tr tr-Σ

private
  module T₁ = Definition.Typed R₁
  module T₂ = Definition.Typed R₂
  module U₁ = Definition.Untyped M₁
  module U₂ = Definition.Untyped M₂

private variable
  x       : Fin _
  Γ Δ     : Con _ _
  A B t u : Term _ _
  σ σ′    : Subst _ _ _
  p q     : M₁

-- Preservation of _∷_∈_.

tr-∷∈ : x T₁.∷ A ∈ Γ → x T₂.∷ tr-Term A ∈ tr-Con Γ
tr-∷∈ here =
  PE.subst (_ T₂.∷_∈ _ ∙ tr-Term _) tr-Term-wk here
tr-∷∈ (there x) =
  PE.subst (_ T₂.∷_∈ _ ∙ tr-Term _) tr-Term-wk (there (tr-∷∈ x))

mutual

  -- Preservation of ⊢_.

  tr-⊢ : T₁.⊢ Γ → T₂.⊢ tr-Con Γ
  tr-⊢ ε       = ε
  tr-⊢ (Γ ∙ A) = tr-⊢ Γ ∙ tr-⊢′ A

  -- Preservation of _⊢_.

  tr-⊢′ : Γ T₁.⊢ A → tr-Con Γ T₂.⊢ tr-Term A
  tr-⊢′ (Uⱼ Γ) =
    Uⱼ (tr-⊢ Γ)
  tr-⊢′ (ℕⱼ Γ) =
    ℕⱼ (tr-⊢ Γ)
  tr-⊢′ (Emptyⱼ Γ) =
    Emptyⱼ (tr-⊢ Γ)
  tr-⊢′ (Unitⱼ Γ ok) =
    Unitⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢′ (ΠΣⱼ {b = b} A P ok) =
    ΠΣⱼ (tr-⊢′ A) (tr-⊢′ P) (ΠΣ-preserved ok)
  tr-⊢′ (univ A) =
    univ (tr-⊢∷ A)

  -- Preservation of _⊢_∷_.

  tr-⊢∷ : Γ T₁.⊢ t ∷ A → tr-Con Γ T₂.⊢ tr-Term t ∷ tr-Term A
  tr-⊢∷ (ΠΣⱼ {b = b} A P ok) =
    ΠΣⱼ (tr-⊢∷ A) (tr-⊢∷ P) (ΠΣ-preserved ok)
  tr-⊢∷ (ℕⱼ Γ) =
    ℕⱼ (tr-⊢ Γ)
  tr-⊢∷ (Emptyⱼ Γ) =
    Emptyⱼ (tr-⊢ Γ)
  tr-⊢∷ (Unitⱼ Γ ok) =
    Unitⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢∷ (var Γ x) =
    var (tr-⊢ Γ) (tr-∷∈ x)
  tr-⊢∷ (lamⱼ A t ok) =
    lamⱼ (tr-⊢′ A) (tr-⊢∷ t) (ΠΣ-preserved ok)
  tr-⊢∷ (_∘ⱼ_ {G = P} t u) =
    PE.subst (_ T₂.⊢ _ ∷_) (tr-Term-[] P) (tr-⊢∷ t ∘ⱼ tr-⊢∷ u)
  tr-⊢∷ (prodⱼ {G = P} A ⊢P t u ok) =
    prodⱼ (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      (ΠΣ-preserved ok)
  tr-⊢∷ (fstⱼ A P t) =
    fstⱼ (tr-⊢′ A) (tr-⊢′ P) (tr-⊢∷ t)
  tr-⊢∷ (sndⱼ {G = P} A ⊢P t) =
    PE.subst (_ T₂.⊢ _ ∷_) (tr-Term-[] P)
      (sndⱼ (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t))
  tr-⊢∷ (prodrecⱼ {A = Q} A P ⊢Q t u ok) =
    PE.subst (_ T₂.⊢ prodrec _ _ _ _ _ _ ∷_) (tr-Term-[] Q)
      (prodrecⱼ (tr-⊢′ A) (tr-⊢′ P) (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ u))
         (ΠΣ-preserved ok))
  tr-⊢∷ (zeroⱼ Γ) =
    zeroⱼ (tr-⊢ Γ)
  tr-⊢∷ (sucⱼ t) =
    sucⱼ (tr-⊢∷ t)
  tr-⊢∷ (natrecⱼ {A = P} ⊢P z s n) =
    PE.subst (_ T₂.⊢ natrec _ _ _ _ _ _ _ ∷_) (tr-Term-[] P)
      (natrecⱼ (tr-⊢′ ⊢P)
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (_ ∙ _ ∙ tr-Term _ T₂.⊢ _ ∷_)
            (PE.sym (tr-Term-[]↑² P) )
            (tr-⊢∷ s))
         (tr-⊢∷ n))
  tr-⊢∷ (Emptyrecⱼ A e) =
    Emptyrecⱼ (tr-⊢′ A) (tr-⊢∷ e)
  tr-⊢∷ (starⱼ Γ ok) =
    starⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢∷ (conv t A≡B) =
    conv (tr-⊢∷ t) (tr-⊢≡ A≡B)

  -- Preservation of _⊢_≡_.

  tr-⊢≡ : Γ T₁.⊢ A ≡ B → tr-Con Γ T₂.⊢ tr-Term A ≡ tr-Term B
  tr-⊢≡ (univ A≡B) =
    univ (tr-⊢≡∷ A≡B)
  tr-⊢≡ (refl A) =
    refl (tr-⊢′ A)
  tr-⊢≡ (sym A≡B) =
    sym (tr-⊢≡ A≡B)
  tr-⊢≡ (trans A≡B C≡D) =
    trans (tr-⊢≡ A≡B) (tr-⊢≡ C≡D)
  tr-⊢≡ (ΠΣ-cong {b = b} A A≡B C≡D ok) =
    ΠΣ-cong (tr-⊢′ A) (tr-⊢≡ A≡B) (tr-⊢≡ C≡D) (ΠΣ-preserved ok)

  -- Preservation of _⊢_≡_∷_.

  tr-⊢≡∷ :
    Γ T₁.⊢ t ≡ u ∷ A → tr-Con Γ T₂.⊢ tr-Term t ≡ tr-Term u ∷ tr-Term A
  tr-⊢≡∷ (refl t) =
    refl (tr-⊢∷ t)
  tr-⊢≡∷ (sym t≡u) =
    sym (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (trans t≡u u≡v) =
    trans (tr-⊢≡∷ t≡u) (tr-⊢≡∷ u≡v)
  tr-⊢≡∷ (conv t≡u A≡B) =
    conv (tr-⊢≡∷ t≡u) (tr-⊢≡ A≡B)
  tr-⊢≡∷ (ΠΣ-cong {b = b} A A≡B C≡D ok) =
    ΠΣ-cong (tr-⊢′ A) (tr-⊢≡∷ A≡B) (tr-⊢≡∷ C≡D) (ΠΣ-preserved ok)
  tr-⊢≡∷ (app-cong {G = P} t≡u v≡w) =
    PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (tr-Term-[] P)
      (app-cong (tr-⊢≡∷ t≡u) (tr-⊢≡∷ v≡w))
  tr-⊢≡∷ (β-red {G = P} {t = t} A ⊢P ⊢t u PE.refl ok) =
    PE.subst₂
      (_ T₂.⊢ _ ∘⟨ _ ⟩ _ ≡_∷_)
      (tr-Term-[] t)
      (tr-Term-[] P)
      (β-red (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ ⊢t) (tr-⊢∷ u) PE.refl
         (ΠΣ-preserved ok))
  tr-⊢≡∷ {Γ = Γ} (η-eq {F = A} {G = P} ⊢A t u t≡u) =
    η-eq (tr-⊢′ ⊢A) (tr-⊢∷ t) (tr-⊢∷ u)
      (PE.subst₂ (tr-Con (Γ ∙ A) T₂.⊢_≡_∷ tr-Term P)
         (PE.sym (PE.cong (_∘⟨ _ ⟩ _ ) tr-Term-wk))
         (PE.sym (PE.cong (_∘⟨ _ ⟩ _ ) tr-Term-wk))
         (tr-⊢≡∷ t≡u))
  tr-⊢≡∷ (fst-cong A P t≡u) =
    fst-cong (tr-⊢′ A) (tr-⊢′ P) (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (snd-cong {G = P} A ⊢P t≡u) =
    PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (tr-Term-[] P)
      (snd-cong (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢≡∷ t≡u))
  tr-⊢≡∷ (prod-cong {G = P} {k = s} A ⊢P t≡u v≡w ok) =
    prod-cong (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢≡∷ t≡u)
      (PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢≡∷ v≡w))
      (ΠΣ-preserved ok)
  tr-⊢≡∷ (Σ-β₁ {G = P} A ⊢P t u PE.refl ok) =
    Σ-β₁ (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      PE.refl (ΠΣ-preserved ok)
  tr-⊢≡∷ (Σ-β₂ {G = P} A ⊢P t u PE.refl ok) =
    PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (tr-Term-[] P)
      (Σ-β₂ (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t)
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ (Σ-η {G = P} A ⊢P t u t₁≡u₁ t₂≡u₂) =
    Σ-η (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t) (tr-⊢∷ u) (tr-⊢≡∷ t₁≡u₁)
      (PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (PE.sym (tr-Term-[] P))
         (tr-⊢≡∷ t₂≡u₂))
  tr-⊢≡∷ (prodrec-cong {A = Q} A P Q≡R t≡u v≡w ok) =
    PE.subst (_ T₂.⊢ prodrec _ _ _ _ _ _ ≡ _ ∷_) (tr-Term-[] Q)
      (prodrec-cong (tr-⊢′ A) (tr-⊢′ P) (tr-⊢≡ Q≡R) (tr-⊢≡∷ t≡u)
         (PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (PE.sym (tr-Term-[]↑² Q))
            (tr-⊢≡∷ v≡w))
         (ΠΣ-preserved ok))
  tr-⊢≡∷
    (prodrec-β {G = P} {A = Q} {u = v} A ⊢P ⊢Q t u ⊢v PE.refl ok) =
    PE.subst₂ (_ T₂.⊢ prodrec _ _ _ _ _ _ ≡_∷_)
      (tr-Term-[,] v)
      (tr-Term-[] Q)
      (prodrec-β (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ ⊢v))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ (suc-cong t≡u) =
    suc-cong (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (natrec-cong {A = P} ⊢P P≡P′ z≡z′ s≡s′ n≡n′) =
    PE.subst (_ T₂.⊢ natrec _ _ _ _ _ _ _ ≡ _ ∷_) (tr-Term-[] P)
      (natrec-cong (tr-⊢′ ⊢P) (tr-⊢≡ P≡P′)
         (PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (PE.sym (tr-Term-[] P))
            (tr-⊢≡∷ z≡z′))
         (PE.subst (tr-Con (_ ∙ ℕ ∙ _) T₂.⊢ _ ≡ _ ∷_)
            (PE.sym (tr-Term-[]↑² P))
            (tr-⊢≡∷ s≡s′))
         (tr-⊢≡∷ n≡n′))
  tr-⊢≡∷ (natrec-zero {A = P} ⊢P z s) =
    PE.subst (_ T₂.⊢ natrec _ _ _ (tr-Term P) _ _ _ ≡ _ ∷_)
      (tr-Term-[] P)
      (natrec-zero (tr-⊢′ ⊢P)
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (tr-Con (_ ∙ ℕ ∙ _) T₂.⊢ _ ∷_)
            (PE.sym (tr-Term-[]↑² P))
            (tr-⊢∷ s)))
  tr-⊢≡∷ (natrec-suc {A = P} {s = s} ⊢P z ⊢s n) =
    PE.subst₂ (_ T₂.⊢ natrec _ _ _ _ _ _ _ ≡_∷_)
      (tr-Term-[,] s)
      (tr-Term-[] P)
      (natrec-suc (tr-⊢′ ⊢P)
         (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (tr-Con (_ ∙ ℕ ∙ _) T₂.⊢ _ ∷_)
            (PE.sym (tr-Term-[]↑² P))
            (tr-⊢∷ ⊢s))
         (tr-⊢∷ n))
  tr-⊢≡∷ (Emptyrec-cong A≡B t≡u) =
    Emptyrec-cong (tr-⊢≡ A≡B) (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (η-unit t u) =
    η-unit (tr-⊢∷ t) (tr-⊢∷ u)

-- Preservation of _⊢_⇒_∷_.

tr-⊢⇒∷ :
  Γ T₁.⊢ t ⇒ u ∷ A → tr-Con Γ T₂.⊢ tr-Term t ⇒ tr-Term u ∷ tr-Term A
tr-⊢⇒∷ (conv t⇒u A≡B) =
  conv (tr-⊢⇒∷ t⇒u) (tr-⊢≡ A≡B)
tr-⊢⇒∷ (app-subst {G = P} t⇒u v) =
  PE.subst (_ T₂.⊢ _ ⇒ _ ∷_) (tr-Term-[] P)
    (app-subst (tr-⊢⇒∷ t⇒u) (tr-⊢∷ v))
tr-⊢⇒∷ (β-red {G = P} {t = t} A ⊢P ⊢t u PE.refl ok) =
  PE.subst₂
    (_ T₂.⊢ _ ∘⟨ _ ⟩ _ ⇒_∷_)
    (tr-Term-[] t)
    (tr-Term-[] P)
    (β-red (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ ⊢t) (tr-⊢∷ u) PE.refl
       (ΠΣ-preserved ok))
tr-⊢⇒∷ (fst-subst A P t⇒u) =
  fst-subst (tr-⊢′ A) (tr-⊢′ P) (tr-⊢⇒∷ t⇒u)
tr-⊢⇒∷ (snd-subst {G = P} A ⊢P t⇒u) =
  PE.subst (_ T₂.⊢ _ ⇒ _ ∷_) (tr-Term-[] P)
    (snd-subst (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢⇒∷ t⇒u))
tr-⊢⇒∷ (Σ-β₁ {G = P} A ⊢P t u PE.refl ok) =
  Σ-β₁ (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t)
    (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
    PE.refl (ΠΣ-preserved ok)
tr-⊢⇒∷ (Σ-β₂ {G = P} A ⊢P t u PE.refl ok) =
  PE.subst (_ T₂.⊢ _ ⇒ _ ∷_) (tr-Term-[] P)
    (Σ-β₂ (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢∷ t)
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
       PE.refl (ΠΣ-preserved ok))
tr-⊢⇒∷ (prodrec-subst {A = Q} A P ⊢Q v t⇒u ok) =
  PE.subst (_ T₂.⊢ prodrec _ _ _ _ _ _ ⇒ _ ∷_) (tr-Term-[] Q)
    (prodrec-subst (tr-⊢′ A) (tr-⊢′ P) (tr-⊢′ ⊢Q)
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ v))
       (tr-⊢⇒∷ t⇒u) (ΠΣ-preserved ok))
tr-⊢⇒∷
  (prodrec-β {G = P} {A = Q} {u = v} A ⊢P ⊢Q t u ⊢v PE.refl ok) =
  PE.subst₂ (_ T₂.⊢ prodrec _ _ _ _ _ _ ⇒_∷_)
    (tr-Term-[,] v)
    (tr-Term-[] Q)
    (prodrec-β (tr-⊢′ A) (tr-⊢′ ⊢P) (tr-⊢′ ⊢Q) (tr-⊢∷ t)
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ ⊢v))
       PE.refl (ΠΣ-preserved ok))
tr-⊢⇒∷ (natrec-subst {A = P} ⊢P z s n⇒n′) =
  PE.subst (_ T₂.⊢ natrec _ _ _ _ _ _ _ ⇒ _ ∷_) (tr-Term-[] P)
    (natrec-subst (tr-⊢′ ⊢P)
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
       (PE.subst (tr-Con (_ ∙ ℕ ∙ _) T₂.⊢ _ ∷_)
          (PE.sym (tr-Term-[]↑² P))
          (tr-⊢∷ s))
       (tr-⊢⇒∷ n⇒n′))
tr-⊢⇒∷ (natrec-zero {A = P} ⊢P z s) =
  PE.subst (_ T₂.⊢ natrec _ _ _ (tr-Term P) _ _ _ ⇒ _ ∷_)
    (tr-Term-[] P)
    (natrec-zero (tr-⊢′ ⊢P)
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
       (PE.subst (tr-Con (_ ∙ ℕ ∙ _) T₂.⊢ _ ∷_)
          (PE.sym (tr-Term-[]↑² P))
          (tr-⊢∷ s)))
tr-⊢⇒∷ (natrec-suc {A = P} {s = s} ⊢P z ⊢s n) =
  PE.subst₂ (_ T₂.⊢ natrec _ _ _ _ _ _ _ ⇒_∷_)
    (tr-Term-[,] s)
    (tr-Term-[] P)
    (natrec-suc (tr-⊢′ ⊢P)
       (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
       (PE.subst (tr-Con (_ ∙ ℕ ∙ _) T₂.⊢ _ ∷_)
          (PE.sym (tr-Term-[]↑² P))
          (tr-⊢∷ ⊢s))
       (tr-⊢∷ n))
tr-⊢⇒∷ (Emptyrec-subst A t⇒u) =
  Emptyrec-subst (tr-⊢′ A) (tr-⊢⇒∷ t⇒u)

-- Preservation of _⊢_⇒_.

tr-⊢⇒ : Γ T₁.⊢ A ⇒ B → tr-Con Γ T₂.⊢ tr-Term A ⇒ tr-Term B
tr-⊢⇒ (univ A⇒B) = univ (tr-⊢⇒∷ A⇒B)

-- Preservation of _⊢_⇒*_∷_.

tr-⊢⇒*∷ :
  Γ T₁.⊢ t ⇒* u ∷ A → tr-Con Γ T₂.⊢ tr-Term t ⇒* tr-Term u ∷ tr-Term A
tr-⊢⇒*∷ (id t)       = id (tr-⊢∷ t)
tr-⊢⇒*∷ (t⇒u ⇨ u⇒*v) = tr-⊢⇒∷ t⇒u ⇨ tr-⊢⇒*∷ u⇒*v

-- Preservation of _⊢_⇒*_.

tr-⊢⇒* : Γ T₁.⊢ A ⇒* B → tr-Con Γ T₂.⊢ tr-Term A ⇒* tr-Term B
tr-⊢⇒* (id A)       = id (tr-⊢′ A)
tr-⊢⇒* (A⇒B ⇨ B⇒*C) = tr-⊢⇒ A⇒B ⇨ tr-⊢⇒* B⇒*C

-- Preservation of _⊢_↘_.

tr-⊢↘ : Γ T₁.⊢ A ↘ B → tr-Con Γ T₂.⊢ tr-Term A ↘ tr-Term B
tr-⊢↘ (A⇒*B , B) = tr-⊢⇒* A⇒*B , tr-Whnf B

-- Preservation of _⊢_↘_∷_.

tr-⊢↘∷ :
  Γ T₁.⊢ t ↘ u ∷ A → tr-Con Γ T₂.⊢ tr-Term t ↘ tr-Term u ∷ tr-Term A
tr-⊢↘∷ (t⇒*u , u) = tr-⊢⇒*∷ t⇒*u , tr-Whnf u

-- Preservation of _⊢_:≡:_.

tr-⊢:≡: : Γ T₁.⊢ A :≡: B → tr-Con Γ T₂.⊢ tr-Term A :≡: tr-Term B
tr-⊢:≡: (A , B , A≡B) = tr-⊢′ A , tr-⊢′ B , tr-⊢≡ A≡B

-- Preservation of _⊢_:≡:_∷_.

tr-⊢:≡:∷ :
  Γ T₁.⊢ t :≡: u ∷ A → tr-Con Γ T₂.⊢ tr-Term t :≡: tr-Term u ∷ tr-Term A
tr-⊢:≡:∷ (t , u , t≡u) = tr-⊢∷ t , tr-⊢∷ u , tr-⊢≡∷ t≡u

-- Preservation of _⊢_:⇒*:_.

tr-⊢:⇒*: : Γ T₁.⊢ A :⇒*: B → tr-Con Γ T₂.⊢ tr-Term A :⇒*: tr-Term B
tr-⊢:⇒*: [ A , B , A⇒*B ] = [ tr-⊢′ A , tr-⊢′ B , tr-⊢⇒* A⇒*B ]

-- Preservation of _⊢_:⇒*:_∷_.

tr-⊢:⇒*:∷ :
  Γ T₁.⊢ t :⇒*: u ∷ A →
  tr-Con Γ T₂.⊢ tr-Term t :⇒*: tr-Term u ∷ tr-Term A
tr-⊢:⇒*:∷ [ t , u , t⇒*u ] = [ tr-⊢∷ t , tr-⊢∷ u , tr-⊢⇒*∷ t⇒*u ]

-- Preservation of _⊢ˢ_∷_.

tr-⊢ˢ∷ : Δ T₁.⊢ˢ σ ∷ Γ → tr-Con Δ T₂.⊢ˢ tr-Subst σ ∷ tr-Con Γ
tr-⊢ˢ∷ id                           = id
tr-⊢ˢ∷ (_,_ {A = A} ⊢ˢtail ⊢head) =
    tr-⊢ˢ∷ ⊢ˢtail
  , PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-subst A)) (tr-⊢∷ ⊢head)

-- Preservation of _⊢ˢ_≡_∷_.

tr-⊢ˢ≡∷ :
  Δ T₁.⊢ˢ σ ≡ σ′ ∷ Γ →
  tr-Con Δ T₂.⊢ˢ tr-Subst σ ≡ tr-Subst σ′ ∷ tr-Con Γ
tr-⊢ˢ≡∷ id                           = id
tr-⊢ˢ≡∷ (_,_ {A = A} ⊢ˢtail≡ ⊢head≡) =
    tr-⊢ˢ≡∷ ⊢ˢtail≡
  , PE.subst (_ T₂.⊢ _ ≡ _ ∷_) (PE.sym (tr-Term-subst A))
      (tr-⊢≡∷ ⊢head≡)