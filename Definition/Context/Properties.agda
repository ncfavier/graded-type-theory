{-# OPTIONS --without-K --safe #-}

module Definition.Context.Properties where

open import Definition.Context
open import Definition.Modality
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality


-- Modality contexts form a left module

-- 𝟙 is a left identity to modality contex scaling
identity : (M : Modality A) → (γ : Con A ℓ) → M ▷ (Modality.𝟙 M) · γ ≡ γ
identity M  ε      = refl
identity M (γ · p) = cong₂ _·_ γ' p'
  where
  γ' = identity M γ
  p' = (proj₁ (Modality.·-Identity M)) p

-- 𝟘 is a left zero to modality context scaling
leftZero : (M : Modality A) → (γ : Con A ℓ) → 𝟘ᶜ M ≡ M ▷ (Modality.𝟘 M) · γ
leftZero M ε = refl
leftZero M (γ · p) = cong₂ _·_ IH z
  where
  IH = leftZero M γ
  z  = sym (proj₁ (Modality.·-Zero M) p)

-- A zero context is a right zero to modality context scaling
rightZero : (M : Modality A) → (p : A) → 𝟘ᶜ {ℓ = ℓ} M ≡ M ▷ p · (𝟘ᶜ M)
rightZero {ℓ = 0}    M p = refl
rightZero {ℓ = 1+ ℓ} M p = cong₂ _·_ IH z
  where
  IH = rightZero M p
  z  = sym (proj₂ (Modality.·-Zero M) p)

-- Modality context scaling is associative
associative : (M : Modality A) → (p q : A) → (γ : Con A ℓ) →
               M ▷ (Modality._·_ M p q) · γ ≡ M ▷ p · (M ▷ q · γ)
associative M p q  ε      = refl
associative M p q (γ · r) = cong₂ _·_ γ' r'
  where
  γ' = associative M p q γ
  r' = Modality.·-Associative M p q r

-- Modality contex scaling is left distributive over addition
leftDistr+ : (M : Modality A) → (p : A) → (γ δ : Con A ℓ) →
              M ▷ p · (M ▷ γ + δ) ≡ M ▷ (M ▷ p · γ) + (M ▷ p · δ)
leftDistr+ M p  ε       ε      = refl
leftDistr+ M p (γ · q) (δ · r) = cong₂ _·_ IH distr
  where
  IH    = leftDistr+ M p γ δ
  distr = proj₁ (Modality.·Distr+ M) p q r

-- Modality context scaling is right distributive over addition
rightDistr+ : (M : Modality A) → (p q : A) → (γ : Con A ℓ) →
               M ▷ (Modality._+_ M p q) · γ ≡ M ▷ (M ▷ p · γ) + (M ▷ q · γ)
rightDistr+ M p q  ε      = refl
rightDistr+ M p q (γ · r) = cong₂ _·_ IH distr
  where
  IH    = rightDistr+ M p q γ
  distr = proj₂ (Modality.·Distr+ M) r p q

-- Modality contex scaling is left distributive over meet
leftDistr∧ : (M : Modality A) → (p : A) → (γ δ : Con A ℓ) →
              M ▷ p · (M ▷ γ ∧ δ) ≡ M ▷ (M ▷ p · γ) ∧ (M ▷ p · δ)
leftDistr∧ M p  ε       ε      = refl
leftDistr∧ M p (γ · q) (δ · r) = cong₂ _·_ IH distr
  where
  IH    = leftDistr∧ M p γ δ
  distr = proj₁ (Modality.·Distr∧ M) p q r

-- Modality context scaling is right distributive over meet
rightDistr∧ : {A : Set} → (M : Modality A) → (p q : A) → (γ : Con A ℓ)
                        → M ▷ (Modality._∧_ M p q) · γ ≡ M ▷ (M ▷ p · γ) ∧ (M ▷ q · γ)
rightDistr∧ M p q  ε      = refl
rightDistr∧ M p q (γ · r) = cong₂ _·_ IH distr
  where
    IH    = rightDistr∧ M p q γ
    distr = proj₂ (Modality.·Distr∧ M) r p q
