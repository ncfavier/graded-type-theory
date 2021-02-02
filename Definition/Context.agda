{-# OPTIONS --without-K --safe #-}

module Definition.Context where

open import Definition.Modality
open import Tools.Nat
open import Tools.PropositionalEquality

infixl 30 _·_

data Con (A : Set) : Nat → Set where
  ε   : Con A 0
  _·_ : {n : Nat} → Con A n → A → Con A (1+ n)

variable
  ℓ : Nat
  A : Set

infix 15 _▷_+_
infix 15 _▷_∧_
infix 18 _▷_·_

-- Addition lifted to modality contexts
_▷_+_  : Modality A → (γ δ : Con A ℓ) → Con A ℓ
M ▷  ε      +  ε      = ε
M ▷ (γ · p) + (δ · q) = (M ▷ γ + δ) · (Modality._+_ M p q)

-- Meet lifted to modality contexts
_▷_∧_ : Modality A → (γ δ : Con A ℓ) → Con A ℓ
M ▷  ε      ∧  ε      = ε
M ▷ (γ · p) ∧ (δ · q) = (M ▷ γ ∧ δ) · Modality._∧_ M p q

-- Scaling of modality contexts
_▷_·_ : Modality A → (p : A) → (γ : Con A ℓ) → Con A ℓ
M ▷ p ·  ε      = ε
M ▷ p · (γ · q) = (M ▷ p · γ) · Modality._·_ M p q

-- Partial order for modalities lifted to modality contexts
_▷_≤_ : Modality A → (γ δ : Con A ℓ) → Set
M ▷ γ ≤ δ = γ ≡ (M ▷ γ ∧ δ)

-- Zero modality context
𝟘ᶜ : Modality A → Con A ℓ
𝟘ᶜ {ℓ = 0}    M = ε
𝟘ᶜ {ℓ = 1+ ℓ} M = 𝟘ᶜ M · Modality.𝟘 M

-- Unit modality context
𝟙ᶜ : Modality A → Con A ℓ
𝟙ᶜ {ℓ = 0}    M = ε
𝟙ᶜ {ℓ = 1+ n} M = 𝟙ᶜ M · Modality.𝟙 M
