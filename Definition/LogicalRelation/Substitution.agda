module Definition.LogicalRelation.Substitution where

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.Typed

open import Tools.Context

open import Data.Nat
open import Data.Product
open import Data.Unit

import Relation.Binary.PropositionalEquality as PE


mutual
  data ⊩ₛ⟨_⟩_ (l : TypeLevel) : Con Term → Set where
    ε : ⊩ₛ⟨ l ⟩ ε
    _∙_ : ∀ {Γ A} ([Γ] : ⊩ₛ⟨ l ⟩ Γ) → Γ ⊩ₛ⟨ l ⟩ A / [Γ]
        → ⊩ₛ⟨ l ⟩ Γ ∙ A

  _⊩ₛ⟨_⟩_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ₛ⟨ l ⟩ Γ → Set
  Γ ⊩ₛ⟨ l ⟩ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ)
                   → Σ (Δ ⊩⟨ l ⟩ subst σ A)
                       (λ [Aσ] → ∀ {σ'} → Δ ⊩ₛ⟨ l ⟩ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
                              → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ' A / [Aσ])

  _⊩ₛ⟨_⟩_∷_/_/_ : (Δ : Con Term) (l : TypeLevel) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ₛ⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ) → Set
  Δ ⊩ₛ⟨ l ⟩ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  Δ ⊩ₛ⟨ l ⟩ σ ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊩ₛ⟨ l ⟩ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
    (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))

  _⊩ₛ⟨_⟩_≡_∷_/_/_/_ : (Δ : Con Term) (l : TypeLevel) (σ σ' : Subst) (Γ : Con Term) ([Γ] : ⊩ₛ⟨ l ⟩ Γ) (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  Δ ⊩ₛ⟨ l ⟩ σ ≡ σ' ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  Δ ⊩ₛ⟨ l ⟩ σ ≡ σ' ∷ .(Γ ∙ A) / (_∙_ {Γ} {A} [Γ] [A]) / ⊢Δ / [σ] =
    (Δ ⊩ₛ⟨ l ⟩ tail σ ≡ tail σ' ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (Δ ⊩⟨ l ⟩ head σ ≡ head σ' ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ])))


_⊩ₛ⟨_⟩t_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) ([Γ] : ⊩ₛ⟨ l ⟩ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) → Set
Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ'} → Δ ⊩ₛ⟨ l ⟩ σ ≡ σ' ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ' t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

_⊩ₛ⟨_⟩_≡_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) ([Γ] : ⊩ₛ⟨ l ⟩ Γ) ([A] : Γ ⊩ₛ⟨ l ⟩ A / [Γ]) -> Set
Γ ⊩ₛ⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

record _⊩ₛ⟨_⟩t_≡_∷_/_ (Γ : Con Term) (l : TypeLevel) (t u A : Term) ([Γ] : ⊩ₛ⟨ l ⟩ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ₛ⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊩ₛ⟨ l ⟩t t ∷ A / [Γ] / [A]
    [u]   : Γ ⊩ₛ⟨ l ⟩t u ∷ A / [Γ] / [A]
    [t≡u] : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ₛ⟨ l ⟩ σ ∷ Γ / [Γ] / ⊢Δ)
            → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])
