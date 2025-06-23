------------------------------------------------------------------------
-- Algorithmic equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R hiding (_⊢_~_∷_)
open import Definition.LogicalRelation R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqRelInstance ⦄

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
import Tools.List as L
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

import Data.List as L
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any

infix 10 _⊢_~_↑_
infix 10 _⊢_~_↓_
infix 10 _⊢_[conv↑]_
infix 10 _⊢_[conv↓]_
infix 10 _⊢_[conv↑]_∷_
infix 10 _⊢_[conv↓]_∷_

private
  variable
    n : Nat
    Γ : Con Term n
    A₁ A₂ B₁ B₂ C F G E : Term n
    g h k l l′ l₁ l₂ t t₁ t₂ t₃ u u₁ u₂ u₃ v v₁ v₂ w₁ w₂ : Term n
    x y : Fin n
    p p′ p″ p₁ p₂ q q′ q″ q₁ q₂ r r′ : M
    b : BinderMode
    s : Strength

mutual
  -- Neutral equality.
  data _⊢_~_↑_ (Γ : Con Term n) : (k l A : Term n) → Set a where

    var-refl      : Γ ⊢ var x ∷ C
                  → x PE.≡ y
                  → Γ ⊢ var x ~ var y ↑ C

    lower-cong    : ∀ {A}
                  → Γ ⊢ t₁ ~ t₂ ↓ Lift k A
                  → Γ ⊢ lower t₁ ~ lower t₂ ↑ A

    app-cong      : ∀ {A B}
                  → Γ ⊢ t₁ ~ t₂ ↓ Π p , q ▷ A ▹ B
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ A
                  → Γ ⊢ t₁ ∘⟨ p ⟩ u₁ ~ t₂ ∘⟨ p ⟩ u₂ ↑ B [ u₁ ]₀

    fst-cong      : ∀ {A B}
                  → Γ ⊢ t₁ ~ t₂ ↓ Σˢ p , q ▷ A ▹ B
                  → Γ ⊢ fst p t₁ ~ fst p t₂ ↑ A

    snd-cong      : ∀ {A B}
                  → Γ ⊢ t₁ ~ t₂ ↓ Σˢ p , q ▷ A ▹ B
                  → Γ ⊢ snd p t₁ ~ snd p t₂ ↑ B [ fst p t₁ ]₀

    natrec-cong   : Γ ∙ ℕ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ [ zero ]₀
                  → Γ ∙ ℕ ∙ A₁ ⊢ u₁ [conv↑] u₂ ∷ A₁ [ suc (var x1) ]↑²
                  → Γ ⊢ v₁ ~ v₂ ↓ ℕ
                  → Γ ⊢ natrec p q r A₁ t₁ u₁ v₁ ~
                      natrec p q r A₂ t₂ u₂ v₂ ↑ A₁ [ v₁ ]₀

    prodrec-cong  : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ C [conv↑] E
                  → Γ ⊢ g ~ h ↓ Σʷ p , q ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u [conv↑] v ∷ C [ prodʷ p (var x1) (var x0) ]↑²
                  → Γ ⊢ prodrec r p q′ C g u ~ prodrec r p q′ E h v ↑ C [ g ]₀

    emptyrec-cong : Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ ~ t₂ ↓ Empty
                  → Γ ⊢ emptyrec p A₁ t₁ ~ emptyrec p A₂ t₂ ↑ A₁

    unitrec-cong : Γ ⊢ l₁ [conv↑] l₂ ∷ Level
                 → Γ ∙ Unitʷ l₁ ⊢ A₁ [conv↑] A₂
                 → Γ ⊢ t₁ ~ t₂ ∷ Unitʷ l₁
                 → Γ ⊢ u₁ [conv↑] u₂ ∷ A₁ [ starʷ l₁ ]₀
                 → ¬ Unitʷ-η
                 → Γ ⊢ unitrec p q l₁ A₁ t₁ u₁ ~ unitrec p q l₂ A₂ t₂ u₂ ↑
                     A₁ [ t₁ ]₀

    J-cong        : Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
                  → Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀
                  → Γ ⊢ v₁ [conv↑] v₂ ∷ A₁
                  → Γ ⊢ w₁ ~ w₂ ↓ C
                  → Γ ⊢ C ≡ Id A₁ t₁ v₁
                  → Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~
                        J p q A₂ t₂ B₂ u₂ v₂ w₂ ↑ B₁ [ v₁ , w₁ ]₁₀

    K-cong        : Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
                  → Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀
                  → Γ ⊢ v₁ ~ v₂ ↓ C
                  → Γ ⊢ C ≡ Id A₁ t₁ t₁
                  → K-allowed
                  → Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ↑
                      B₁ [ v₁ ]₀

    []-cong-cong  : ∀ {B}
                  → Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ A₁
                  → Γ ⊢ v₁ ~ v₂ ↓ B
                  → Γ ⊢ B ≡ Id A₁ t₁ u₁
                  → []-cong-allowed s
                  → let open Erased s in
                    Γ ⊢ []-cong s A₁ t₁ u₁ v₁ ~ []-cong s A₂ t₂ u₂ v₂ ↑
                      Id (Erased A₁) ([ t₁ ]) ([ u₁ ])

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓_ (Γ : Con Term n) (k l B : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor [~]
    field
      A   : Term n
      D   : Γ ⊢ A ↘ B
      k~l : Γ ⊢ k ~ l ↑ A

  -- Algorithmic equality of neutrals with injected conversion.
  record _⊢_~_∷_ (Γ : Con Term n) (k l A : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor ↑
    field
      {B} : Term n
      A≡B : Γ ⊢ A ≡ B
      k~↑l : Γ ⊢ k ~ l ↑ B

  -- Type equality.
  record _⊢_[conv↑]_ (Γ : Con Term n) (A B : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor [↑]
    field
      A′ B′  : Term n
      D      : Γ ⊢ A ↘ A′
      D′     : Γ ⊢ B ↘ B′
      A′<>B′ : Γ ⊢ A′ [conv↓] B′

  -- Type equality with types in WHNF.
  data _⊢_[conv↓]_ (Γ : Con Term n) : (A B : Term n) → Set a where

    Level-refl : ⊢ Γ → Γ ⊢ Level [conv↓] Level

    U-cong     : Γ ⊢ l₁ [conv↑] l₂ ∷ Level
               → Γ ⊢ U l₁ [conv↓] U l₂

    Lift-cong  : ∀ {F H}
               → Γ ⊢ l₁ [conv↑] l₂ ∷ Level
               → Γ ⊢ F [conv↑] H
               → Γ ⊢ Lift l₁ F [conv↓] Lift l₂ H

    ℕ-refl     : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ

    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty

    Unit-cong  : Γ ⊢ l₁ [conv↑] l₂ ∷ Level
               → Unit-allowed s
               → Γ ⊢ Unit s l₁ [conv↓] Unit s l₂

    ne         : Γ ⊢ A₁ ~ A₂ ↓ U l
               → Γ ⊢ A₁ [conv↓] A₂

    ΠΣ-cong    : ∀ {F G H E}
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → ΠΣ-allowed b p q
               → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G [conv↓] ΠΣ⟨ b ⟩ p , q ▷ H ▹ E

    Id-cong    : Γ ⊢ A₁ [conv↑] A₂
               → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
               → Γ ⊢ u₁ [conv↑] u₂ ∷ A₁
               → Γ ⊢ Id A₁ t₁ u₁ [conv↓] Id A₂ t₂ u₂

  -- Term equality.
  record _⊢_[conv↑]_∷_ (Γ : Con Term n) (t u A : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor [↑]ₜ
    field
      B t′ u′ : Term n
      D       : Γ ⊢ A ↘ B
      d       : Γ ⊢ t ↘ t′ ∷ B
      d′      : Γ ⊢ u ↘ u′ ∷ B
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B

  data LevelAtom (Γ : Con Term n) : Set a where
    zeroᵘ : LevelAtom Γ
    ne : ∀ {t : Term n} → Γ ⊢ t ~ t ↓ Level → LevelAtom Γ

  LevelPlus : Con Term n → Set a
  LevelPlus Γ = Nat × LevelAtom Γ

  LevelView : Con Term n → Set a
  LevelView Γ = L.List (LevelPlus Γ)

  data ≡ⁿ (Γ : Con Term n) (t u : Term n) : Bool → Set a where
    ne≡ : Γ ⊢ t ~ u ↓ Level → ≡ⁿ Γ t u false
    ne≡' : Γ ⊢ u ~ t ↓ Level → ≡ⁿ Γ t u true

  data ≤ᵃ {Γ : Con Term n} (d : Bool) : LevelAtom Γ → LevelAtom Γ → Set a where
    zeroᵘ≤ : ∀ {a} → ≤ᵃ d zeroᵘ a
    ne≤
      : ∀ {t u} {[t] : Γ ⊢ t ~ t ↓ Level} {[u] : Γ ⊢ u ~ u ↓ Level}
      → ≡ⁿ Γ t u d
      → ≤ᵃ d (ne [t]) (ne [u])

  ≤⁺ : Bool → LevelPlus Γ → LevelPlus Γ → Set a
  ≤⁺ d (n , a) (m , b) = n ≤ m × ≤ᵃ d a b

  ≤⁺ᵛ : Bool → LevelPlus Γ → LevelView Γ → Set a
  ≤⁺ᵛ d l l′ = Any.Any (≤⁺ d l) l′

  ≤ᵛ : Bool → LevelView Γ → LevelView Γ → Set a
  ≤ᵛ d l l′ = All.All (λ x → ≤⁺ᵛ d x l′) l

  _≡ᵛ_ : LevelView Γ → LevelView Γ → Set a
  l ≡ᵛ l′ = ≤ᵛ false l l′ × ≤ᵛ true l′ l

  record _⊢_↑ᵛ_ (Γ : Con Term n) (t : Term n) (v : LevelView Γ) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor [↑]ᵛ
    field
      {t′} : Term n
      d    : Γ ⊢ t ↘ t′ ∷ Level
      t↓v  : Γ ⊢ t′ ↓ᵛ v

  zeroᵛ : LevelView Γ
  zeroᵛ = L.[]

  suc⁺ : LevelPlus Γ → LevelPlus Γ
  suc⁺ (n , a) = 1+ n , a

  -- Using L.map here results in termination problems in Definition.Conversion.Weakening
  map-suc⁺ : LevelView Γ → LevelView Γ
  map-suc⁺ L.[] = L.[]
  map-suc⁺ (x L.∷ l) = suc⁺ x L.∷ map-suc⁺ l

  sucᵛ : LevelView Γ → LevelView Γ
  sucᵛ l = (1 , zeroᵘ) L.∷ map-suc⁺ l

  maxᵛ : LevelView Γ → LevelView Γ → LevelView Γ
  maxᵛ = L._++_

  neᵛ : Γ ⊢ t ~ t ↓ Level → LevelView Γ
  neᵛ t~t = L.[ 0 , ne t~t ]

  data _⊢_↓ᵛ_ (Γ : Con Term n) : Term n → LevelView Γ → Set a where
    zeroᵘₙ
      : ⊢ Γ
      → Γ ⊢ zeroᵘ ↓ᵛ zeroᵛ
    sucᵘₙ
      : ∀ {t v v′}
      → v PE.≡ sucᵛ v′
      → Γ ⊢ t ↑ᵛ v′
      → Γ ⊢ sucᵘ t ↓ᵛ v
    neₙ
      : ∀ {v}
      → Γ ⊢ t ~ᵛ v
      → Γ ⊢ t ↓ᵛ v

  data _⊢_~ᵛ_ (Γ : Con Term n) : Term n → LevelView Γ → Set a where
    maxᵘˡₙ
      : ∀ {t′ t″ v v′ v″}
      → v PE.≡ maxᵛ v′ v″
      → Γ ⊢ t′ ~ᵛ v′
      → Γ ⊢ t″ ↑ᵛ v″
      → Γ ⊢ t′ maxᵘ t″ ~ᵛ v
    maxᵘʳₙ
      : ∀ {t′ t″ v v′ v″}
      → v PE.≡ maxᵛ (sucᵛ v′) v″
      → Γ ⊢ t′ ↑ᵛ v′
      → Γ ⊢ t″ ~ᵛ v″
      → Γ ⊢ sucᵘ t′ maxᵘ t″ ~ᵛ v
    neₙ
      : ∀ {t v}
      → ([t] : Γ ⊢ t ~ t ↓ Level)
      → v PE.≡ neᵛ [t]
      → Γ ⊢ t ~ᵛ v

  record _⊢_[conv↑]_∷Level (Γ : Con Term n) (t u : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor [↑]ˡ
    field
      tᵛ : LevelView Γ
      uᵛ : LevelView Γ
      t↑ : Γ ⊢ t ↑ᵛ tᵛ
      u↑ : Γ ⊢ u ↑ᵛ uᵛ
      t≡u : tᵛ ≡ᵛ uᵛ

  record _⊢_[conv↓]_∷Level (Γ : Con Term n) (t u : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor [↓]ˡ
    field
      tᵛ : LevelView Γ
      uᵛ : LevelView Γ
      t↓ : Γ ⊢ t ↓ᵛ tᵛ
      u↓ : Γ ⊢ u ↓ᵛ uᵛ
      t≡u : tᵛ ≡ᵛ uᵛ

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_ (Γ : Con Term n) : (t u A : Term n) → Set a where

    Level-ins : Γ ⊢ t₁ [conv↓] t₂ ∷Level
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Level

    ℕ-ins     : Γ ⊢ t₁ ~ t₂ ↓ ℕ
              → Γ ⊢ t₁ [conv↓] t₂ ∷ ℕ

    Empty-ins : Γ ⊢ t₁ ~ t₂ ↓ Empty
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Empty

    Unitʷ-ins : ¬ Unitʷ-η
              → Γ ⊢ t₁ ~ t₂ ∷ Unitʷ l
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Unitʷ l

    Σʷ-ins    : ∀ {A A′ B B′}
              → Γ ⊢ t₁ ∷ Σʷ p , q ▷ A ▹ B
              → Γ ⊢ t₂ ∷ Σʷ p , q ▷ A ▹ B
              → Γ ⊢ t₁ ~ t₂ ↓ Σʷ p′ , q′ ▷ A′ ▹ B′
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Σʷ p , q ▷ A ▹ B

    ne-ins    : ∀ {A A′}
              → Γ ⊢ t₁ ∷ A
              → Γ ⊢ t₂ ∷ A
              → Neutral A
              → Γ ⊢ t₁ ~ t₂ ↓ A′
              → Γ ⊢ t₁ [conv↓] t₂ ∷ A

    univ      : ∀ {A B}
              → Γ ⊢ A ∷ U l
              → Γ ⊢ B ∷ U l
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A [conv↓] B ∷ U l

    Lift-η    : ∀ {A}
              → Γ ⊢ k [conv↑] k ∷ Level
              → Γ ⊢ t₁ ∷ Lift k A
              → Γ ⊢ t₂ ∷ Lift k A
              → Whnf t₁
              → Whnf t₂
              → Γ ⊢ lower t₁ [conv↑] lower t₂ ∷ A
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Lift k A

    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ

    starʷ-cong : Γ ⊢ l ≡ l₁ ∷ Level
               → Γ ⊢ l₁ [conv↑] l₂ ∷ Level
               → Unitʷ-allowed
               → ¬ Unitʷ-η
               → Γ ⊢ starʷ l₁ [conv↓] starʷ l₂ ∷ Unitʷ l

    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ

    prod-cong : ∀ {F G t t′ u u′}
              → Γ ∙ F ⊢ G
              → Γ ⊢ t [conv↑] t′ ∷ F
              → Γ ⊢ u [conv↑] u′ ∷ G [ t ]₀
              → Σʷ-allowed p q
              → Γ ⊢ prodʷ p t u [conv↓] prodʷ p t′ u′ ∷ Σʷ p , q ▷ F ▹ G

    η-eq      : ∀ {f g F G}
              → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
              → Function f
              → Function g
              → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 [conv↑] wk1 g ∘⟨ p ⟩ var x0 ∷ G
              → Γ ⊢ f [conv↓] g ∷ Π p , q ▷ F ▹ G

    Σ-η       : ∀ {A B}
              → Γ ⊢ t₁ ∷ Σˢ p , q ▷ A ▹ B
              → Γ ⊢ t₂ ∷ Σˢ p , q ▷ A ▹ B
              → Product t₁
              → Product t₂
              → Γ ⊢ fst p t₁ [conv↑] fst p t₂ ∷ A
              → Γ ⊢ snd p t₁ [conv↑] snd p t₂ ∷ B [ fst p t₁ ]₀
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Σˢ p , q ▷ A ▹ B

    η-unit    : Γ ⊢ l ∷ Level
              → Γ ⊢ t₁ ∷ Unit s l
              → Γ ⊢ t₂ ∷ Unit s l
              → Whnf t₁
              → Whnf t₂
              → Unit-allowed s
              → Unit-with-η s
              → Γ ⊢ t₁ [conv↓] t₂ ∷ Unit s l

    Id-ins    : ∀ {A A′ t′ u′}
              → Γ ⊢ v₁ ∷ Id A t u
              → Γ ⊢ v₁ ~ v₂ ↓ Id A′ t′ u′
              → Γ ⊢ v₁ [conv↓] v₂ ∷ Id A t u

    rfl-refl  : ∀ {A}
              → Γ ⊢ t ≡ u ∷ A
              → Γ ⊢ rfl [conv↓] rfl ∷ Id A t u

-- An inversion lemma for prod-cong.

prod-cong⁻¹ :
  ∀ {t′ u′} →
  Γ ⊢ prodʷ p t u [conv↓] prodʷ p′ t′ u′ ∷ Σʷ p″ , q ▷ F ▹ G →
  p PE.≡ p′ ×
  p PE.≡ p″ ×
  Γ ∙ F ⊢ G ×
  (Γ ⊢ t [conv↑] t′ ∷ F) ×
  (Γ ⊢ u [conv↑] u′ ∷ G [ t ]₀) ×
  Σʷ-allowed p q
prod-cong⁻¹ (prod-cong G t u ok) =
  PE.refl , PE.refl , G , t , u , ok
prod-cong⁻¹ (Σʷ-ins _ _ ([~] _ _ ()))
prod-cong⁻¹ (ne-ins _ _ () _)

-- An inversion lemma for J-cong.

J-cong⁻¹ :
  Γ ⊢ J p₁ q₁ A₁ t₁ B₁ u₁ v₁ w₁ ~ J p₂ q₂ A₂ t₂ B₂ u₂ v₂ w₂ ↑ C →
  ∃ λ D →
  p₁ PE.≡ p₂ ×
  q₁ PE.≡ q₂ ×
  (Γ ⊢ A₁ [conv↑] A₂) ×
  Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ ×
  (Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂) ×
  Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀ ×
  Γ ⊢ v₁ [conv↑] v₂ ∷ A₁ ×
  Γ ⊢ w₁ ~ w₂ ↓ D ×
  Γ ⊢ D ≡ Id A₁ t₁ v₁ ×
  C PE.≡ B₁ [ v₁ , w₁ ]₁₀
J-cong⁻¹ (J-cong A t B u v w D) =
  _ , PE.refl , PE.refl , A , t , B , u , v , w , D , PE.refl

-- An inversion lemma for K-cong.

K-cong⁻¹ :
  Γ ⊢ K p₁ A₁ t₁ B₁ u₁ v₁ ~ K p₂ A₂ t₂ B₂ u₂ v₂ ↑ C →
  ∃ λ D →
  p₁ PE.≡ p₂ ×
  (Γ ⊢ A₁ [conv↑] A₂) ×
  Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ ×
  (Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂) ×
  Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀ ×
  Γ ⊢ v₁ ~ v₂ ↓ D ×
  Γ ⊢ D ≡ Id A₁ t₁ t₁ ×
  K-allowed ×
  C PE.≡ B₁ [ v₁ ]₀
K-cong⁻¹ (K-cong A t B u v D ok) =
  _ , PE.refl , A , t , B , u , v , D , ok , PE.refl
