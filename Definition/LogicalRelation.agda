{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening

open import Tools.Product
import Tools.PropositionalEquality as PE


-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_ (Γ : Con Term) (A : Term) : Set where
  constructor ne
  field
    K   : Term
    D   : Γ ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ ⊢ K ~ K ∷ U

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term) (A B : Term) ([A] : Γ ⊩ne A) : Set where
  constructor ne₌
  open _⊩ne_ [A]
  field
    M   : Term
    D′  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ U

-- Neutral term in WHNF
record _⊩neNf_∷_ (Γ : Con Term) (k A : Term) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A
    k≡k  : Γ ⊢ k ~ k ∷ A

-- Neutral term
record _⊩ne_∷_/_ (Γ : Con Term) (t A : Term) ([A] : Γ ⊩ne A) : Set where
  inductive
  constructor neₜ
  open _⊩ne_ [A]
  field
    k   : Term
    d   : Γ ⊢ t :⇒*: k ∷ K
    nf  : Γ ⊩neNf k ∷ K

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_ (Γ : Con Term) (k m A : Term) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A

-- Neutral term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩ne A) : Set where
  constructor neₜ₌
  open _⊩ne_ [A]
  field
    k m : Term
    d   : Γ ⊢ t :⇒*: k ∷ K
    d′  : Γ ⊢ u :⇒*: m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ

mutual
  -- Natural number term
  record _⊩ℕ_∷ℕ (Γ : Con Term) (t : Term) : Set where
    inductive
    constructor ℕₜ
    field
      n : Term
      d : Γ ⊢ t :⇒*: n ∷ ℕ
      n≡n : Γ ⊢ n ≅ n ∷ ℕ
      prop : Natural-prop Γ n

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ → Natural-prop Γ n

mutual
  -- Natural number term equality
  record _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    inductive
    constructor ℕₜ₌
    field
      k k′ : Term
      d : Γ ⊢ t :⇒*: k  ∷ ℕ
      d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ
      k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ
      prop : [Natural]-prop Γ k k′

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ n n′

-- Natural extraction from term WHNF property
natural : ∀ {Γ n} → Natural-prop Γ n → Natural n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {Γ a b} → [Natural]-prop Γ a b → Natural a × Natural b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Reducibility of Empty

-- Empty type
_⊩Empty_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩Empty A = Γ ⊢ A :⇒*: Empty

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty

-- WHNF property of absurd terms
data Empty-prop (Γ : Con Term) : (n : Term) → Set where
  ne    : ∀ {n} → Γ ⊩neNf n ∷ Empty → Empty-prop Γ n

-- Empty term
record _⊩Empty_∷Empty (Γ : Con Term) (t : Term) : Set where
  inductive
  constructor Emptyₜ
  field
    n : Term
    d : Γ ⊢ t :⇒*: n ∷ Empty
    n≡n : Γ ⊢ n ≅ n ∷ Empty
    prop : Empty-prop Γ n

data [Empty]-prop (Γ : Con Term) : (n n′ : Term) → Set where
  ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ n n′

-- Empty term equality
record _⊩Empty_≡_∷Empty (Γ : Con Term) (t u : Term) : Set where
  inductive
  constructor Emptyₜ₌
  field
    k k′ : Term
    d : Γ ⊢ t :⇒*: k  ∷ Empty
    d′ : Γ ⊢ u :⇒*: k′ ∷ Empty
    k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty
    prop : [Empty]-prop Γ k k′

empty : ∀ {Γ n} → Empty-prop Γ n → Neutral n
empty (ne (neNfₜ neK _ _)) = neK

esplit : ∀ {Γ a b} → [Empty]-prop Γ a b → Neutral a × Neutral b
esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- Reducibility of Unit

-- Unit type
_⊩Unit_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩Unit A = Γ ⊢ A :⇒*: Unit

-- Unit type equality
_⊩Unit_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩Unit A ≡ B = Γ ⊢ B ⇒* Unit

data Unit-prop (Γ : Con Term) : (n : Term) → Set where
  starᵣ : Unit-prop Γ star
  ne    : ∀ {n} → Γ ⊩neNf n ∷ Unit → Unit-prop Γ n

record _⊩Unit_∷Unit (Γ : Con Term) (t : Term) : Set where
  inductive
  constructor Unitₜ
  field
    n : Term
    d : Γ ⊢ t :⇒*: n ∷ Unit
    n≡n : Γ ⊢ n ≅ n ∷ Unit
    prop : Unit-prop Γ n

-- Unit term equality
record _⊩Unit_≡_∷Unit (Γ : Con Term) (t u : Term) : Set where
  inductive
  constructor Unitₜ₌
  field
    k k′ : Term
    d : Γ ⊢ t :⇒*: k  ∷ Unit
    d′ : Γ ⊢ u :⇒*: k′ ∷ Unit
    k≡k′ : Γ ⊢ k ≅ k′ ∷ Unit

unitary : ∀ {Γ n} → Unit-prop Γ n → Unitary n
unitary starᵣ = starₙ
unitary (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

-- Logical relation
-- Exported interface
record LogRelKit : Set₁ where
  constructor Kit
  field
    _⊩U : (Γ : Con Term) → Set
    _⊩Π_ : (Γ : Con Term) → Term → Set

    _⊩_ : (Γ : Con Term) → Term → Set
    _⊩_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩ A → Set
    _⊩_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩ A → Set
    _⊩_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩ A → Set

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩¹U (Γ : Con Term) : Set where
    constructor Uᵣ
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  _⊩¹U≡_ : (Γ : Con Term) (B : Term) → Set
  Γ ⊩¹U≡ B = B PE.≡ U -- Note lack of reduction

  -- Universe term
  record _⊩¹U_∷U/_ {l′} (Γ : Con Term) (t : Term) (l< : l′ < l) : Set where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term
      d     : Γ ⊢ t :⇒*: A ∷ U
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩¹U_≡_∷U/_ {l′} (Γ : Con Term) (t u : Term) (l< : l′ < l) : Set where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term
      d     : Γ ⊢ t :⇒*: A ∷ U
      d′    : Γ ⊢ u :⇒*: B ∷ U
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]

  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _⊩¹B⟨_⟩_ (Γ : Con Term) (W : Term → Term → Term) (A : Term) : Set where
      inductive
      constructor Bᵣ
      field
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: W F G
        ⊢F : Γ ⊢ F
        ⊢G : Γ ∙ F ⊢ G
        A≡A : Γ ⊢ W F G ≅ W F G
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ]
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]

    -- B-type equality
    record _⊩¹B⟨_⟩_≡_/_ (Γ : Con Term) (W : Term → Term → Term) (A B : Term) ([A] : Γ ⊩¹B⟨ W ⟩ A) : Set where
      inductive
      constructor B₌
      open _⊩¹B⟨_⟩_ [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* W F′ G′
        A≡B    : Γ ⊢ W F G ≅ W F′ G′
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _⊩¹Π_∷_/_ : (Γ : Con Term) (t A : Term) ([A] : Γ ⊩¹B⟨ Π_▹_ ⟩ A) → Set
    Γ ⊩¹Π t ∷ A / Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ▹ G
            × Function f
            × Γ ⊢ f ≅ f ∷ Π F ▹ G
            × (∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
            × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _⊩¹Π_≡_∷_/_ : (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩¹B⟨ Π_▹_ ⟩ A) → Set
    Γ ⊩¹Π t ≡ u ∷ A / Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      let [A] = Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      in  ∃₂ λ f g →
          Γ ⊢ t :⇒*: f ∷ Π F ▹ G
      ×   Γ ⊢ u :⇒*: g ∷ Π F ▹ G
      ×   Function f
      ×   Function g
      ×   Γ ⊢ f ≅ g ∷ Π F ▹ G
      ×   Γ ⊩¹Π t ∷ A / [A]
      ×   Γ ⊩¹Π u ∷ A / [A]
      ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
          → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.

    -- Term reducibility of Σ-type
    record _⊩¹Σ_∷_/_ (Γ : Con Term) (t A : Term) ([A] : Γ ⊩¹B⟨ Σ_▹_ ⟩ A) : Set where
      inductive
      constructor Σₜ
      open _⊩¹B⟨_⟩_ [A]
      field
        p : Term
        t⇒p : Γ ⊢ t :⇒*: p ∷ Σ F ▹ G
        pProd : Product p
        pRefl : Γ ⊢ p ≅ p ∷ Σ F ▹ G
        -- TODO extra stuff re projections?

    -- Term equality of Σ-type
    record _⊩¹Σ_≡_∷_/_ (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩¹B⟨ Σ_▹_ ⟩ A) : Set where
      inductive
      constructor Σₜ₌
      open _⊩¹B⟨_⟩_ [A]
      field
        p r : Term
        t⇒p : Γ ⊢ t :⇒*: p ∷ Σ F ▹ G
        u⇒r : Γ ⊢ u :⇒*: r ∷ Σ F ▹ G
        pProd : Product p
        rProd : Product r
        p≅r : Γ ⊢ p ≅ r ∷ Σ F ▹ G
        ⊩t : Γ ⊩¹Σ t ∷ A / [A]
        ⊩u : Γ ⊩¹Σ u ∷ A / [A]
        -- TODO extra stuff re projections?

    -- Logical relation definition

    data _⊩¹_ (Γ : Con Term) : Term → Set where
      Uᵣ  : Γ ⊩¹U → Γ ⊩¹ U
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩¹ A
      Unitᵣ : ∀ {A} → Γ ⊩Unit A → Γ ⊩¹ A
      ne  : ∀ {A} → Γ ⊩ne A → Γ ⊩¹ A
      Πᵣ  : ∀ {A} → Γ ⊩¹B⟨ Π_▹_ ⟩ A → Γ ⊩¹ A
      Σᵣ  : ∀ {A} → Γ ⊩¹B⟨ Σ_▹_ ⟩ A → Γ ⊩¹ A
      emb : ∀ {A l′} (l< : l′ < l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A) → Γ ⊩¹ A

    _⊩¹_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ A ≡ B / Uᵣ UA = Γ ⊩¹U≡ B
    Γ ⊩¹ A ≡ B / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩¹ A ≡ B / Unitᵣ D = Γ ⊩Unit A ≡ B
    Γ ⊩¹ A ≡ B / ne neA = Γ ⊩ne A ≡ B / neA
    Γ ⊩¹ A ≡ B / Πᵣ ΠA = Γ ⊩¹B⟨ Π_▹_ ⟩ A ≡ B / ΠA
    Γ ⊩¹ A ≡ B / Σᵣ ΣA = Γ ⊩¹B⟨ Σ_▹_ ⟩ A ≡ B / ΣA
    Γ ⊩¹ A ≡ B / emb l< [A] = Γ ⊩ A ≡ B / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ t ∷ .U / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ∷U/ l<
    Γ ⊩¹ t ∷ A / ℕᵣ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A / Emptyᵣ D = Γ ⊩Empty t ∷Empty
    Γ ⊩¹ t ∷ A / Unitᵣ D = Γ ⊩Unit t ∷Unit
    Γ ⊩¹ t ∷ A / ne neA = Γ ⊩ne t ∷ A / neA
    Γ ⊩¹ t ∷ A / Πᵣ ΠA  = Γ ⊩¹Π t ∷ A / ΠA
    Γ ⊩¹ t ∷ A / Σᵣ ΣA  = Γ ⊩¹Σ t ∷ A / ΣA
    Γ ⊩¹ t ∷ A / emb l< [A] = Γ ⊩ t ∷ A / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩¹ A → Set
    Γ ⊩¹ t ≡ u ∷ .U / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ≡ u ∷U/ l<
    Γ ⊩¹ t ≡ u ∷ A / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩¹ t ≡ u ∷ A / Unitᵣ D = Γ ⊩Unit t ≡ u ∷Unit
    Γ ⊩¹ t ≡ u ∷ A / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩¹ t ≡ u ∷ A / Πᵣ ΠA = Γ ⊩¹Π t ≡ u ∷ A / ΠA
    Γ ⊩¹ t ≡ u ∷ A / Σᵣ ΣA  = Γ ⊩¹Σ t ≡ u ∷ A / ΣA
    Γ ⊩¹ t ≡ u ∷ A / emb l< [A] = Γ ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U _⊩¹B⟨ Π_▹_ ⟩_
              _⊩¹_ _⊩¹_≡_/_ _⊩¹_∷_/_ _⊩¹_≡_∷_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Πᵣ; Σᵣ; Bᵣ; B₌; Σₜ; Σₜ₌; emb; Uₜ; Uₜ₌)

-- Patterns for the non-records of Π
pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]

pattern Uᵣ′ a b c = Uᵣ (Uᵣ a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Πᵣ′ a b c d e f g h i = Πᵣ (Bᵣ a b c d e f g h i)
pattern Σᵣ′ a b c d e f g h i = Σᵣ (Bᵣ a b c d e f g h i)

logRelRec : ∀ l {l′} → l′ < l → LogRelKit
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l = LogRel.kit l (logRelRec l)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_⊩′⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩′⟨ l ⟩U = Γ ⊩U where open LogRelKit (kit l)

_⊩′⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) → Term → Set
Γ ⊩′⟨ l ⟩Π A = Γ ⊩Π A where open LogRelKit (kit l)

_⊩⟨_⟩_ : (Γ : Con Term) (l : TypeLevel) → Term → Set
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

_⊩⟨_⟩_≡_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) → Γ ⊩⟨ l ⟩ A → Set
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) → Γ ⊩⟨ l ⟩ A → Set
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) → Γ ⊩⟨ l ⟩ A → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)
