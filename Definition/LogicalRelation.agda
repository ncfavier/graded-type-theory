------------------------------------------------------------------------
-- The logical relation for reducibility
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (K)
open import Definition.Untyped.Neutral Mod type-variant
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R

open import Tools.Empty
open import Tools.Function
open import Tools.Level hiding (Level; _⊔_)
open import Tools.Nat hiding (_<_; _≤_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private
  variable
    p q : Mod
    ℓ : Nat
    l : Universe-level
    Γ Δ : Con Term ℓ
    t t′ u u′ : Term _
    ρ : Wk _ _
    s : Strength

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_ {ℓ : Nat} (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
  constructor ne
  field
    K   : Term ℓ
    D   : Γ ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ ⊢ K ≅ K

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term ℓ) (A B : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  constructor ne₌
  open _⊩ne_ [A]
  field
    M   : Term ℓ
    D′  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ≅ M

-- Neutral term in WHNF
record _⊩neNf_∷_ (Γ : Con Term ℓ) (k A : Term ℓ) : Set a where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A
    k≡k  : Γ ⊢ k ~ k ∷ A

-- Neutral term
record _⊩ne_∷_/_ (Γ : Con Term ℓ) (t A : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  inductive
  constructor neₜ
  open _⊩ne_ [A]
  field
    k   : Term ℓ
    d   : Γ ⊢ t :⇒*: k ∷ K
    nf  : Γ ⊩neNf k ∷ K

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_ (Γ : Con Term ℓ) (k m A : Term ℓ) : Set a where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A

-- Neutral term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  constructor neₜ₌
  open _⊩ne_ [A]
  field
    k m : Term ℓ
    d   : Γ ⊢ t :⇒*: k ∷ K
    d′  : Γ ⊢ u :⇒*: m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K

-- Reducibility of levels:

-- Level type
_⊩Level_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩Level A = Γ ⊢ A :⇒*: Level

-- Level type equality
_⊩Level_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩Level A ≡ B = Γ ⊢ B ⇒* Level

mutual
  -- Level term
  record _⊩Level_∷Level (Γ : Con Term ℓ) (t : Term ℓ) : Set a where
    inductive
    constructor Levelₜ
    field
      m : Term ℓ
      d : Γ ⊢ t :⇒*: m ∷ Level
      m≡m : Γ ⊢ m ≅ m ∷ Level
      prop : Level-prop Γ m

  -- WHNF property of level terms
  data Level-prop (Γ : Con Term ℓ) : (l : Term ℓ) → Set a where
    zeroᵘᵣ : Level-prop Γ zeroᵘ
    sucᵘᵣ  : ∀ {l} → Γ ⊩Level l ∷Level → Level-prop Γ (sucᵘ l)
    ne     : ∀ {l} → Γ ⊩neNf l ∷ Level → Level-prop Γ l

mutual
  -- Level term equality
  record _⊩Level_≡_∷Level (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
    inductive
    constructor Levelₜ₌
    field
      k k′ : Term ℓ
      d : Γ ⊢ t :⇒*: k ∷ Level
      d′ : Γ ⊢ u :⇒*: k′ ∷ Level
      k≡k′ : Γ ⊢ k ≅ k′ ∷ Level
      prop : [Level]-prop Γ k k′

  -- WHNF property of level term equality
  data [Level]-prop (Γ : Con Term ℓ) : (k k′ : Term ℓ) → Set a where
    zeroᵘᵣ : [Level]-prop Γ zeroᵘ zeroᵘ
    sucᵘᵣ  : ∀ {k k′} → Γ ⊩Level k ≡ k′ ∷Level → [Level]-prop Γ (sucᵘ k) (sucᵘ k′)
    ne     : ∀ {k k′} → Γ ⊩neNf k ≡ k′ ∷ Level → [Level]-prop Γ k k′

mutual
  _⊩_≤ᵘ_ : (Γ : Con Term ℓ) → ∀ {l′} ([l′] : Γ ⊩Level l′ ∷Level) (l : Universe-level) → Set a
  Γ ⊩ [l′] ≤ᵘ l = Γ ⊩ [l′] ._⊩Level_∷Level.prop ≤ᵘ′ l

  data _⊩_≤ᵘ′_ (Γ : Con Term ℓ) : ∀ {l′} (prop : Level-prop Γ l′) (l : Universe-level) → Set a where
    ≤ᵘ-ne : ∀ {l l′} ([l′] : Γ ⊩neNf l′ ∷ Level) → Γ ⊩ ne [l′] ≤ᵘ′ l
    ≤ᵘ-zeroᵘ : ∀ {l} → Γ ⊩ zeroᵘᵣ ≤ᵘ′ l
    ≤ᵘ-sucᵘ : ∀ {l l′} {[l′] : Γ ⊩Level l′ ∷Level} → Γ ⊩ [l′] ≤ᵘ l → Γ ⊩ sucᵘᵣ [l′] ≤ᵘ′ 1+ l

_⊩_<ᵘ_ : (Γ : Con Term ℓ) → ∀ {l′} ([l′] : Γ ⊩Level l′ ∷Level) (l : Universe-level) → Set a
Γ ⊩ [l′] <ᵘ l = Γ ⊩ sucᵘᵣ [l′] ≤ᵘ′ l

mutual
  _⊩_≡ᵘ_ : (Γ : Con Term ℓ) → ∀ {l′} ([l′] : Γ ⊩Level l′ ∷Level) (l : Universe-level) → Set a
  Γ ⊩ [l′] ≡ᵘ l = Γ ⊩ [l′] ._⊩Level_∷Level.prop ≡ᵘ′ l

  data _⊩_≡ᵘ′_ (Γ : Con Term ℓ) : ∀ {l′} (prop : Level-prop Γ l′) (l : Universe-level) → Set a where
    ≡ᵘ-ne : ∀ {l′} ([l′] : Γ ⊩neNf l′ ∷ Level) → Γ ⊩ ne [l′] ≡ᵘ′ 0
    ≡ᵘ-zeroᵘ : Γ ⊩ zeroᵘᵣ ≡ᵘ′ 0
    ≡ᵘ-sucᵘ : ∀ {l l′} {[l′] : Γ ⊩Level l′ ∷Level} → Γ ⊩ [l′] ≡ᵘ l → Γ ⊩ sucᵘᵣ [l′] ≡ᵘ′ 1+ l

-- mutual
--   reflect-level : Γ ⊩Level t ∷Level → Universe-level
--   reflect-level [t] = reflect-level-prop ([t] ._⊩Level_∷Level.prop)

--   reflect-level-prop : Level-prop Γ t → Universe-level
--   reflect-level-prop zeroᵘᵣ = 0
--   reflect-level-prop (sucᵘᵣ x) = 1+ (reflect-level x)
--   reflect-level-prop (ne x) = 0

-- mutual
--   _⊩_<ᵘ_ : (Γ : Con Term ℓ) → ∀ {l′} ([l′] : Γ ⊩Level l′ ∷Level) (l : Universe-level) → Set a
--   Γ ⊩ [l′] <ᵘ l = Γ ⊩ [l′] ._⊩Level_∷Level.prop <ᵘ′ l

--   data _⊩_<ᵘ′_ (Γ : Con Term ℓ) : ∀ {l′} (prop : Level-prop Γ l′) (l : Universe-level) → Set a where
--     zeroᵘ-<ᵘ : ∀ {n} → Γ ⊩ zeroᵘᵣ <ᵘ′ lnat (1+ n)
--     sucᵘ-<ᵘ
--       : ∀ {n l} {[l] : Γ ⊩Level l ∷Level}
--       → Γ ⊩ [l] <ᵘ lnat n
--       → Γ ⊩ sucᵘᵣ [l] <ᵘ′ lnat (1+ n)
--     <ᵘ-lω : ∀ {l′} {[l′] : Level-prop Γ l′} → Γ ⊩ [l′] <ᵘ′ lω

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ

mutual
  -- Natural number term
  record _⊩ℕ_∷ℕ (Γ : Con Term ℓ) (t : Term ℓ) : Set a where
    inductive
    constructor ℕₜ
    field
      n : Term ℓ
      d : Γ ⊢ t :⇒*: n ∷ ℕ
      n≡n : Γ ⊢ n ≅ n ∷ ℕ
      prop : Natural-prop Γ n

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term ℓ) : (n : Term ℓ) → Set a where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ → Natural-prop Γ n

mutual
  -- Natural number term equality
  record _⊩ℕ_≡_∷ℕ (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
    inductive
    constructor ℕₜ₌
    field
      k k′ : Term ℓ
      d : Γ ⊢ t :⇒*: k  ∷ ℕ
      d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ
      k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ
      prop : [Natural]-prop Γ k k′

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term ℓ) : (n n′ : Term ℓ) → Set a where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ n n′

-- Reducibility of Empty

-- Empty type
_⊩Empty_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩Empty A = Γ ⊢ A :⇒*: Empty

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty

-- WHNF property of absurd terms
data Empty-prop (Γ : Con Term ℓ) : (n : Term ℓ) → Set a where
  ne    : ∀ {n} → Γ ⊩neNf n ∷ Empty → Empty-prop Γ n

-- Empty term
record _⊩Empty_∷Empty (Γ : Con Term ℓ) (t : Term ℓ) : Set a where
  inductive
  constructor Emptyₜ
  field
    n : Term ℓ
    d : Γ ⊢ t :⇒*: n ∷ Empty
    n≡n : Γ ⊢ n ≅ n ∷ Empty
    prop : Empty-prop Γ n

data [Empty]-prop (Γ : Con Term ℓ) : (n n′ : Term ℓ) → Set a where
  ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ n n′

-- Empty term equality
record _⊩Empty_≡_∷Empty (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
  inductive
  constructor Emptyₜ₌
  field
    k k′ : Term ℓ
    d : Γ ⊢ t :⇒*: k  ∷ Empty
    d′ : Γ ⊢ u :⇒*: k′ ∷ Empty
    k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty
    prop : [Empty]-prop Γ k k′

-- Reducibility of Unit

-- Unit type
record _⊩Unit⟨_,_⟩_
  (Γ : Con Term ℓ) (l : Universe-level) (s : Strength) (A : Term ℓ) :
  Set a where
  no-eta-equality
  pattern
  constructor Unitₜ
  field
    l′ : Term ℓ
    [l′] : Γ ⊩Level l′ ∷Level
    l′<  : Γ ⊩ [l′] ≤ᵘ l
    ⇒*-Unit : Γ ⊢ A :⇒*: Unit s l′
    ok      : Unit-allowed s

-- Unit type equality
_⊩Unit⟨_,_⟩_≡_/_ :
  (Γ : Con Term ℓ) → (l : Universe-level) → (s : Strength) → (A B : Term ℓ) → Γ ⊩Unit⟨ l , s ⟩ A → Set a
Γ ⊩Unit⟨ l , s ⟩ A ≡ B / [A] = Γ ⊢ B ⇒* Unit s ([A] ._⊩Unit⟨_,_⟩_.l′)

data Unit-prop
  (Γ : Con Term ℓ) (l : Universe-level) (s : Strength) (A : Term ℓ) ([A] : Γ ⊩Unit⟨ l , s ⟩ A) :
  Term ℓ → Set a where
  starᵣ : Unit-prop Γ l s A [A] (star s ([A] ._⊩Unit⟨_,_⟩_.l′))
  ne : ∀ {n} → Γ ⊩neNf n ∷ Unit s ([A] ._⊩Unit⟨_,_⟩_.l′) → Unit-prop Γ l s A [A] n

record _⊩Unit⟨_,_⟩_∷_/_
  (Γ : Con Term ℓ) (l : Universe-level) (s : Strength) (t : Term ℓ) (A : Term ℓ) ([A] : Γ ⊩Unit⟨ l , s ⟩ A) :
  Set a where
  inductive
  constructor Unitₜ
  open _⊩Unit⟨_,_⟩_ [A]
  field
    n : Term ℓ
    d : Γ ⊢ t :⇒*: n ∷ Unit s l′
    n≡n : Γ ⊢ n ≅ n ∷ Unit s l′
    prop : Unit-prop Γ l s A [A] n

-- Unit term equality

data [Unitʷ]-prop
  (Γ : Con Term ℓ) (l : Universe-level) (A : Term ℓ) ([A] : Γ ⊩Unit⟨ l , 𝕨 ⟩ A) : (_ _ : Term ℓ) → Set a where
  starᵣ : [Unitʷ]-prop Γ l A [A] (starʷ ([A] ._⊩Unit⟨_,_⟩_.l′)) (starʷ ([A] ._⊩Unit⟨_,_⟩_.l′))
  ne : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Unit 𝕨 ([A] ._⊩Unit⟨_,_⟩_.l′) → [Unitʷ]-prop Γ l A [A] n n′

data _⊩Unit⟨_,_⟩_≡_∷_/_
  (Γ : Con Term ℓ) (l : Universe-level) : (s : Strength) (t u : Term ℓ) (A : Term ℓ) ([A] : Γ ⊩Unit⟨ l , s ⟩ A) → Set a where
  Unitₜ₌ˢ :
    ∀ {A} {[A]} (open _⊩Unit⟨_,_⟩_ [A]) →
    Γ ⊢ t ∷ Unit s l′ →
    Γ ⊢ u ∷ Unit s l′ →
    Unit-with-η s →
    Γ ⊩Unit⟨ l , s ⟩ t ≡ u ∷ A / [A]
  Unitₜ₌ʷ :
    ∀ {A} {[A]} (open _⊩Unit⟨_,_⟩_ [A]) →
    (k k′ : Term ℓ) →
    Γ ⊢ t :⇒*: k  ∷ Unitʷ l′ →
    Γ ⊢ u :⇒*: k′ ∷ Unitʷ l′ →
    Γ ⊢ k ≅ k′ ∷ Unitʷ l′ →
    [Unitʷ]-prop Γ l A [A] k k′ →
    ¬ Unitʷ-η →
    Γ ⊩Unit⟨ l , 𝕨 ⟩ t ≡ u ∷ A / [A]

-- Logical relation
-- Exported interface
record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    _⊩U_ : Con Term ℓ → Term ℓ → Set a
    _⊩B⟨_⟩_ : (Γ : Con Term ℓ) (W : BindingType) → Term ℓ → Set a
    _⊩Id_ : Con Term ℓ → Term ℓ → Set a

    _⊩_ : (Γ : Con Term ℓ) → Term ℓ → Set a
    _⊩_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ A → Set a
    _⊩_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ A → Set a
    _⊩_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ A → Set a

module LogRel
  (l : Universe-level) (rec : ∀ {l′} → l′ <ᵘ l → LogRelKit)
  where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩₁U_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
    constructor Uᵣ
    field
      l′  : Universe-level
      l′< : l′ <ᵘ l
      k   : Term ℓ
      [k] : Γ ⊩Level k ∷Level
      k≤  : Γ ⊩ [k] ≡ᵘ l′
      ⇒*U : Γ ⊢ A :⇒*: U k

  -- Universe type equality
  _⊩₁U≡_/_ : Con Term ℓ → Term ℓ → Term ℓ → Set a
  Γ ⊩₁U≡ B / l′ = Γ ⊢ B :⇒*: U l′


  -- Universe term
  record _⊩₁U_∷U/_
           {T} (Γ : Con Term ℓ) (t : Term ℓ) ([T] : Γ ⊩₁U T) :
           Set a where
    constructor Uₜ
    open _⊩₁U_ [T]
    open LogRelKit (rec l′<)
    field
      A     : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U k
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U k
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩₁U_≡_∷U/_
           {T} (Γ : Con Term ℓ) (t u : Term ℓ) ([T] : Γ ⊩₁U T) :
           Set a where
    constructor Uₜ₌
    open _⊩₁U_ [T]
    open LogRelKit (rec l′<)
    field
      A B   : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U k
      d′    : Γ ⊢ u :⇒*: B ∷ U k
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U k
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]



  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _⊩ₗB⟨_⟩_ (Γ : Con Term ℓ) (W : BindingType) (A : Term ℓ) : Set a where
      inductive
      constructor Bᵣ
      eta-equality
      field
        F : Term ℓ
        G : Term (1+ ℓ)
        D : Γ ⊢ A :⇒*: ⟦ W ⟧ F ▹ G
        ⊢F : Γ ⊢ F
        ⊢G : Γ ∙ F ⊢ G
        A≡A : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊩ₗ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G [ b ]₀ / [G] [ρ] ⊢Δ [a]
        ok : BindingType-allowed W

    -- B-type equality
    record _⊩ₗB⟨_⟩_≡_/_ (Γ : Con Term ℓ) (W : BindingType) (A B : Term ℓ) ([A] : Γ ⊩ₗB⟨ W ⟩ A) : Set a where
      inductive
      constructor B₌
      eta-equality
      open _⊩ₗB⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ ⊢ B :⇒*: ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩ₗ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G′ [ a ]₀ / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _⊩ₗΠ_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_∷_/_ {ℓ} {p} {q} Γ t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
            × Function f
            × Γ ⊢ f ≅ f ∷ Π p , q ▷ F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ f ∘⟨ p ⟩ b ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _⊩ₗΠ_≡_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_≡_∷_/_
      {ℓ} {p} {q} Γ t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ f g → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
               × Γ ⊢ u :⇒*: g ∷ Π p , q ▷ F ▹ G
               × Function f
               × Function g
               × Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G
               × Γ ⊩ₗΠ t ∷ A / [A]
               × Γ ⊩ₗΠ u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                 → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ g ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _⊩ₗΣ_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_∷_/_
      {p = p} {q = q} {m = m} Γ t A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ u → Γ ⊢ t :⇒*: u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Γ ⊢ u ≅ u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Σ (Product u) λ pProd
            → Σ-prop m u Γ [A] pProd

    Σ-prop : ∀ {A p q} (m : Strength) (t : Term ℓ) → (Γ : Con Term ℓ)
           → ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → (Product t) → Set a
    Σ-prop {p = p} 𝕤 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst] →
      Γ ⊩ₗ snd p t ∷ U.wk (lift id) G [ fst p t ]₀ /
        [G] id (wf ⊢F) [fst]
    Σ-prop
      {p = p} 𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂} {m = m}) =
           p PE.≡ p′ ×
           Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁]
           → Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁]
           × m PE.≡ 𝕨
    Σ-prop
      {p = p} {q = q}
      𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) =
      Γ ⊢ t ~ t ∷ Σʷ p , q ▷ F ▹ G

    -- Term equality of Σ-type
    _⊩ₗΣ_≡_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t u A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_≡_∷_/_
      {p = p} {q = q} {m} Γ t u A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ t′ u′ → Γ ⊢ t :⇒*: t′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ u :⇒*: u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ t′ ≅ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊩ₗΣ t ∷ A / [A]
                 × Γ ⊩ₗΣ u ∷ A / [A]
                 × Σ (Product t′) λ pProd
                 → Σ (Product u′) λ rProd
                 → [Σ]-prop m t′ u′ Γ [A] pProd rProd

    [Σ]-prop :
      ∀ {A p q} (m : Strength) (t r : Term ℓ) (Γ : Con Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Product t → Product r → Set a
    [Σ]-prop {p = p} 𝕤 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
      → Γ ⊩ₗ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ fst p t ≡ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ snd p t ≡ snd p r ∷ U.wk (lift id) G [ fst p t ]₀
        / [G] id (wf ⊢F) [fstp]
    [Σ]-prop
      {p = p} 𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂})
      (prodₙ {p = p″} {t = r₁} {u = r₂}) =
             p PE.≡ p′ × p PE.≡ p″ ×
             Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁] →
             Σ (Γ ⊩ₗ r₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [r₁]
             → (Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
             × (Γ ⊩ₗ r₂ ∷ U.wk (lift id) G [ r₁ ]₀ / [G] id (wf ⊢F) [r₁])
             × (Γ ⊩ₗ p₁ ≡ r₁ ∷ U.wk id F / [F] id (wf ⊢F))
             × (Γ ⊩ₗ p₂ ≡ r₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {t = p₁} {u = p₂}) (ne y) =
      Lift a ⊥
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
      (ne x) (prodₙ {t = r₁} {u = r₂}) =
      Lift a ⊥
    [Σ]-prop
      {p = p} {q = q} 𝕨 t r Γ
      (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) (ne y) =
        Γ ⊢ t ~ r ∷ Σʷ p , q ▷ F ▹ G

    -- Reducibility for identity types.

    -- Well-formed identity types.
    record _⊩ₗId_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
      inductive
      constructor Idᵣ
      eta-equality
      field
        Ty lhs rhs : Term ℓ
        ⇒*Id       : Γ ⊢ A :⇒*: Id Ty lhs rhs
        ⊩Ty        : Γ ⊩ₗ Ty
        ⊩lhs       : Γ ⊩ₗ lhs ∷ Ty / ⊩Ty
        ⊩rhs       : Γ ⊩ₗ rhs ∷ Ty / ⊩Ty

    -- Well-formed identity type equality.
    record _⊩ₗId_≡_/_
      (Γ : Con Term ℓ) (A B : Term ℓ) (⊩A : Γ ⊩ₗId A) : Set a where
      inductive
      constructor Id₌
      eta-equality

      open _⊩ₗId_ ⊩A

      field
        Ty′ lhs′ rhs′ : Term ℓ
        ⇒*Id′         : Γ ⊢ B :⇒*: Id Ty′ lhs′ rhs′
        Ty≡Ty′        : Γ ⊩ₗ Ty ≡ Ty′ / ⊩Ty
        lhs≡lhs′      : Γ ⊩ₗ lhs ≡ lhs′ ∷ Ty / ⊩Ty
        rhs≡rhs′      : Γ ⊩ₗ rhs ≡ rhs′ ∷ Ty / ⊩Ty

        -- The fact that the types of the following two fields are
        -- inhabited follows from symmetry, transitivity and the
        -- previous two fields, see
        -- Definition.LogicalRelation.Properties.Transitivity.Id₌′.
        -- The fields are used in
        -- Definition.LogicalRelation.Properties.Conversion, which is
        -- imported from
        -- Definition.LogicalRelation.Properties.Transitivity.
        lhs≡rhs→lhs′≡rhs′ : Γ ⊩ₗ lhs  ≡ rhs  ∷ Ty / ⊩Ty →
                            Γ ⊩ₗ lhs′ ≡ rhs′ ∷ Ty / ⊩Ty
        lhs′≡rhs′→lhs≡rhs : Γ ⊩ₗ lhs′ ≡ rhs′ ∷ Ty / ⊩Ty →
                            Γ ⊩ₗ lhs  ≡ rhs  ∷ Ty / ⊩Ty

    -- Well-formed identity terms.
    _⊩ₗId_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗId A → Set a
    Γ ⊩ₗId t ∷ A / ⊩A =
      ∃ λ u →
      Γ ⊢ t :⇒*: u ∷ Id Ty lhs rhs ×
      ∃ λ (u-id : Identity u) →
      case u-id of λ where
        (ne _) → Γ ⊢ u ~ u ∷ Id Ty lhs rhs
        rflₙ   → Γ ⊩ₗ lhs ≡ rhs ∷ Ty / ⊩Ty
      where
      open _⊩ₗId_ ⊩A

    -- Well-formed identity term equality.
    _⊩ₗId_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗId A → Set a
    Γ ⊩ₗId t ≡ u ∷ A / ⊩A =
      ∃₂ λ t′ u′ →
      Γ ⊢ t :⇒*: t′ ∷ Id Ty lhs rhs ×
      Γ ⊢ u :⇒*: u′ ∷ Id Ty lhs rhs ×
      ∃ λ (t′-id : Identity t′) →
      ∃ λ (u′-id : Identity u′) →
      Identity-rec t′-id
        (Identity-rec u′-id
           (Γ ⊩ₗ lhs ≡ rhs ∷ Ty / ⊩Ty)
           (Lift _ ⊥))
        (Identity-rec u′-id
           (Lift _ ⊥)
           (Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs))
      where
      open _⊩ₗId_ ⊩A

    -- Logical relation definition
    data _⊩ₗ_ (Γ : Con Term ℓ) : Term ℓ → Set a where
      Levelᵣ : ∀ {A} → Γ ⊩Level A → Γ ⊩ₗ A
      Uᵣ  : ∀ {A} → Γ ⊩₁U A → Γ ⊩ₗ A
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩ₗ A
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩ₗ A
      Unitᵣ : ∀ {A} {s : Strength} → Γ ⊩Unit⟨ l , s ⟩ A → Γ ⊩ₗ A
      ne  : ∀ {A} → Γ ⊩ne A → Γ ⊩ₗ A
      Bᵣ  : ∀ {A} W → Γ ⊩ₗB⟨ W ⟩ A → Γ ⊩ₗ A
      Idᵣ : ∀ {A} → Γ ⊩ₗId A → Γ ⊩ₗ A
      emb : ∀ {A l′} (l< : l′ <ᵘ l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A) → Γ ⊩ₗ A

    _⊩ₗ_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ A ≡ B / Levelᵣ D = Γ ⊩Level A ≡ B
    Γ ⊩ₗ A ≡ B / Uᵣ D = Γ ⊩₁U≡ B / D ._⊩₁U_.k
    Γ ⊩ₗ A ≡ B / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩ₗ A ≡ B / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩ₗ A ≡ B / Unitᵣ {s = s} D = Γ ⊩Unit⟨ l , s ⟩ A ≡ B / D
    Γ ⊩ₗ A ≡ B / ne neA = Γ ⊩ne A ≡ B / neA
    Γ ⊩ₗ A ≡ B / Bᵣ W BA = Γ ⊩ₗB⟨ W ⟩ A ≡ B / BA
    Γ ⊩ₗ A ≡ B / Idᵣ ⊩A = Γ ⊩ₗId A ≡ B / ⊩A
    Γ ⊩ₗ A ≡ B / emb l< [A] = Γ ⊩ A ≡ B / [A]
      where open LogRelKit (rec l<)

    _⊩ₗ_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ∷ A / Levelᵣ D = Γ ⊩Level t ∷Level
    Γ ⊩ₗ t ∷ A / Uᵣ p = Γ ⊩₁U t ∷U/ p
    Γ ⊩ₗ t ∷ A / ℕᵣ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩ₗ t ∷ A / Emptyᵣ D = Γ ⊩Empty t ∷Empty
    Γ ⊩ₗ t ∷ A / Unitᵣ {s = s} D = Γ ⊩Unit⟨ l , s ⟩ t ∷ A / D
    Γ ⊩ₗ t ∷ A / ne neA = Γ ⊩ne t ∷ A / neA
    Γ ⊩ₗ t ∷ A / Bᵣ BΠ! ΠA  = Γ ⊩ₗΠ t ∷ A / ΠA
    Γ ⊩ₗ t ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ∷ A / ΣA
    Γ ⊩ₗ t ∷ A / Idᵣ ⊩A = Γ ⊩ₗId t ∷ A / ⊩A
    Γ ⊩ₗ t ∷ A / emb l< [A] = Γ ⊩ t ∷ A / [A]
      where open LogRelKit (rec l<)

    _⊩ₗ_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ≡ u ∷ A / Levelᵣ D = Γ ⊩Level t ≡ u ∷Level
    Γ ⊩ₗ t ≡ u ∷ A / Uᵣ p = Γ ⊩₁U t ≡ u ∷U/ p
    Γ ⊩ₗ t ≡ u ∷ A / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩ₗ t ≡ u ∷ A / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩ₗ t ≡ u ∷ A / Unitᵣ {s = s} D = Γ ⊩Unit⟨ l , s ⟩ t ≡ u ∷ A / D
    Γ ⊩ₗ t ≡ u ∷ A / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΠ! ΠA = Γ ⊩ₗΠ t ≡ u ∷ A / ΠA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ≡ u ∷ A / ΣA
    Γ ⊩ₗ t ≡ u ∷ A / Idᵣ ⊩A = Γ ⊩ₗId t ≡ u ∷ A / ⊩A
    Γ ⊩ₗ t ≡ u ∷ A / emb l< [A] = Γ ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩₁U_ _⊩ₗB⟨_⟩_ _⊩ₗId_
              _⊩ₗ_ _⊩ₗ_≡_/_ _⊩ₗ_∷_/_ _⊩ₗ_≡_∷_/_

open LogRel public
  using
    (Levelᵣ; Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Bᵣ; B₌; Idᵣ; Id₌; emb; Uₜ; Uₜ₌;
     module _⊩₁U_; module _⊩₁U_∷U/_; module _⊩₁U_≡_∷U/_;
     module _⊩ₗB⟨_⟩_; module _⊩ₗB⟨_⟩_≡_/_;
     module _⊩ₗId_; module _⊩ₗId_≡_/_)

-- Patterns for the non-records of Π
pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]
pattern Σₜ p d p≡p pProd prop =  p , d , p≡p , pProd , prop
pattern Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] prop = p , r , d , d′ , p≅r , [t] , [u] , pProd , rProd , prop

pattern Uᵣ′ a b c d e f = Uᵣ (Uᵣ a b c d e f)
pattern ne′ a b c d = ne (ne a b c d)
pattern Bᵣ′ W a b c d e f g h i j = Bᵣ W (Bᵣ a b c d e f g h i j)
pattern Πᵣ′ a b c d e f g h i j = Bᵣ′ BΠ! a b c d e f g h i j
pattern 𝕨′ a b c d e f g h i j = Bᵣ′ BΣ! a b c d e f g h i j

mutual

  -- A LogRelKit for the first Universe-level.

  -- kit0 : LogRelKit
  -- kit0 = LogRel.kit 0 (λ ())

  -- A LogRelKit for the given Universe-level.

  kit : Universe-level → LogRelKit
  kit l = LogRel.kit l kit′
  -- kit (lnat n) = LogRel.kit (lnat n) (λ {_} {_} {_} {[l′]} → kit′ {n = n} {[m] = [l′]})
  -- kit lω = LogRel.kit lω λ {_} {_} {_} {[l′]} → kitω {[m] = [l′]}

  -- A LogRelKit for m.

  kit′ : {n m : Universe-level} → m <ᵘ n → LogRelKit
  -- kit′ (≤ᵘ-sucᵘ (≤ᵘ-ne [l′])) = kit0
  -- kit′ (≤ᵘ-sucᵘ ≤ᵘ-zeroᵘ) = kit0
  -- kit′ (≤ᵘ-sucᵘ (≤ᵘ-sucᵘ {[l′]} x)) = kit′ {[m] = [l′]} (≤ᵘ-sucᵘ x)
  kit′ {m = m} ≤′-refl = kit m
  kit′ (≤′-step m<n) = kit′ m<n

  -- kit′ {.(1+ᵘ ⟦ [m] ⟧ᵘ)} {[m]} (≤ᵘ-refl .(sucᵘᵣ _)) = kit ⟦ [m] ⟧ᵘ
  -- kit′ {(n)} (≤ᵘ-suc _ m<n) = kit′ m<n

  -- kit′ {(1+ n)} zeroᵘ-<ᵘ = kit0
  -- kit′ {(1+ n)} (sucᵘ-<ᵘ {[l]} m<n) = kit′ {n} {[m] = [l]} m<n

  -- kitω : ∀ {ℓ} {Γ : Con Term ℓ} {m} {[m] : Γ ⊩Level m ∷Level} → Γ ⊩ [m] <ᵘ lω → LogRelKit
  -- kitω <ᵘ-lω = {!   !}

_⊩′⟨_⟩U_ : Con Term ℓ → Universe-level → Term ℓ → Set a
Γ ⊩′⟨ l ⟩U A = Γ ⊩U A where open LogRelKit (kit l)

_⊩′⟨_⟩B⟨_⟩_ : Con Term ℓ → Universe-level → BindingType → Term ℓ → Set a
Γ ⊩′⟨ l ⟩B⟨ W ⟩ A = Γ ⊩B⟨ W ⟩ A where open LogRelKit (kit l)

_⊩′⟨_⟩Id_ : Con Term ℓ → Universe-level → Term ℓ → Set a
Γ ⊩′⟨ l ⟩Id A = Γ ⊩Id A
  where
  open LogRelKit (kit l)

-- Reducibility of types

_⊩⟨_⟩_ : Con Term ℓ → Universe-level → Term ℓ → Set a
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

-- Equality of reducibile types

_⊩⟨_⟩_≡_/_ :
  (Γ : Con Term ℓ) (l : Universe-level) (A _ : Term ℓ) → Γ ⊩⟨ l ⟩ A →
  Set a
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)

-- Reducibility of terms

_⊩⟨_⟩_∷_/_ :
  (Γ : Con Term ℓ) (l : Universe-level) (_ A : Term ℓ) → Γ ⊩⟨ l ⟩ A →
  Set a
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

-- Equality of reducibile terms

_⊩⟨_⟩_≡_∷_/_ :
  (Γ : Con Term ℓ) (l : Universe-level) (_ _ A : Term ℓ) → Γ ⊩⟨ l ⟩ A →
  Set a
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)

------------------------------------------------------------------------
-- Some definitions related to the identity type

-- A view of parts of _⊩ₗId_∷_/_.

data ⊩Id∷-view
  {A : Term ℓ} (⊩A : Γ ⊩′⟨ l ⟩Id A) :
  ∀ t → Identity t → Set a where
  rflᵣ : let open _⊩ₗId_ ⊩A in
         Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty →
         ⊩Id∷-view ⊩A rfl rflₙ
  ne   : let open _⊩ₗId_ ⊩A in
         (u-n : Neutral u) →
         Γ ⊢ u ~ u ∷ Id Ty lhs rhs →
         ⊩Id∷-view ⊩A u (ne u-n)

-- The view is inhabited for well-formed identity terms.

⊩Id∷-view-inhabited :
  ∀ {A} {⊩A : Γ ⊩′⟨ l ⟩Id A}
  ((u , _ , u-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A) →
  ⊩Id∷-view ⊩A u u-id
⊩Id∷-view-inhabited = λ where
  (_ , _ , rflₙ , lhs≡rhs) → rflᵣ lhs≡rhs
  (_ , _ , ne u-n , u~u)   → ne u-n u~u

-- A view of parts of _⊩ₗId_≡_∷_/_.

data ⊩Id≡∷-view
  {Γ : Con Term ℓ} (lhs rhs {Ty} : Term ℓ) (⊩Ty : Γ ⊩⟨ l ⟩ Ty) :
  ∀ t → Identity t → ∀ u → Identity u → Set a where
  rfl₌ : (lhs≡rhs : Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty) →
         ⊩Id≡∷-view lhs rhs ⊩Ty rfl rflₙ rfl rflₙ
  ne   : (t′-n : Neutral t′) (u′-n : Neutral u′) →
         Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs →
         ⊩Id≡∷-view lhs rhs ⊩Ty t′ (ne t′-n) u′ (ne u′-n)

-- The view is inhabited for instances of "well-formed identity term
-- equality".

⊩Id≡∷-view-inhabited :
  ∀ {A} {Γ : Con Term ℓ}
  (⊩A : Γ ⊩′⟨ l ⟩Id A) →
  let open _⊩ₗId_ ⊩A in
  ((t′ , u′ , _ , _ , t′-id , u′-id , _) :
   Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A) →
  ⊩Id≡∷-view lhs rhs ⊩Ty t′ t′-id u′ u′-id
⊩Id≡∷-view-inhabited _ = λ where
  (_ , _ , _ , _ , rflₙ , rflₙ , lhs≡rhs) →
    rfl₌ lhs≡rhs
  (_ , _ , _ , _ , ne t′-n , ne u′-n , t′~u′) →
    ne t′-n u′-n t′~u′
  (_ , _ , _ , _ , rflₙ , ne _ , ())
  (_ , _ , _ , _ , ne _ , rflₙ , ())

-- A kind of constructor for _⊩ₗId_≡_∷_/_.

⊩Id≡∷ :
  ∀ {A} {Γ : Con Term ℓ} {⊩A : Γ ⊩′⟨ l ⟩Id A} →
  let open _⊩ₗId_ ⊩A in
  ((t′ , _ , t′-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A)
  ((u′ , _ , u′-id , _) : Γ ⊩⟨ l ⟩ u ∷ A / Idᵣ ⊩A) →
  Identity-rec t′-id
    (Identity-rec u′-id
       (Lift _ ⊤)
       (Lift _ ⊥))
    (Identity-rec u′-id
       (Lift _ ⊥)
       (Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs)) →
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A
⊩Id≡∷ ⊩t@(t′ , t⇒*t′ , t′-id , _) ⊩u@(u′ , u⇒*u′ , u′-id , _) rest =
    t′ , u′ , t⇒*t′ , u⇒*u′ , t′-id , u′-id
  , (case ⊩Id∷-view-inhabited ⊩t of λ where
       (rflᵣ lhs≡rhs) → case ⊩Id∷-view-inhabited ⊩u of λ where
         (rflᵣ _) → lhs≡rhs
         (ne _ _) → case rest of λ ()
       (ne _ _) → case ⊩Id∷-view-inhabited ⊩u of λ where
         (rflᵣ _) → case rest of λ ()
         (ne _ _) → rest)

-- A kind of inverse of ⊩Id≡∷.

⊩Id≡∷⁻¹ :
  ∀ {A} {Γ : Con Term ℓ}
  (⊩A : Γ ⊩′⟨ l ⟩Id A) →
  let open _⊩ₗId_ ⊩A in
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A →
  ∃ λ (⊩t@(t′ , _ , t′-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A) →
  ∃ λ (⊩u@(u′ , _ , u′-id , _) : Γ ⊩⟨ l ⟩ u ∷ A / Idᵣ ⊩A) →
  Identity-rec t′-id
    (Identity-rec u′-id
       (Lift _ ⊤)
       (Lift _ ⊥))
    (Identity-rec u′-id
       (Lift _ ⊥)
       (Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs))
⊩Id≡∷⁻¹ ⊩A t≡u@(t′ , u′ , t⇒*t′ , u⇒*u′ , t′-id , u′-id , rest) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (rfl₌ lhs≡rhs) →
        (t′ , t⇒*t′ , t′-id , lhs≡rhs)
      , (u′ , u⇒*u′ , u′-id , lhs≡rhs)
      , _
    (ne _ _ t′~u′) →
        (t′ , t⇒*t′ , t′-id , ~-trans t′~u′ (~-sym t′~u′))
      , (u′ , u⇒*u′ , u′-id , ~-trans (~-sym t′~u′) t′~u′)
      , t′~u′
