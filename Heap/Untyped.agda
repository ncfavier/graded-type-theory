------------------------------------------------------------------------
-- A resource aware heap semantics. Some basic definitions.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Tools.Bool
open import Definition.Typed.Variant

module Heap.Untyped
  {a} {M : Set a}
  {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄 hiding (_+_)
open Type-variant type-variant
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_≤_)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation

open import Definition.Untyped M hiding (head)
open import Graded.Mode
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Modality.Nr-instances
open import Graded.Usage.Erased-matches

private variable
  n n′ m m′ m″ n″ k : Nat
  Γ : Con Term _
  t t₁ t₂ u v A B : Term _
  x : Fin _
  p q r : M
  s : Strength
  b : BinderMode
  ρ ρ′ : Wk _ _

infixl 20 _⊢_↦[_]_⨾_
infix   2 ⟨_,_,_,_⟩

------------------------------------------------------------------------
-- Pointers, closures and environments

-- Pointers as de Bruijn indices

Ptr : Nat → Set
Ptr = Fin

pattern y0 = x0

-- Heap entries, containing a term and a weakening, translating variable
-- indices to pointer indices.
-- Indexed by the size of the heap and the number of free variables of
-- the term

Entry : (m n : Nat) → Set a
Entry m n = Term n × Wk m n

-- Entires with a grade

Entryₘ : (m n : Nat) → Set a
Entryₘ m n = M × Entry m n

-- Weakening of entries

wkᵉⁿ : Wk m′ m → Entry m n → Entry m′ n
wkᵉⁿ ρ (t , E) = t , ρ • E

wk1ᵉⁿ : Entry m n → Entry (1+ m) n
wk1ᵉⁿ = wkᵉⁿ (step id)

------------------------------------------------------------------------
-- Eliminators and Evaluation stacks

-- Eliminators, indexed by the size of the heap

data Elim (m : Nat) : Set a where
  ∘ₑ        : (p : M) (u : Term n) (ρ : Wk m n) → Elim m
  fstₑ      : M → Elim m
  sndₑ      : M → Elim m
  prodrecₑ  : (r p q : M) (A : Term (1+ n)) (u : Term (2+ n)) (ρ : Wk m n) → Elim m
  natrecₑ   : (p q r : M) (A : Term (1+ n)) (z : Term n)
              (s : Term (2+ n)) (ρ : Wk m n) → Elim m
  unitrecₑ  : (p q : M) (A : Term (1+ n)) (u : Term n) (ρ : Wk m n) → Elim m
  emptyrecₑ : (p : M) (A : Term n) (ρ : Wk m n) → Elim m
  Jₑ        : (p q : M) (A t : Term n) (B : Term (2+ n))
              (u v : Term n) (ρ : Wk m n) → Elim m
  Kₑ        : (p : M) (A t : Term n) (B : Term (1+ n))
              (u : Term n) (ρ : Wk m n) → Elim m
  []-congₑ  : (s : Strength) (A t u : Term n) (ρ : Wk m n) → Elim m
  sucₑ      : Elim m

-- Weakening of eliminators

wkᵉ : Wk m′ m → Elim m → Elim m′
wkᵉ ρ (∘ₑ p u ρ′) = ∘ₑ p u (ρ • ρ′)
wkᵉ ρ (fstₑ p) = fstₑ p
wkᵉ ρ (sndₑ p) = sndₑ p
wkᵉ ρ (natrecₑ p q r A z s ρ′) = natrecₑ p q r A z s (ρ • ρ′)
wkᵉ ρ (prodrecₑ r p q A u ρ′) = prodrecₑ r p q A u (ρ • ρ′)
wkᵉ ρ (unitrecₑ p q A u ρ′) = unitrecₑ p q A u (ρ • ρ′)
wkᵉ ρ (emptyrecₑ p A ρ′) = emptyrecₑ p A (ρ • ρ′)
wkᵉ ρ (Jₑ p q A t B u v ρ′) = Jₑ p q A t B u v (ρ • ρ′)
wkᵉ ρ (Kₑ p A t B u ρ′) = Kₑ p A t B u (ρ • ρ′)
wkᵉ ρ ([]-congₑ s A t u ρ′) = []-congₑ s A t u (ρ • ρ′)
wkᵉ ρ sucₑ = sucₑ

wk1ᵉ : Elim m → Elim (1+ m)
wk1ᵉ = wkᵉ (step id)

wk2ᵉ : Elim m → Elim (2+ m)
wk2ᵉ = wkᵉ (step (step id))

-- The multiplicity of the Jₑ eliminator

∣∣ᵉ-J : Erased-matches → (p q : M) → M
∣∣ᵉ-J none _ _ = ω
∣∣ᵉ-J all  _ _ = 𝟘
∣∣ᵉ-J some p q =
  case is-𝟘? p of λ where
    (no _) → ω
    (yes _) → case is-𝟘? q of λ where
      (no _) → ω
      (yes _) → 𝟘

-- The multiplicity of the Kₑ eliminator

∣∣ᵉ-K : Erased-matches → (p : M) → M
∣∣ᵉ-K none _ = ω
∣∣ᵉ-K all  _ = 𝟘
∣∣ᵉ-K some p =
  case is-𝟘? p of λ where
    (no _) → ω
    (yes _) → 𝟘

-- Multiplicity of an eliminator, representing how many copies need to be evaluated

∣_∣ᵉ : ⦃ _ : Has-nr M semiring-with-meet ⦄
     → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
     → Elim m → M
∣ ∘ₑ _ _ _ ∣ᵉ = 𝟙
∣ fstₑ _ ∣ᵉ = 𝟙
∣ sndₑ _ ∣ᵉ = 𝟙
∣ prodrecₑ r _ _ _ _ _ ∣ᵉ = r
∣ natrecₑ p _ r _ _ _ _ ∣ᵉ = nr₂ p r
∣ unitrecₑ p _ _ _ _ ∣ᵉ = p
∣ emptyrecₑ p _ _ ∣ᵉ = p
∣ Jₑ p q _ _ _ _ _ _ ∣ᵉ = ∣∣ᵉ-J (erased-matches-for-J 𝟙ᵐ) p q
∣ Kₑ p _ _ _ _ _ ∣ᵉ = ∣∣ᵉ-K (erased-matches-for-K 𝟙ᵐ) p
∣ []-congₑ _ _ _ _ _ ∣ᵉ = 𝟘
∣ sucₑ ∣ᵉ = 𝟙

-- Evaluation stacks, indexed by the size of the heap

data Stack (m : Nat) : Set a where
  ε : Stack m
  _∙_ : (e : Elim m) → (S : Stack m) → Stack m

-- Multiplicity of a stack, representing how many copies are currently being evaluated

∣_∣ : ⦃ _ : Has-nr M semiring-with-meet ⦄
    → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
    →  Stack m → M
∣ ε ∣ = 𝟙
∣ e ∙ S ∣ = ∣ S ∣ · ∣ e ∣ᵉ

-- Weakening of stacks

wkˢ : Wk m′ m → Stack m → Stack m′
wkˢ ρ ε = ε
wkˢ ρ (e ∙ S) = wkᵉ ρ e ∙ wkˢ ρ S

wk1ˢ : Stack m → Stack (1+ m)
wk1ˢ = wkˢ (step id)

wk2ˢ : Stack m → Stack (2+ m)
wk2ˢ = wkˢ (step (step id))

-- Concatenation of stacks

_++_ : (S S′ : Stack m) → Stack m
ε ++ S′ = S′
(e ∙ S) ++ S′ = e ∙ (S ++ S′)

sucₛ : Nat → Stack m
sucₛ 0 = ε
sucₛ (1+ n) = sucₑ ∙ sucₛ n

private variable
  e : Elim _
  S : Stack _

-- A utility predicate: stacks containing erased emptyrec

data emptyrec₀∈_ : (S : Stack m) → Set a where
  here : emptyrec₀∈ (emptyrecₑ 𝟘 A ρ ∙ S)
  there : emptyrec₀∈ S → emptyrec₀∈ (e ∙ S)

------------------------------------------------------------------------
-- Heaps

-- Heaps are collections of bindings.

infixl 24 _∙_
infixl 24 _∙●

data Heap : (k m : Nat) → Set a where
  ε   : Heap 0 0
  _∙_ : (H : Heap k m) → (c : Entryₘ m n) → Heap k (1+ m)
  _∙● : (H : Heap k m) → Heap (1+ k) (1+ m)

-- A heap where all entries are erased

erasedHeap : (k : Nat) → Heap k k
erasedHeap 0 = ε
erasedHeap (1+ k) = erasedHeap k ∙●

private variable
  H H′ : Heap _ _
  c : Entry _ _
  c′ : Entryₘ _ _
  y : Ptr _

-- Heap lookup (with grade update)
-- Note that lookup fails e.g. when the grade is 𝟘.

data _⊢_↦[_]_⨾_ : (H : Heap k m) (y : Ptr m) (q : M)
                  (c : Entry m n) (H′ : Heap k m) → Set a where
  here : p - q ≡ r
       → H ∙ (p , c) ⊢ y0 ↦[ q ] wk1ᵉⁿ c ⨾ H ∙ (r , c)
  there : H ⊢ y ↦[ q ] c ⨾ H′
        → H ∙ c′ ⊢ y +1 ↦[ q ] wk1ᵉⁿ c ⨾ H′ ∙ c′
  there● : H ⊢ y ↦[ q ] c ⨾ H′
         → H ∙● ⊢ y +1 ↦[ q ] wk1ᵉⁿ c ⨾ H′ ∙●


-- Heap lookup (without grade update)

data _⊢_↦_ : (H : Heap k m) (y : Ptr m) (c : Entry m n) → Set a where
  here : H ∙ (p , c) ⊢ y0 ↦ wk1ᵉⁿ c
  there : H ⊢ y ↦ c
        → H ∙ c′ ⊢ y +1 ↦ wk1ᵉⁿ c
  there● : H ⊢ y ↦ c
         → H ∙● ⊢ y +1 ↦ wk1ᵉⁿ c

data _⊢_↦● : (H : Heap k m) (y : Ptr m) → Set a where
  here : H ∙● ⊢ y0 ↦●
  there : H ⊢ y ↦● → H ∙ c′ ⊢ y +1 ↦●
  there● : H ⊢ y ↦● → H ∙● ⊢ y +1 ↦●


-- Equality of heaps up to grades

infix 5 _~ʰ_

data _~ʰ_ : (H H′ : Heap k m) → Set a where
  ε : ε ~ʰ ε
  _∙_ : H ~ʰ H′ → (c : Entry m n) → H ∙ (p , c) ~ʰ H′ ∙ (q , c)
  _∙● : H ~ʰ H′ → H ∙● ~ʰ H′ ∙●

-- Weakening of heaps

data _∷_⊇ʰ_ : (ρ : Wk m n) (H : Heap k m) (H′ : Heap k n) → Set a where
  id : id ∷ H ⊇ʰ H
  step : ρ ∷ H ⊇ʰ H′ → step ρ ∷ H ∙ c′ ⊇ʰ H′
  lift : ρ ∷ H ⊇ʰ H′ → lift ρ ∷ H ∙ (p , wkᵉⁿ ρ c) ⊇ʰ H′ ∙ (p , c)

-- Heaps as substitutions

toSubstₕ : Heap k m → Subst k m
toSubstₕ ε = idSubst
toSubstₕ (H ∙ (_ , t , ρ)) =
  let σ = toSubstₕ H
  in  consSubst σ (wk ρ t [ σ ])
toSubstₕ (H ∙●) = liftSubst (toSubstₕ H)

infix 25 _[_]ₕ
infix 25 _[_]⇑ₕ
infix 25 _[_]⇑²ₕ

_[_]ₕ : Term m → Heap k m → Term k
t [ H ]ₕ = t [ toSubstₕ H ]

_[_]⇑ₕ : Term (1+ m) → Heap k m → Term (1+ k)
t [ H ]⇑ₕ = t [ liftSubst (toSubstₕ H) ]

_[_]⇑²ₕ : Term (2+ m) → Heap k m → Term (2+ k)
t [ H ]⇑²ₕ = t [ liftSubstn (toSubstₕ H) 2 ]

-- A weakening that acts as an "inverse" to a heap substitution
-- See Heap.Untyped.Properties.toWkₕ-toSubstₕ

toWkₕ : Heap k m → Wk m k
toWkₕ ε = id
toWkₕ (H ∙ c) = step (toWkₕ H)
toWkₕ (H ∙●) = lift (toWkₕ H)

------------------------------------------------------------------------
-- Evaluation states

-- States, indexed by the size of the heap and the number of free
-- variables in the head.

record State (k m n : Nat) : Set a where
  constructor ⟨_,_,_,_⟩
  field
    heap : Heap k m
    head : Term n
    env : Wk m n
    stack : Stack m

-- Converting states back to terms

⦅_⦆ᵉ : Elim m → (Term m → Term m)
⦅ ∘ₑ p u ρ ⦆ᵉ = _∘⟨ p ⟩ wk ρ u
⦅ fstₑ p ⦆ᵉ = fst p
⦅ sndₑ p ⦆ᵉ = snd p
⦅ prodrecₑ r p q A u ρ ⦆ᵉ t =
  prodrec r p q (wk (lift ρ) A) t (wk (liftn ρ 2) u)
⦅ natrecₑ p q r A z s ρ ⦆ᵉ t =
  natrec p q r (wk (lift ρ) A) (wk ρ z) (wk (liftn ρ 2) s) t
⦅ unitrecₑ p q A u ρ ⦆ᵉ t =
  unitrec p q (wk (lift ρ) A) t (wk ρ u)
⦅ emptyrecₑ p A ρ ⦆ᵉ t =
  emptyrec p (wk ρ A) t
⦅ Jₑ p q A t B u v ρ ⦆ᵉ w =
  J p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v) w
⦅ Kₑ p A t B u ρ ⦆ᵉ v =
  K p (wk ρ A) (wk ρ t) (wk (lift ρ) B) (wk ρ u) v
⦅ []-congₑ s A t u ρ ⦆ᵉ v =
  []-cong s (wk ρ A ) (wk ρ t) (wk ρ u) v
⦅ sucₑ ⦆ᵉ = suc

⦅_⦆ˢ : Stack m → (Term m → Term m)
⦅ ε ⦆ˢ = idᶠ
⦅ e ∙ S ⦆ˢ = ⦅ S ⦆ˢ ∘ᶠ ⦅ e ⦆ᵉ

⦅_⦆ : (s : State k m n) → Term k
⦅ ⟨ H , t , ρ , S ⟩ ⦆ = ⦅ S ⦆ˢ (wk ρ t) [ H ]ₕ

-- The initial state

initial : Term k → State k k k
initial {k} t = ⟨ erasedHeap k , t , id , ε ⟩

------------------------------------------------------------------------
-- Values and normal form head terms

-- Values are those terms that do not evaluate further

data Value {n : Nat} : (t : Term n) → Set a where
  lamᵥ : Value (lam p t)
  zeroᵥ : Value zero
  sucᵥ : Value (suc t)
  starᵥ : Value (star s)
  prodᵥ : Value (prod s p u t)
  rflᵥ : Value rfl
  Uᵥ : Value U
  ΠΣᵥ : Value (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕᵥ : Value ℕ
  Unitᵥ : Value (Unit s)
  Emptyᵥ : Value Empty
  Idᵥ : Value (Id A t u)
  unitrec-ηᵥ : Unitʷ-η → Value (unitrec p q A t u)

-- States in normal form are either values, variables without entries in
-- the heap or unitrec when the weak unit type has η-equality.
-- I.e. states which do not reduce with _⇒ₙ_

data Normal : (State k m n) → Set a where
  val : Value t → Normal ⟨ H , t , ρ , S ⟩
  var : H ⊢ wkVar ρ x ↦● → Normal ⟨ H , var x , ρ , S ⟩
