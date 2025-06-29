------------------------------------------------------------------------
-- Some definitions that are re-exported from Definition.Untyped but
-- do not depend on that module's module parameter
------------------------------------------------------------------------

module Definition.Untyped.NotParametrised where

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.List
open import Tools.Nat
open import Tools.PropositionalEquality

private variable
  a   : Level
  l n : Nat
  P   : Nat → Set _

------------------------------------------------------------------------
-- Definitions related to terms

-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Terms added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

infixl 24 _∙_

data Con (A : Nat → Set a) : Nat → Set a where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private variable
  Γ : Con _ _

-- Empty-con Γ holds if Γ is empty.

data Empty-con {P : Nat → Set a} : Con P n → Set a where
  ε : Empty-con ε

-- A variant of Empty-con.

infix 4 _or-empty_

data _or-empty_ {P : Nat → Set a} (A : Set a) : Con P n → Set a where
  possibly-nonempty : ⦃ ok : A ⦄ → A or-empty Γ
  ε                 : A or-empty ε

-- Representation of sub terms using a list of binding levels

infixr 5 _∷ₜ_

data GenTs (A : Nat → Set a) : Nat → List Nat → Set a where
  []   : {n : Nat} → GenTs A n []
  _∷ₜ_ : {n b : Nat} {bs : List Nat}
         (t : A (b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

-- Sigma and Unit types have two modes, allowing either projections
-- and η-equality (strong) or elimination by prodrec/unitrec (weak).
--
-- Note that one can optionally enable η-equality for weak unit types,
-- see Definition.Typed.Variant.Type-variant.η-for-Unitʷ.
data Strength : Set where
  𝕤 𝕨 : Strength

-- Π- or Σ-types.

data BinderMode : Set where
  BMΠ : BinderMode
  BMΣ : (s : Strength) → BinderMode

-- The function drop k removes the last k entries from contexts.

drop : ∀ k → Con P (k + n) → Con P n
drop 0      Γ       = Γ
drop (1+ k) (Γ ∙ _) = drop k Γ

------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Nat → Nat → Set where
  id    : {n : Nat}   → Wk n n                    -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  {l m n : Nat} → Wk l m → Wk m n → Wk l n
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

liftn : {k m : Nat} → Wk k m → (n : Nat) → Wk (n + k) (n + m)
liftn ρ 0 = ρ
liftn ρ (1+ n) = lift (liftn ρ n)

stepn : {k m : Nat} (ρ : Wk k m) → (n : Nat) → Wk (n + k) m
stepn ρ 0 = ρ
stepn ρ (1+ n) = step (stepn ρ n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

-- A weakening for closed terms.

wk₀ : Wk n 0
wk₀ {n = 0}    = id
wk₀ {n = 1+ n} = step wk₀

------------------------------------------------------------------------
-- Universe levels

-- Universe levels.

Infinite-universe-level : Set
Infinite-universe-level = Nat

data Universe-level : Set where
  0ᵘ+_ : Nat → Universe-level
  ωᵘ+_ : Infinite-universe-level → Universe-level

0ᵘ : Universe-level
0ᵘ = 0ᵘ+ 0

1ᵘ : Universe-level
1ᵘ = 0ᵘ+ 1

ωᵘ : Universe-level
ωᵘ = ωᵘ+ 0

-- The successor of a universe level.

1ᵘ+_ : Universe-level → Universe-level
1ᵘ+ (0ᵘ+ x) = 0ᵘ+ 1+ x
1ᵘ+ (ωᵘ+ x) = ωᵘ+ 1+ x

-- The maximum of two universe levels.

infixl 6 _⊔ᵘ_

_⊔ᵘ_ : (_ _ : Universe-level) → Universe-level
(0ᵘ+ m) ⊔ᵘ (0ᵘ+ n) = 0ᵘ+ (m Tools.Nat.⊔ n)
(0ᵘ+ m) ⊔ᵘ (ωᵘ+ n) = ωᵘ+ n
(ωᵘ+ m) ⊔ᵘ (0ᵘ+ n) = ωᵘ+ m
(ωᵘ+ m) ⊔ᵘ (ωᵘ+ n) = ωᵘ+ (m Tools.Nat.⊔ n)

-- Ordering of universe levels.

infix 4 _≤ᵘ_

data _≤ᵘ_ : Universe-level → Universe-level → Set where
  ≤ᵘ-fin     : ∀ {l l′} → l ≤′ l′ → 0ᵘ+ l ≤ᵘ 0ᵘ+ l′
  ≤ᵘ-fin-inf : ∀ {l l′} → 0ᵘ+ l ≤ᵘ ωᵘ+ l′
  ≤ᵘ-inf     : ∀ {l l′} → l ≤′ l′ → ωᵘ+ l ≤ᵘ ωᵘ+ l′

≤ᵘ-refl : ∀ {l} → l ≤ᵘ l
≤ᵘ-refl {0ᵘ+ x} = ≤ᵘ-fin ≤′-refl
≤ᵘ-refl {ωᵘ+ x} = ≤ᵘ-inf ≤′-refl

-- Strict ordering of universe levels.

infix 4 _<ᵘ_

data _<ᵘ_ : Universe-level → Universe-level → Set where
  <ᵘ-fin     : ∀ {l l′} → l <′ l′ → 0ᵘ+ l <ᵘ 0ᵘ+ l′
  <ᵘ-fin-inf : ∀ {l l′} → 0ᵘ+ l <ᵘ ωᵘ+ l′
  <ᵘ-inf     : ∀ {l l′} → l <′ l′ → ωᵘ+ l <ᵘ ωᵘ+ l′

0ᵘ<ᵘ1ᵘ : 0ᵘ <ᵘ 1ᵘ
0ᵘ<ᵘ1ᵘ = <ᵘ-fin ≤′-refl
