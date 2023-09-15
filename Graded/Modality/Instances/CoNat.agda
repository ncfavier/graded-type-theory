{-# OPTIONS --cubical --postfix-projections #-}

------------------------------------------------------------------------
-- A modality for the conatural numbers
------------------------------------------------------------------------

module Graded.Modality.Instances.CoNat where

import Tools.Algebra
open import Tools.Bool as B using (Bool; false; true; T)
import Data.Bool.Properties as B
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+)
import Data.Nat.Base as N
import Data.Nat.Properties as N
open import Tools.Nullary
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
import Relation.Binary.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Sum.Base using ([_,_])
open import Tools.Unit

import Cubical.Data.Equality as □
import Cubical.Foundations.HLevels as □
open import Function using (id; _∘_)
open import Function.Equivalence using (Equivalence)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Nullary.Negation using (¬¬-map; decidable-stable)

import Graded.Modality
import Graded.Modality.Instances.BoundedStar as BoundedStar
import Graded.Modality.Properties.PartialOrder
open import Graded.Modality.Variant lzero
open import Graded.Modality.Instances.Nat-plus-infinity as ℕ⊎∞ using (ℕ⊎∞)

-- The grades are the conatural numbers, represented as downward closed subsets of ℕ.
-- These can be seen as presheaves on ω valued in decidable propositions.

Coℕ : Set
Coℕ = Σ (Nat → Bool) λ P → {n m : Nat} → n N.≤ m → T (P m) → T (P n)

open Graded.Modality Coℕ
open Tools.Algebra   Coℕ

private variable
  a b c   : ℕ⊎∞
  m n o   : Coℕ
  x y z   : Nat
  variant : Modality-variant

_∈_ _∉_ : Nat → Coℕ → Bool
x ∈ n = n .proj₁ x
x ∉ n = B.not (n .proj₁ x)

-- A Yoneda embedding.
⌞_⌟ : Nat → Coℕ
⌞ x ⌟ .proj₁ y = Dec.does (y N.<? x)
⌞ x ⌟ .proj₂ {y} {z} y≤z z<?x = N.<⇒<ᵇ (N.<-transʳ y≤z (N.<ᵇ⇒< z x z<?x))

∞ : Coℕ
∞ .proj₁ _ = true
∞ .proj₂ _ _ = _

-- A restricted Yoneda embedding with respect to the inclusion
-- `⌞_⌟ : ℕ → ℕ⊎∞`.
よ : ℕ⊎∞ → Coℕ
よ ℕ⊎∞.⌞ x ⌟ = ⌞ x ⌟
よ ℕ⊎∞.∞ = ∞

よ→≤ : T (x ∈ よ a) → a ℕ⊎∞.≤ ℕ⊎∞.⌞ 1+ x ⌟
よ→≤ {x} {ℕ⊎∞.⌞ a ⌟} x∈a = ℕ⊎∞.⌞⌟-antitone (N.<ᵇ⇒< x a x∈a)
よ→≤ {x} {ℕ⊎∞.∞} x∈a = ℕ⊎∞.∞≤ ℕ⊎∞.⌞ 1+ x ⌟

≤→よ : a ℕ⊎∞.≤ ℕ⊎∞.⌞ 1+ x ⌟ → T (x ∈ よ a)
≤→よ {ℕ⊎∞.⌞ a ⌟} {x} a≤x = N.<⇒<ᵇ (ℕ⊎∞.⌞⌟-antitone⁻¹ a≤x)
≤→よ {ℕ⊎∞.∞} {x} a≤x = _

-- よ's action on morphisms (monotonicity).
よ₁ : ∀ {x y z} → x ℕ⊎∞.≤ y → T (z ∈ よ y) → T (z ∈ よ x)
よ₁ {ℕ⊎∞.⌞ x ⌟} {ℕ⊎∞.⌞ y ⌟} x≤y z∈y = N.<⇒<ᵇ (N.<-transˡ
  (N.<ᵇ⇒< _ _ z∈y)
  (ℕ⊎∞.⌞⌟-antitone⁻¹ x≤y))
よ₁ {ℕ⊎∞.∞} _ _ = _

N-yoneda : ∀ {x y : Nat} → (∀ z → (z N.< x) ⇔ (z N.< y)) → x ≡ y
N-yoneda {x} {y} h = N.≤-antisym
  (N.≮⇒≥ λ y<x → N.n≮n _ (h y .proj₁ y<x))
  (N.≮⇒≥ λ x<y → N.n≮n _ (h x .proj₂ x<y))

-- A consequence of the Yoneda lemma.
⌞⌟-injective : {x y : Nat} → ⌞ x ⌟ ≡ ⌞ y ⌟ → x ≡ y
⌞⌟-injective e = N-yoneda λ z →
    (λ z<x → N.<ᵇ⇒< _ _ (subst T (□.happly (cong proj₁ e) z) (N.<⇒<ᵇ z<x)))
  , (λ z<y → N.<ᵇ⇒< _ _ (subst T (sym (□.happly (cong proj₁ e) z)) (N.<⇒<ᵇ z<y)))

⌞⌟≢∞ : ⌞ x ⌟ ≢ ∞
⌞⌟≢∞ {x} e = N.n≮n _ (N.<ᵇ⇒< x x (B.true→T (cong (x ∈_) e)))

よ-injective : ∀ {a b} → よ a ≡ よ b → a ≡ b
よ-injective {ℕ⊎∞.⌞ _ ⌟} {ℕ⊎∞.⌞ _ ⌟} e = cong ℕ⊎∞.⌞_⌟ (⌞⌟-injective e)
よ-injective {ℕ⊎∞.⌞ x ⌟} {ℕ⊎∞.∞} e = ⊥-elim (⌞⌟≢∞ e)
よ-injective {ℕ⊎∞.∞} {ℕ⊎∞.⌞ x ⌟} e = ⊥-elim (⌞⌟≢∞ (sym e))
よ-injective {ℕ⊎∞.∞} {ℕ⊎∞.∞} e = refl

-- Some extensionality principles.

ext∈ : (∀ x → x ∈ n ≡ x ∈ m) → n ≡ m
ext∈ h = □.Σ≡Prop (λ _ → □.isPropPathToIsProp
                  (□.isPropImplicitΠ2
                  λ _ _ → □.isPropΠ2
                  λ _ _ → □.isPropToIsPropPath
                  λ _ _ → B.T-propositional))
         (□.funExt h)

boolext-contra : {b c : Bool} → (T b → T c) → (¬ T b → ¬ T c) → b ≡ c
boolext-contra {false} {false} b→c ¬b→¬c = refl
boolext-contra {false} {true} b→c ¬b→¬c = ⊥-elim (¬b→¬c id _)
boolext-contra {true} {false} b→c ¬b→¬c = ⊥-elim (b→c _)
boolext-contra {true} {true} b→c ¬b→¬c = refl

boolext : {b c : Bool} → (T b → T c) → (T c → T b) → b ≡ c
boolext b→c c→b = boolext-contra b→c (λ k → k ∘ c→b)

ext0 : ¬ T (0 ∈ n) → n ≡ ⌞ 0 ⌟
ext0 {n} 0∉n = ext∈ λ x → B.¬T→false (0∉n ∘ n .proj₂ N.z≤n)

ext1+ : ∀ x → T (x ∈ n) → ¬ T (1+ x ∈ n) → n ≡ ⌞ 1+ x ⌟
ext1+ {n} x x∈n 1+x∉n = ext∈ λ y → sym (boolext-contra
  (λ y<1+x → n .proj₂ (N.≤-pred (N.<ᵇ⇒< y (1+ x) y<1+x)) x∈n)
  (λ ¬y<1+x y∈n → 1+x∉n (n .proj₂ (N.≮⇒≥ (¬y<1+x ∘ N.<⇒<ᵇ)) y∈n)))

-- Non-infinite conaturals are finite.
toℕ : (n : Coℕ) → (u : Nat) → ¬ T (u ∈ n) → Σ Nat λ x → n ≡ ⌞ x ⌟
toℕ n 0 0∉n = 0 , ext0 0∉n
toℕ n (1+ u) 1+u∉n with B.T? (u ∈ n)
... | yes u∈n = 1+ u , ext1+ u u∈n 1+u∉n
... | no u∉n = toℕ n u u∉n

toℕ-retr : ∀ {a} {x} {x∉よa} → ℕ⊎∞.⌞ toℕ (よ a) x x∉よa .proj₁ ⌟ ≡ a
toℕ-retr {ℕ⊎∞.⌞ a ⌟} {x} {x∉よa} = cong ℕ⊎∞.⌞_⌟ (⌞⌟-injective (sym (toℕ ⌞ a ⌟ x x∉よa .proj₂)))
toℕ-retr {ℕ⊎∞.∞} {x} {x∉よa} = ⊥-elim (x∉よa _)

toℕ-irrelevant : ∀ n u v {u∉n v∉n} → toℕ n u u∉n .proj₁ ≡ toℕ n v v∉n .proj₁
toℕ-irrelevant n u v = ⌞⌟-injective (trans (sym (toℕ n u _ .proj₂))
                                                (toℕ n v _ .proj₂))

toℕ-injective : ∀ n m x {x∉n x∉m} → toℕ n x x∉n .proj₁ ≡ toℕ m x x∉m .proj₁ → n ≡ m
toℕ-injective n m x {x∉n} {x∉m} h =
  n ≡⟨ toℕ n x x∉n .proj₂ ⟩
  ⌞ toℕ n x x∉n .proj₁ ⌟ ≡⟨ cong ⌞_⌟ h ⟩
  ⌞ toℕ m x x∉m .proj₁ ⌟ ≡˘⟨ toℕ m x x∉m .proj₂ ⟩
  m ∎
  where
    open Tools.Reasoning.PropositionalEquality

-- Non-finite conaturals are infinite.
¬finite→∞ : (∀ x → n ≢ ⌞ x ⌟) → n ≡ ∞
¬finite→∞ {n} h = ext∈ λ x → decidable-stable (_ B.≟ _) λ k → h _ (toℕ n x (λ t → k (B.T→true t)) .proj₂)

-- Approximate conaturals into ℕ⊎∞ by sending everything above x : ℕ to ∞.
_↓_ : Coℕ → Nat → ℕ⊎∞
n ↓ x with B.T? (x ∈ n)
... | no x∉n = ℕ⊎∞.⌞ toℕ n x x∉n .proj₁ ⌟
... | yes _ = ℕ⊎∞.∞

_↓₁_ : ∀ n {x y} → x N.≤ y → (n ↓ x) ℕ⊎∞.≤ (n ↓ y)
_↓₁_ n {x} {y} x≤y with B.T? (x ∈ n) | B.T? (y ∈ n)
... | yes x∈n | _ = refl
... | no x∉n | yes y∈n = ⊥-elim (x∉n (n .proj₂ x≤y y∈n))
... | no x∉n | no y∉n = cong ℕ⊎∞.⌞_⌟ (sym (N.m≥n⇒m⊔n≡m (N.≤-reflexive (toℕ-irrelevant n y x))))

is-mono : (ℕ⊎∞ → ℕ⊎∞) → Set
is-mono f = ∀ {x x'} → x ℕ⊎∞.≤ x' → f x ℕ⊎∞.≤ f x'
is-mono² : (ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞) → Set
is-mono² _⋆_ = ∀ {x x' y y'} → x ℕ⊎∞.≤ x' → y ℕ⊎∞.≤ y' → (x ⋆ y) ℕ⊎∞.≤ (x' ⋆ y')

-- A rather strong condition: the first n "bits" of output only depend on the first
-- n "bits" of input.
is-continuous : (ℕ⊎∞ → ℕ⊎∞) → Set
is-continuous f = ∀ a x → a ℕ⊎∞.≤ ℕ⊎∞.⌞ x ⌟ → f ℕ⊎∞.∞ ℕ⊎∞.≤ ℕ⊎∞.⌞ x ⌟ → f a ℕ⊎∞.≤ ℕ⊎∞.⌞ x ⌟
is-continuous² : (ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞) → Set
is-continuous² _⋆_ = (∀ b → is-continuous (_⋆ b)) × (∀ a → is-continuous (a ⋆_))

continuous↓
  : ∀ {f} {f₁ : is-mono f} → is-continuous f
  → ∀ a x → x ∈ よ (f (よ a ↓ x)) ≡ x ∈ よ (f a)
continuous↓ {f} {f₁} f-continuous a x with B.T? (x ∈ よ a)
... | no x∉a = cong (λ z → x ∈ よ (f z)) (toℕ-retr {a} {x} {x∉a})
... | yes x∈a = boolext
  ( T (x ∈ よ (f ℕ⊎∞.∞))        →⟨ よ→≤ ⟩
    f ℕ⊎∞.∞ ℕ⊎∞.≤ ℕ⊎∞.⌞ 1+ x ⌟ →⟨ f-continuous _ _ (よ→≤ x∈a) ⟩
    f a ℕ⊎∞.≤ ℕ⊎∞.⌞ 1+ x ⌟     →⟨ ≤→よ ⟩
    T (x ∈ よ (f a))            □)
  ( T (x ∈ よ (f a))            →⟨ よ→≤ ⟩
    f a ℕ⊎∞.≤ ℕ⊎∞.⌞ 1+ x ⌟     →⟨ ≤-trans (f₁ refl) ⟩
    f ℕ⊎∞.∞ ℕ⊎∞.≤ ℕ⊎∞.⌞ 1+ x ⌟ →⟨ ≤→よ ⟩
    T (x ∈ よ (f ℕ⊎∞.∞))        □)
  where
    open Graded.Modality.Properties.PartialOrder ℕ⊎∞.ℕ⊎∞-semiring-with-meet

-- Given a binary operation on ℕ⊎∞ satisfying a certain continuity property, we can
-- compute its "Yoneda extension" acting on Coℕ.
lift² : (_⋆_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞) → is-mono² _⋆_
      → Coℕ → Coℕ → Coℕ
lift² _⋆_ _⋆₁_ n m .proj₁ x = よ ((n ↓ x) ⋆ (m ↓ x)) .proj₁ x
lift² _⋆_ _⋆₁_ n m .proj₂ {x} {y} x≤y ty =
  よ ((n ↓ x) ⋆ (m ↓ x)) .proj₂ x≤y
    (よ₁ ((n ↓₁ x≤y) ⋆₁ (m ↓₁ x≤y)) ty)

lift²-よ : ∀ {_⋆_} {⋆₁ : is-mono² _⋆_} → is-continuous² _⋆_ → lift² _⋆_ ⋆₁ (よ a) (よ b) ≡ よ (a ⋆ b)
lift²-よ {a} {b} {_⋆_} {_⋆₁_} ⋆-continuous = ext∈ λ x → trans
  (continuous↓ {_⋆ (よ b ↓ x)} {λ x≤x' → x≤x' ⋆₁ ≤-refl} (⋆-continuous .proj₁ _) a x)
  (continuous↓ {a ⋆_} {λ x≤x' → ≤-refl ⋆₁ x≤x'} (⋆-continuous .proj₂ _) b x)
  where
    open Graded.Modality.Properties.PartialOrder ℕ⊎∞.ℕ⊎∞-semiring-with-meet

-- In order to prove properties about lifted functions, it is convenient to have an
-- "induction principle" that lets us reduce the problem to the image of よ.
-- We get this from よ being a topologically dense inclusion.
-- This is freely adapted from Martín Escardó's TypeTopology
-- (https://www.cs.bham.ac.uk/~mhe/TypeTopology/CoNaturals.GenericConvergentSequence.html#12159).

¬¬-separated : ∀ {ℓ} → Set ℓ → Set ℓ
¬¬-separated A = (x y : A) → ¬ ¬ (x ≡ y) → x ≡ y

Coℕ-¬¬-separated : ¬¬-separated Coℕ
Coℕ-¬¬-separated n m ¬¬n≡m = ext∈ λ x → decidable-stable (_ B.≟ _) (¬¬-map (cong (x ∈_)) ¬¬n≡m)

Coℕ-densityP
  : ∀ {ℓ} {X : Set ℓ} → ¬¬-separated X
  → {f g : Coℕ → X}
  → {P : Coℕ → Set}
  → (∀ a → P (よ a) → f (よ a) ≡ g (よ a))
  → ∀ n → P n → f n ≡ g n
Coℕ-densityP sep {f} {g} {P} h n pn = sep (f n) (g n) ¬¬fn≡gn
  where
    ¬finite : f n ≢ g n → ∀ x → n ≢ ⌞ x ⌟
    ¬finite k x n≡x = k (subst (λ z → f z ≡ g z) (sym n≡x) (h ℕ⊎∞.⌞ x ⌟ (subst P n≡x pn)))
    ¬∞ : f n ≢ g n → n ≢ ∞
    ¬∞ k n≡∞ = k (subst (λ z → f z ≡ g z) (sym n≡∞) (h ℕ⊎∞.∞ (subst P n≡∞ pn)))
    ¬¬fn≡gn : ¬ ¬ (f n ≡ g n)
    ¬¬fn≡gn k = ¬∞ k (¬finite→∞ (¬finite k))

Coℕ-density
  : ∀ {ℓ} {X : Set ℓ} → ¬¬-separated X
  → {f g : Coℕ → X}
  → (∀ a → f (よ a) ≡ g (よ a))
  → ∀ n → f n ≡ g n
Coℕ-density sep {f} {g} h n = Coℕ-densityP sep {f} {g} {λ _ → ⊤} (λ a _ → h a) n _

Coℕ-density²
  : ∀ {ℓ} {X : Set ℓ} → ¬¬-separated X
  → {f g : Coℕ → Coℕ → X}
  → (∀ a b → f (よ a) (よ b) ≡ g (よ a) (よ b))
  → ∀ n m → f n m ≡ g n m
Coℕ-density² sep {f} {g} h n = Coℕ-density sep λ b → Coℕ-density sep (λ a → h a b) n

Coℕ-density³
  : ∀ {ℓ} {X : Set ℓ} → ¬¬-separated X
  → {f g : Coℕ → Coℕ → Coℕ → X}
  → (∀ a b c → f (よ a) (よ b) (よ c) ≡ g (よ a) (よ b) (よ c))
  → ∀ n m o → f n m o ≡ g n m o
Coℕ-density³ sep {f} {g} h n = Coℕ-density² sep (λ b c → Coℕ-density sep (λ a → h a b c) n)

-- We can now lift some generic properties of lifted operations.

lift²-assoc : ∀ {_⋆_} {⋆₁ : is-mono² _⋆_}
            → is-continuous² _⋆_
            → Tools.Algebra.Associative _ _⋆_
            → Associative (lift² _⋆_ ⋆₁)
lift²-assoc {_⋆_} {⋆₁} ⋆-continuous ⋆-assoc = Coℕ-density³ Coℕ-¬¬-separated λ a b c →
  ((よ a ⋆' よ b) ⋆' よ c) ≡⟨ cong (λ z → z ⋆' よ c) (lift²-よ {a} {b} {_⋆_} {⋆₁} ⋆-continuous) ⟩
  (よ (a ⋆ b) ⋆' よ c)    ≡⟨ lift²-よ {a ⋆ b} {c} {_⋆_} {⋆₁} ⋆-continuous ⟩
  よ ((a ⋆ b) ⋆ c)       ≡⟨ cong よ (⋆-assoc _ _ _) ⟩
  よ (a ⋆ (b ⋆ c))       ≡˘⟨ lift²-よ {a} {b ⋆ c} {_⋆_} {⋆₁} ⋆-continuous ⟩
  (よ a ⋆' よ (b ⋆ c))    ≡˘⟨ cong (λ z → よ a ⋆' z) (lift²-よ {b} {c} {_⋆_} {⋆₁} ⋆-continuous) ⟩
  (よ a ⋆' (よ b ⋆' よ c)) ∎
  where
    _⋆'_ = lift² _⋆_ ⋆₁
    open Tools.Reasoning.PropositionalEquality

lift²-comm : ∀ {_⋆_} {⋆₁ : is-mono² _⋆_}
           → Tools.Algebra.Commutative _ _⋆_
           → Commutative (lift² _⋆_ ⋆₁)
lift²-comm ⋆-comm n m = ext∈ λ x → cong (λ z → x ∈ よ z) (⋆-comm _ _)

------------------------------------------------------------------------
-- Operators

-- Meet, defined pointwise.

infixr 40 _∧_

_∧_ : Coℕ → Coℕ → Coℕ
(n ∧ m) .proj₁ x = x ∈ n B.∨ x ∈ m
(n ∧ m) .proj₂ {x} {y} x≤y y∈n∧m with Equivalence.to (B.T-∨ {y ∈ n} {y ∈ m}) ⟨$⟩ y∈n∧m
... | inj₁ yn = Equivalence.from (B.T-∨ {x ∈ n} {x ∈ m}) ⟨$⟩
      inj₁ (n .proj₂ x≤y yn)
... | inj₂ ym = Equivalence.from (B.T-∨ {x ∈ n} {x ∈ m}) ⟨$⟩
      inj₂ (m .proj₂ x≤y ym)

¬T-∨ : ∀ {b c} → ¬ T (b B.∨ c) → ¬ T b × ¬ T c
¬T-∨ {false} ¬b∨c = id , ¬b∨c
¬T-∨ {true} ¬b∨c = ⊥-elim (¬b∨c _)

∧-よ : よ a ∧ よ b ≡ よ (a ℕ⊎∞.∧ b)
∧-よ {ℕ⊎∞.⌞ a ⌟} {ℕ⊎∞.⌞ b ⌟} = ext∈ λ x → boolext-contra
  ( T ((x N.<ᵇ a) B.∨ (x N.<ᵇ b)) →⟨ Equivalence.to (B.T-∨ {x N.<ᵇ a} {x N.<ᵇ b}) ⟨$⟩_ ⟩
    T (x N.<ᵇ a) ⊎ T (x N.<ᵇ b)   →⟨ [ (λ t → N.<⇒<ᵇ (N.m≤n⇒m≤n⊔o b (N.<ᵇ⇒< x a t))) , (λ t → N.<⇒<ᵇ (N.m≤n⇒m≤o⊔n a (N.<ᵇ⇒< x b t))) ] ⟩
    T (x N.<ᵇ a N.⊔ b)            □)
  λ ¬x<a∨x<b → let
    x≮a×x≮b : ¬ T (x N.<ᵇ a) × ¬ T (x N.<ᵇ b)
    x≮a×x≮b = ¬T-∨ {x N.<ᵇ a} {x N.<ᵇ b} ¬x<a∨x<b
    a≤x : a N.≤ x
    a≤x = N.≮⇒≥ (x≮a×x≮b .proj₁ ∘ N.<⇒<ᵇ {x} {a})
    b≤x : b N.≤ x
    b≤x = N.≮⇒≥ (x≮a×x≮b .proj₂ ∘ N.<⇒<ᵇ {x} {b})
  in N.≤⇒≯ (N.⊔-lub a≤x b≤x) ∘ N.<ᵇ⇒< x (a N.⊔ b)
∧-よ {ℕ⊎∞.⌞ a ⌟} {ℕ⊎∞.∞} = ext∈ λ x → B.∨-zeroʳ _
∧-よ {ℕ⊎∞.∞} {b} = ext∈ λ x → refl

-- Addition, lifted from ℕ⊎∞.

infixr 40 _+_

+₁ : is-mono² ℕ⊎∞._+_
+₁ {ℕ⊎∞.⌞ _ ⌟} {ℕ⊎∞.⌞ _ ⌟} {ℕ⊎∞.⌞ _ ⌟} {ℕ⊎∞.⌞ _ ⌟} x≤x' y≤y' = ℕ⊎∞.⌞⌟-antitone (N.+-mono-≤ (ℕ⊎∞.⌞⌟-antitone⁻¹ x≤x') (ℕ⊎∞.⌞⌟-antitone⁻¹ y≤y'))
+₁ {ℕ⊎∞.⌞ x ⌟} {ℕ⊎∞.⌞ x' ⌟} {ℕ⊎∞.∞} {y'} x≤x' y≤y' = ℕ⊎∞.∞≤ (ℕ⊎∞.⌞ x' ⌟ ℕ⊎∞.+ y')
+₁ {ℕ⊎∞.∞} {x'} {y} {y'} x≤x' y≤y' = ℕ⊎∞.∞≤ (x' ℕ⊎∞.+ y')

+-continuous : is-continuous² ℕ⊎∞._+_
+-continuous = +-continuousˡ , +-continuousʳ where
  open Graded.Modality.Properties.PartialOrder ℕ⊎∞.ℕ⊎∞-semiring-with-meet
  +-continuousˡ : ∀ b → is-continuous (ℕ⊎∞._+ b)
  +-continuousˡ b a x a≤x _ = ≤-trans ℕ⊎∞.+-decreasingˡ a≤x
  +-continuousʳ : ∀ a → is-continuous (a ℕ⊎∞.+_)
  +-continuousʳ a b x b≤x _ = ≤-trans ℕ⊎∞.+-decreasingʳ b≤x

_+_ : Coℕ → Coℕ → Coℕ
_+_ = lift² ℕ⊎∞._+_ +₁

-- Multiplication, lifted from ℕ⊎∞.

infixr 45 _·_

·₁ : is-mono² ℕ⊎∞._·_
·₁ {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞.⌞ 0 ⌟} {_} {y'} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.⌞ 1+ x ⌟} {ℕ⊎∞.⌞ x' ⌟} {ℕ⊎∞.∞} {y'} x≤x' y≤y' = ℕ⊎∞.∞≤ (ℕ⊎∞.⌞ x' ⌟ ℕ⊎∞.· y')
·₁ {ℕ⊎∞.⌞ 1+ x ⌟} {ℕ⊎∞.⌞ 0 ⌟} {_} {ℕ⊎∞.⌞ 0 ⌟} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.⌞ 1+ x ⌟} {ℕ⊎∞.⌞ 0 ⌟} {_} {ℕ⊎∞.⌞ 1+ y' ⌟} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.⌞ 1+ x ⌟} {ℕ⊎∞.⌞ 1+ x' ⌟} {_} {ℕ⊎∞.⌞ 0 ⌟} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.∞} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞.⌞ 0 ⌟} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.∞} {ℕ⊎∞.⌞ 1+ x ⌟} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞.⌞ 0 ⌟} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.∞} {ℕ⊎∞.∞} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞.⌞ 0 ⌟} x≤x' y≤y' = ℕ⊎∞.≤0
·₁ {ℕ⊎∞.∞} {x'} {ℕ⊎∞.⌞ 1+ _ ⌟} {y'} x≤x' y≤y' = ℕ⊎∞.∞≤ (x' ℕ⊎∞.· y')
·₁ {ℕ⊎∞.∞} {x'} {ℕ⊎∞.∞} {y'} x≤x' y≤y' = ℕ⊎∞.∞≤ (x' ℕ⊎∞.· y')
·₁ {ℕ⊎∞.⌞ 1+ x ⌟} {ℕ⊎∞.⌞ 1+ x' ⌟} {ℕ⊎∞.⌞ 1+ y ⌟} {ℕ⊎∞.⌞ 1+ y' ⌟} x≤x' y≤y' =
  ℕ⊎∞.⌞⌟-antitone (N.*-mono-≤ {1+ x'} {1+ x} {1+ y'} {1+ y} (ℕ⊎∞.⌞⌟-antitone⁻¹ x≤x') (ℕ⊎∞.⌞⌟-antitone⁻¹ y≤y'))

·-continuous : is-continuous² ℕ⊎∞._·_
·-continuous = ·-continuousˡ , ·-continuousʳ where
  open Graded.Modality.Properties.PartialOrder ℕ⊎∞.ℕ⊎∞-semiring-with-meet
  a·1+x≤a : a ℕ⊎∞.· ℕ⊎∞.⌞ 1+ x ⌟ ℕ⊎∞.≤ a
  a·1+x≤a {ℕ⊎∞.⌞ 0 ⌟} {x} = ℕ⊎∞.≤0
  a·1+x≤a {ℕ⊎∞.⌞ 1+ a ⌟} {x} = ℕ⊎∞.⌞⌟-antitone {1+ a} {(1+ a) N.* (1+ x)} (N.m≤m*n (1+ a) (N.s≤s N.z≤n))
  a·1+x≤a {ℕ⊎∞.∞} {x} = ≤-refl

  ·-continuousˡ : ∀ b → is-continuous (ℕ⊎∞._· b)
  ·-continuousˡ ℕ⊎∞.⌞ 0 ⌟ a 0 a≤x 0≤x = ℕ⊎∞.≤0
  ·-continuousˡ ℕ⊎∞.⌞ 1+ b ⌟ a x a≤x _ = ≤-trans a·1+x≤a a≤x
  ·-continuousˡ ℕ⊎∞.∞ ℕ⊎∞.⌞ 0 ⌟ 0 a≤x _ = ℕ⊎∞.≤0
  ·-continuousˡ ℕ⊎∞.∞ ℕ⊎∞.⌞ 1+ a ⌟ x a≤x _ = ℕ⊎∞.∞≤ ℕ⊎∞.⌞ x ⌟
  ·-continuousˡ ℕ⊎∞.∞ ℕ⊎∞.∞ x a≤x _ = ℕ⊎∞.∞≤ ℕ⊎∞.⌞ x ⌟

  1+x·a≤a : ℕ⊎∞.⌞ 1+ x ⌟ ℕ⊎∞.· a ℕ⊎∞.≤ a
  1+x·a≤a {x} {ℕ⊎∞.⌞ 0 ⌟} = ℕ⊎∞.≤0
  1+x·a≤a {x} {ℕ⊎∞.⌞ 1+ a ⌟} = ℕ⊎∞.⌞⌟-antitone {1+ a} {(1+ x) N.* (1+ a)} (N.m≤n*m (1+ a) {1+ x} (N.s≤s N.z≤n))
  1+x·a≤a {x} {ℕ⊎∞.∞} = ≤-refl

  ·-continuousʳ : ∀ a → is-continuous (a ℕ⊎∞.·_)
  ·-continuousʳ ℕ⊎∞.⌞ 0 ⌟ b 0 b≤x _ = ℕ⊎∞.≤0
  ·-continuousʳ ℕ⊎∞.⌞ 1+ a ⌟ ℕ⊎∞.⌞ 0 ⌟ 0 b≤x _ = ℕ⊎∞.≤0
  ·-continuousʳ ℕ⊎∞.⌞ 1+ a ⌟ ℕ⊎∞.⌞ 1+ b ⌟ x b≤x _ = ≤-trans {_} {_} {ℕ⊎∞.⌞ x ⌟} (1+x·a≤a {a} {ℕ⊎∞.⌞ 1+ b ⌟}) b≤x
  ·-continuousʳ ℕ⊎∞.⌞ 1+ a ⌟ ℕ⊎∞.∞ x b≤x _ = ℕ⊎∞.∞≤ ℕ⊎∞.⌞ x ⌟
  ·-continuousʳ ℕ⊎∞.∞ ℕ⊎∞.⌞ 0 ⌟ 0 b≤x _ = ℕ⊎∞.≤0
  ·-continuousʳ ℕ⊎∞.∞ ℕ⊎∞.⌞ 1+ b ⌟ x b≤x _ = ℕ⊎∞.∞≤ ℕ⊎∞.⌞ x ⌟
  ·-continuousʳ ℕ⊎∞.∞ ℕ⊎∞.∞ x b≤x _ = ℕ⊎∞.∞≤ ℕ⊎∞.⌞ x ⌟

_·_ : Coℕ → Coℕ → Coℕ
_·_ = lift² ℕ⊎∞._·_ ·₁

-- A star operator.

infix 50 _*

_* : Coℕ → Coℕ
n * with B.T? (0 ∈ n)
... | yes _ = ∞
... | no _ = ⌞ 1 ⌟

1+a·∞≡∞ : a ℕ⊎∞.≤ ℕ⊎∞.⌞ 1 ⌟ → a ℕ⊎∞.· ℕ⊎∞.∞ ≡ ℕ⊎∞.∞
1+a·∞≡∞ {ℕ⊎∞.⌞ 1+ a ⌟} h = refl
1+a·∞≡∞ {ℕ⊎∞.∞} h = refl

*≡+·* : ∀ n → n * ≡ ⌞ 1 ⌟ + n · n *
*≡+·* n with B.T? (0 ∈ n)
... | yes 0∈n = Coℕ-densityP Coℕ-¬¬-separated {P = λ n → T (0 ∈ n)} ∞≡1+a·∞ n 0∈n
  where
    open Tools.Reasoning.PropositionalEquality
    ∞≡1+a·∞ : ∀ a → T (0 ∈ よ a) → ∞ ≡ ⌞ 1 ⌟ + よ a · ∞
    ∞≡1+a·∞ a 0∈a =
      よ (ℕ⊎∞.⌞ 1 ⌟ ℕ⊎∞.+ ℕ⊎∞.∞) ≡˘⟨ lift²-よ {ℕ⊎∞.⌞ 1 ⌟} {ℕ⊎∞.∞} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
      ⌞ 1 ⌟ + よ ℕ⊎∞.∞           ≡˘⟨ cong (λ z → ⌞ 1 ⌟ + よ z) (1+a·∞≡∞ (よ→≤ {0} {a} 0∈a)) ⟩
      ⌞ 1 ⌟ + よ (a ℕ⊎∞.· ℕ⊎∞.∞) ≡˘⟨ cong (⌞ 1 ⌟ +_) (lift²-よ {a} {ℕ⊎∞.∞} {ℕ⊎∞._·_} {·₁} ·-continuous) ⟩
      ⌞ 1 ⌟ + よ a · よ ℕ⊎∞.∞     ∎
... | no 0∉n = subst (λ z → ⌞ 1 ⌟ ≡ ⌞ 1 ⌟ + z · ⌞ 1 ⌟) (sym (ext0 {n} 0∉n)) 1≡1+0·1
  where
    open Tools.Reasoning.PropositionalEquality
    1≡1+0·1 : ⌞ 1 ⌟ ≡ ⌞ 1 ⌟ + ⌞ 0 ⌟ · ⌞ 1 ⌟
    1≡1+0·1 =
      ⌞ 1 N.+ 0 ⌟           ≡˘⟨ lift²-よ {ℕ⊎∞.⌞ 1 ⌟} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
      ⌞ 1 ⌟ + ⌞ 0 N.* 1 ⌟   ≡˘⟨ cong (⌞ 1 ⌟ +_) (lift²-よ {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞.⌞ 1 ⌟} {ℕ⊎∞._·_} {·₁} ·-continuous) ⟩
      ⌞ 1 ⌟ + ⌞ 0 ⌟ · ⌞ 1 ⌟ ∎

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Coℕ → Coℕ → Set
m ≤ n = m ≡ m ∧ n

------------------------------------------------------------------------
-- The modality

-- A "semiring with meet" for Coℕ.

Coℕ-semiring-with-meet : Semiring-with-meet
Coℕ-semiring-with-meet = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = ⌞ 0 ⌟
  ; 𝟙 = ⌞ 1 ⌟
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = PE.isMagma _+_
            ; assoc = lift²-assoc {⋆₁ = +₁} +-continuous S.+-assoc
            }
          ; identity = (Coℕ-density Coℕ-¬¬-separated λ a →
            ⌞ 0 ⌟ + よ a           ≡⟨ lift²-よ {ℕ⊎∞.⌞ 0 ⌟} {a} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
            よ (ℕ⊎∞.⌞ 0 ⌟ ℕ⊎∞.+ a) ≡⟨ cong よ (S.+-identityˡ a) ⟩
            よ a                   ∎)
          , Coℕ-density Coℕ-¬¬-separated λ a →
            よ a + ⌞ 0 ⌟           ≡⟨ lift²-よ {a} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
            よ (a ℕ⊎∞.+ ℕ⊎∞.⌞ 0 ⌟) ≡⟨ cong よ (S.+-identityʳ a) ⟩
            よ a                   ∎
          }
        ; comm = lift²-comm {⋆₁ = +₁} S.+-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isMagma = PE.isMagma _·_
          ; assoc = lift²-assoc {⋆₁ = ·₁} ·-continuous S.·-assoc
          }
        ; identity = (Coℕ-density Coℕ-¬¬-separated λ a →
          ⌞ 1 ⌟ · よ a           ≡⟨ lift²-よ {ℕ⊎∞.⌞ 1 ⌟} {a} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
          よ (ℕ⊎∞.⌞ 1 ⌟ ℕ⊎∞.· a) ≡⟨ cong よ (S.·-identityˡ a) ⟩
          よ a                   ∎)
        , Coℕ-density Coℕ-¬¬-separated λ a →
          よ a · ⌞ 1 ⌟           ≡⟨ lift²-よ {a} {ℕ⊎∞.⌞ 1 ⌟} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
          よ (a ℕ⊎∞.· ℕ⊎∞.⌞ 1 ⌟) ≡⟨ cong よ (S.·-identityʳ a) ⟩
          よ a                   ∎
        }
      ; distrib = (Coℕ-density³ Coℕ-¬¬-separated λ a b c →
        よ a · (よ b + よ c)                 ≡⟨ cong (よ a ·_) (lift²-よ {b} {c} {ℕ⊎∞._+_} {+₁} +-continuous) ⟩
        よ a · よ (b ℕ⊎∞.+ c)               ≡⟨ lift²-よ {a} {b ℕ⊎∞.+ c} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
        よ (a ℕ⊎∞.· (b ℕ⊎∞.+ c))           ≡⟨ cong よ (S.·-distribˡ-+ a b c) ⟩
        よ ((a ℕ⊎∞.· b) ℕ⊎∞.+ (a ℕ⊎∞.· c)) ≡˘⟨ lift²-よ {a ℕ⊎∞.· b} {a ℕ⊎∞.· c} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
        よ (a ℕ⊎∞.· b) + よ (a ℕ⊎∞.· c)     ≡˘⟨ cong₂ _+_ (lift²-よ {a} {b} {ℕ⊎∞._·_} {·₁} ·-continuous) (lift²-よ {a} {c} {ℕ⊎∞._·_} {·₁} ·-continuous) ⟩
        よ a · よ b + よ a · よ c            ∎)
      , Coℕ-density³ Coℕ-¬¬-separated λ c a b →
        (よ a + よ b) · よ c                 ≡⟨ cong (_· よ c) (lift²-よ {a} {b} {ℕ⊎∞._+_} {+₁} +-continuous) ⟩
        よ (a ℕ⊎∞.+ b) · よ c               ≡⟨ lift²-よ {a ℕ⊎∞.+ b} {c} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
        よ ((a ℕ⊎∞.+ b) ℕ⊎∞.· c)           ≡⟨ cong よ (S.·-distribʳ-+ c a b) ⟩
        よ ((a ℕ⊎∞.· c) ℕ⊎∞.+ (b ℕ⊎∞.· c)) ≡˘⟨ lift²-よ {a ℕ⊎∞.· c} {b ℕ⊎∞.· c} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
        よ (a ℕ⊎∞.· c) + よ (b ℕ⊎∞.· c)     ≡˘⟨ cong₂ _+_ (lift²-よ {a} {c} {ℕ⊎∞._·_} {·₁} ·-continuous) (lift²-よ {b} {c} {ℕ⊎∞._·_} {·₁} ·-continuous) ⟩
        よ a · よ c + よ b · よ c             ∎
      }
    ; zero = (Coℕ-density Coℕ-¬¬-separated λ a →
      ⌞ 0 ⌟ · よ a           ≡⟨ lift²-よ {ℕ⊎∞.⌞ 0 ⌟} {a} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
      よ (ℕ⊎∞.⌞ 0 ⌟ ℕ⊎∞.· a) ≡⟨ cong よ (S.·-zeroˡ a) ⟩
      ⌞ 0 ⌟                 ∎)
    , Coℕ-density Coℕ-¬¬-separated λ a →
      よ a · ⌞ 0 ⌟           ≡⟨ lift²-よ {a} {ℕ⊎∞.⌞ 0 ⌟} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
      よ (a ℕ⊎∞.· ℕ⊎∞.⌞ 0 ⌟) ≡⟨ cong よ (S.·-zeroʳ a) ⟩
      ⌞ 0 ⌟                 ∎
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = PE.isMagma _∧_
        ; assoc = λ n m o → ext∈ λ x → B.∨-assoc (n .proj₁ x) _ _
        }
      ; idem = λ n → ext∈ λ x → B.∨-idem _
      }
    ; comm = λ n m → ext∈ λ x → B.∨-comm (x ∈ n) _
    }
  ; ·-distrib-∧ = (Coℕ-density³ Coℕ-¬¬-separated λ a b c →
    よ a · (よ b ∧ よ c) ≡⟨ cong (よ a ·_) (∧-よ {b} {c}) ⟩
    よ a · よ (b ℕ⊎∞.∧ c) ≡⟨ lift²-よ {a} {b ℕ⊎∞.∧ c} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
    よ (a ℕ⊎∞.· (b ℕ⊎∞.∧ c)) ≡⟨ cong よ (S.·-distribˡ-∧ a b c) ⟩
    よ ((a ℕ⊎∞.· b) ℕ⊎∞.∧ (a ℕ⊎∞.· c)) ≡˘⟨ ∧-よ {a ℕ⊎∞.· b} {a ℕ⊎∞.· c} ⟩
    よ (a ℕ⊎∞.· b) ∧ よ (a ℕ⊎∞.· c) ≡˘⟨ cong₂ _∧_ (lift²-よ {a} {b} {ℕ⊎∞._·_} {·₁} ·-continuous) (lift²-よ {a} {c} {ℕ⊎∞._·_} {·₁} ·-continuous) ⟩
    よ a · よ b ∧ よ a · よ c ∎)
  , Coℕ-density³ Coℕ-¬¬-separated λ c a b →
    (よ a ∧ よ b) · よ c                 ≡⟨ cong (_· よ c) (∧-よ {a} {b}) ⟩
    よ (a ℕ⊎∞.∧ b) · よ c               ≡⟨ lift²-よ {a ℕ⊎∞.∧ b} {c} {ℕ⊎∞._·_} {·₁} ·-continuous ⟩
    よ ((a ℕ⊎∞.∧ b) ℕ⊎∞.· c)           ≡⟨ cong よ (S.·-distribʳ-∧ c a b) ⟩
    よ ((a ℕ⊎∞.· c) ℕ⊎∞.∧ (b ℕ⊎∞.· c)) ≡˘⟨ ∧-よ {a ℕ⊎∞.· c} {b ℕ⊎∞.· c} ⟩
    よ (a ℕ⊎∞.· c) ∧ よ (b ℕ⊎∞.· c)     ≡˘⟨ cong₂ _∧_ (lift²-よ {a} {c} {ℕ⊎∞._·_} {·₁} ·-continuous) (lift²-よ {b} {c} {ℕ⊎∞._·_} {·₁} ·-continuous) ⟩
    よ a · よ c ∧ よ b · よ c             ∎
  ; +-distrib-∧ = (Coℕ-density³ Coℕ-¬¬-separated λ a b c →
    よ a + (よ b ∧ よ c)                 ≡⟨ cong (よ a +_) (∧-よ {b} {c}) ⟩
    よ a + よ (b ℕ⊎∞.∧ c)               ≡⟨ lift²-よ {a} {b ℕ⊎∞.∧ c} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
    よ (a ℕ⊎∞.+ (b ℕ⊎∞.∧ c))           ≡⟨ cong よ (S.+-distribˡ-∧ a b c) ⟩
    よ ((a ℕ⊎∞.+ b) ℕ⊎∞.∧ (a ℕ⊎∞.+ c)) ≡˘⟨ ∧-よ {a ℕ⊎∞.+ b} {a ℕ⊎∞.+ c} ⟩
    よ (a ℕ⊎∞.+ b) ∧ よ (a ℕ⊎∞.+ c)     ≡˘⟨ cong₂ _∧_ (lift²-よ {a} {b} {ℕ⊎∞._+_} {+₁} +-continuous) (lift²-よ {a} {c} {ℕ⊎∞._+_} {+₁} +-continuous) ⟩
    (よ a + よ b) ∧ よ a + よ c           ∎)
  , Coℕ-density³ Coℕ-¬¬-separated λ c a b →
    (よ a ∧ よ b) + よ c                 ≡⟨ cong (_+ よ c) (∧-よ {a} {b}) ⟩
    よ (a ℕ⊎∞.∧ b) + よ c               ≡⟨ lift²-よ {a ℕ⊎∞.∧ b} {c} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
    よ ((a ℕ⊎∞.∧ b) ℕ⊎∞.+ c)           ≡⟨ cong よ (S.+-distribʳ-∧ c a b) ⟩
    よ ((a ℕ⊎∞.+ c) ℕ⊎∞.∧ (b ℕ⊎∞.+ c)) ≡˘⟨ ∧-よ {a ℕ⊎∞.+ c} {b ℕ⊎∞.+ c} ⟩
    よ (a ℕ⊎∞.+ c) ∧ よ (b ℕ⊎∞.+ c)     ≡˘⟨ cong₂ _∧_ (lift²-よ {a} {c} {ℕ⊎∞._+_} {+₁} +-continuous) (lift²-よ {b} {c} {ℕ⊎∞._+_} {+₁} +-continuous) ⟩
    (よ a + よ c) ∧ よ b + よ c           ∎
  }
  where
    open Tools.Reasoning.PropositionalEquality
    module M = Graded.Modality ℕ⊎∞
    module S = M.Semiring-with-meet ℕ⊎∞.ℕ⊎∞-semiring-with-meet

true≢false : true ≢ false
true≢false ()

𝟙≢𝟘 : ⌞ 1 ⌟ ≢ ⌞ 0 ⌟
𝟙≢𝟘 h = true≢false (cong (0 ∈_) h)

-- Note that we don't have full decidable equality as required by the definition
-- of a modality in [ICFP 2023].
is-𝟘? : (n : Coℕ) → Dec (n ≡ ⌞ 0 ⌟)
is-𝟘? n with B.T? (0 ∈ n)
... | yes 0∈n = no λ h → subst T (cong (0 ∈_) h) 0∈n
... | no 0∉n = yes (ext0 0∉n)

≤0 : {n : Coℕ} → n ≤ ⌞ 0 ⌟
≤0 = ext∈ λ _ → sym (B.∨-identityʳ _)

zero-product : {p q : Coℕ} → p · q ≡ ⌞ 0 ⌟ → p ≡ ⌞ 0 ⌟ ⊎ q ≡ ⌞ 0 ⌟
zero-product {p} {q} p·q≡0 with B.T? (0 ∈ p) | cong (0 ∈_) p·q≡0
... | no 0∉p  | _ = inj₁ (ext0 0∉p)
... | yes 0∈p | 0∈p·q with B.T? (0 ∈ q)
... | no 0∉q  = inj₂ (ext0 0∉q)
... | yes 0∈q = ⊥-elim (true≢false 0∈p·q)

-- The semiring has a well-behaved zero.

ext↓ : n ↓ x ≡ ℕ⊎∞.⌞ y ⌟ → n ≡ ⌞ y ⌟
ext↓ {n} {x} {y} h with B.T? (x ∈ n)
... | no x∉n = trans (toℕ n x x∉n .proj₂) (cong よ h)

+-positiveˡ : ∀ {p} {q} → p + q ≡ ⌞ 0 ⌟ → p ≡ ⌞ 0 ⌟
+-positiveˡ {p} {q} p+q≡0 = ext↓ (W.+-positiveˡ p↓0+q↓0≡0)
  where
    module M = Graded.Modality ℕ⊎∞
    module W = M.Has-well-behaved-zero ℕ⊎∞.ℕ⊎∞-has-well-behaved-zero
    p↓0+q↓0≡0 : (p ↓ 0) ℕ⊎∞.+ (q ↓ 0) ≡ ℕ⊎∞.⌞ 0 ⌟
    p↓0+q↓0≡0 = よ-injective (ext0 (B.false→¬T (cong (0 ∈_) p+q≡0)))

∨-conicalˡ : (a b : Bool) → a B.∨ b ≡ false → a ≡ false
∨-conicalˡ false false _ = refl

∧-positiveˡ : {p q : Coℕ} → p ∧ q ≡ ⌞ 0 ⌟ → p ≡ ⌞ 0 ⌟
∧-positiveˡ {p} {q} p∧q≡0 = ext0 (B.false→¬T (∨-conicalˡ _ _ (cong (0 ∈_) p∧q≡0)))

Coℕ-has-well-behaved-zero : Has-well-behaved-zero Coℕ-semiring-with-meet
Coℕ-has-well-behaved-zero = record
  { 𝟙≢𝟘          = 𝟙≢𝟘
  ; is-𝟘?        = is-𝟘?
  ; zero-product = zero-product
  ; +-positiveˡ  = λ {p} {q} → +-positiveˡ {p} {q}
  ; ∧-positiveˡ  = ∧-positiveˡ
  }

private
  module BS =
    BoundedStar
      Coℕ-semiring-with-meet _* *≡+·* (λ _ → inj₁ ≤0)

+-decreasingˡ : ∀ m n → m + n ≤ m
+-decreasingˡ = Coℕ-density² Coℕ-¬¬-separated λ a b →
  よ a + よ b               ≡⟨ lift²-よ {a} {b} {ℕ⊎∞._+_} {+₁} +-continuous ⟩
  よ (a ℕ⊎∞.+ b)           ≡⟨ cong よ (ℕ⊎∞.+-decreasingˡ {a} {b}) ⟩
  よ ((a ℕ⊎∞.+ b) ℕ⊎∞.∧ a) ≡˘⟨ ∧-よ {a ℕ⊎∞.+ b} {a} ⟩
  よ (a ℕ⊎∞.+ b) ∧ よ a     ≡˘⟨ cong (_∧ よ a) (lift²-よ {a} {b} {ℕ⊎∞._+_} {+₁} +-continuous) ⟩
  (よ a + よ b) ∧ よ a       ∎
  where
    open Tools.Reasoning.PropositionalEquality

Coℕ-modality : Modality-variant → Modality
Coℕ-modality variant =
  BS.isModality
    variant
    (λ _ → Coℕ-has-well-behaved-zero)
    (λ _ _ → +-decreasingˡ)
