------------------------------------------------------------------------
-- Some definitions that are re-exported from
-- Definition.Untyped.Properties but do not depend on that module's
-- module parameter
------------------------------------------------------------------------

module Definition.Untyped.Properties.NotParametrised where

open import Definition.Untyped.NotParametrised

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation
open import Tools.PropositionalEquality
open import Tools.Sum as ⊎

open import Induction
open import Induction.WellFounded

private variable
  ℓ m n              : Nat
  A                  : Set _
  P                  : Nat → Set _
  B                  : A
  Γ                  : Con _ _
  ρ ρ′               : Wk _ _
  x y                : Fin _
  l l₁ l₁′ l₂ l₂′ l₃ : Universe-level

------------------------------------------------------------------------
-- Properties of weakening

-- Two weakenings ρ and ρ′ are extensionally equal if they agree on
-- all arguments when interpreted as functions mapping variables to
-- variables.  Formally, they are considered equal iff
--
--   (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
--
-- Intensional (propositional) equality would be too fine.  For
-- instance,
--
--   lift id : Γ∙A ≤ Γ∙A
--
-- is extensionally equal to
--
--   id : Γ∙A ≤ Γ∙A
--
-- but syntactically different.

-- "lift" preserves equality of weakenings.  Or:
-- If two weakenings are equal under wkVar, then they are equal when lifted.

wkVar-lift : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
           → (∀ x → wkVar (lift ρ) x ≡ wkVar (lift ρ′) x)

wkVar-lift eq x0     = refl
wkVar-lift eq (x +1) = cong _+1 (eq x)


wkVar-lifts : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
            → (∀ n x → wkVar (liftn ρ n) x ≡ wkVar (liftn ρ′ n) x)
wkVar-lifts eq 0 x      = eq x
wkVar-lifts eq (1+ n) x = wkVar-lift (wkVar-lifts eq n) x

-- lift id  is extensionally equal to  id.

wkVar-lift-id : (x : Fin (1+ n)) → wkVar (lift id) x ≡ wkVar id x
wkVar-lift-id x0     = refl
wkVar-lift-id (x +1) = refl

wkVar-lifts-id : (n : Nat) (x : Fin (n + m)) → wkVar (liftn id n) x ≡ wkVar id x
wkVar-lifts-id 0 x           = refl
wkVar-lifts-id (1+ n) x0     = refl
wkVar-lifts-id (1+ n) (x +1) = cong _+1 (wkVar-lifts-id n x)

-- id is the identity renaming.

wkVar-id : (x : Fin n) → wkVar id x ≡ x
wkVar-id x = refl

-- The function wkVar commutes with composition.

wkVar-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (x : Fin n) → wkVar ρ (wkVar ρ′ x) ≡ wkVar (ρ • ρ′) x
wkVar-comp id       ρ′        x      = refl
wkVar-comp (step ρ) ρ′        x      = cong _+1 (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) id        x      = refl
wkVar-comp (lift ρ) (step ρ′) x      = cong _+1 (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) (lift ρ′) x0     = refl
wkVar-comp (lift ρ) (lift ρ′) (x +1) = cong _+1 (wkVar-comp ρ ρ′ x)

wkVar-comps : ∀ k → (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (x : Fin (k + n))
            → wkVar (liftn ρ k • liftn ρ′ k) x
            ≡ wkVar (liftn (ρ • ρ′) k) x
wkVar-comps 0      ρ ρ′ x      = refl
wkVar-comps (1+ n) ρ ρ′ x0     = refl
wkVar-comps (1+ n) ρ ρ′ (x +1) = cong _+1 (wkVar-comps n ρ ρ′ x)

opaque

  -- The weakening id is a right identity for composition.

  •-id : ρ • id ≡ ρ
  •-id {ρ = id}     = refl
  •-id {ρ = step _} = cong step •-id
  •-id {ρ = lift _} = refl

opaque

  -- A composition lemma for wk₀.

  liftn-wk₀-•-wk₀ : ∀ n → liftn {k = m} wk₀ n • wk₀ ≡ wk₀
  liftn-wk₀-•-wk₀ 0      = •-id
  liftn-wk₀-•-wk₀ (1+ n) = cong step $ liftn-wk₀-•-wk₀ n

-- The weakening step id • ρ is equal to lift ρ • step id.

lift-step-comp : (ρ : Wk m n) → step id • ρ ≡ lift ρ • step id
lift-step-comp id       = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

opaque

  -- The function wkVar ρ is injective.

  wkVar-injective : wkVar ρ x ≡ wkVar ρ y → x ≡ y
  wkVar-injective = lemma _ _ _
    where
    lemma : ∀ (ρ : Wk m n) x y → wkVar ρ x ≡ wkVar ρ y → x ≡ y
    lemma ρ x0 x0 =
      wkVar ρ x0 ≡ wkVar ρ x0  →⟨ (λ _ → refl) ⟩
      x0 ≡ x0                  □
    lemma id (x +1) (y +1) =
      (x +1) ≡ (y +1)  □
    lemma (lift ρ) (x +1) (y +1) =
      (wkVar ρ x +1) ≡ (wkVar ρ y +1)  →⟨ suc-injective ⟩
      wkVar ρ x ≡ wkVar ρ y            →⟨ wkVar-injective ⟩
      x ≡ y                            →⟨ cong _+1 ⟩
      x +1 ≡ y +1                      □
    lemma (step ρ) x y =
      (wkVar ρ x +1) ≡ (wkVar ρ y +1)  →⟨ suc-injective ⟩
      wkVar ρ x ≡ wkVar ρ y            →⟨ wkVar-injective ⟩
      x ≡ y                            □
    lemma id       x0     (_ +1) ()
    lemma id       (_ +1) x0     ()
    lemma (lift _) x0     (_ +1) ()
    lemma (lift _) (_ +1) x0     ()

------------------------------------------------------------------------
-- A property related to Universe-level

opaque

  -- Equality of universe levels is decidable.

  infix 4 _≟ᵘ_

  _≟ᵘ_ : Decidable (_≡_ {A = Universe-level})
  0ᵘ+ l₁ ≟ᵘ 0ᵘ+ l₂ = Dec-map (cong 0ᵘ+_ , λ { refl → refl }) (l₁ ≟ l₂)
  0ᵘ+ l₁ ≟ᵘ ωᵘ+ l₂ = no (λ ())
  ωᵘ+ l₁ ≟ᵘ 0ᵘ+ l₂ = no (λ ())
  ωᵘ+ l₁ ≟ᵘ ωᵘ+ l₂ = Dec-map (cong ωᵘ+_ , λ { refl → refl }) (l₁ ≟ l₂)

------------------------------------------------------------------------
-- Properties related to _≤ᵘ_ and _<ᵘ_

opaque

  -- The level 0 is the lowest level.

  0≤ᵘ : 0ᵘ ≤ᵘ l
  0≤ᵘ {0ᵘ+ x} = ≤ᵘ-fin z≤′n
  0≤ᵘ {ωᵘ+ x} = ≤ᵘ-fin-inf

opaque

  -- The relation _≤ᵘ_ is transitive.

  ≤ᵘ-trans : l₁ ≤ᵘ l₂ → l₂ ≤ᵘ l₃ → l₁ ≤ᵘ l₃
  ≤ᵘ-trans (≤ᵘ-fin x) (≤ᵘ-fin y) = ≤ᵘ-fin (≤′-trans x y)
  ≤ᵘ-trans (≤ᵘ-fin x) ≤ᵘ-fin-inf = ≤ᵘ-fin-inf
  ≤ᵘ-trans ≤ᵘ-fin-inf (≤ᵘ-inf x) = ≤ᵘ-fin-inf
  ≤ᵘ-trans (≤ᵘ-inf x) (≤ᵘ-inf y) = ≤ᵘ-inf (≤′-trans x y)

opaque

  -- The relation _<ᵘ_ is transitive.

  <ᵘ-trans : l₁ <ᵘ l₂ → l₂ <ᵘ l₃ → l₁ <ᵘ l₃
  <ᵘ-trans (<ᵘ-fin x) (<ᵘ-fin y) = <ᵘ-fin (<′-trans x y)
  <ᵘ-trans (<ᵘ-fin x) <ᵘ-fin-inf = <ᵘ-fin-inf
  <ᵘ-trans <ᵘ-fin-inf (<ᵘ-inf x) = <ᵘ-fin-inf
  <ᵘ-trans (<ᵘ-inf x) (<ᵘ-inf y) = <ᵘ-inf (<′-trans x y)

opaque

  <ᵘ-≤ᵘ-trans : l₁ <ᵘ l₂ → l₂ ≤ᵘ l₃ → l₁ <ᵘ l₃
  <ᵘ-≤ᵘ-trans (<ᵘ-fin x) (≤ᵘ-fin y) = <ᵘ-fin (≤′-trans x y)
  <ᵘ-≤ᵘ-trans (<ᵘ-fin x) ≤ᵘ-fin-inf = <ᵘ-fin-inf
  <ᵘ-≤ᵘ-trans <ᵘ-fin-inf (≤ᵘ-inf x) = <ᵘ-fin-inf
  <ᵘ-≤ᵘ-trans (<ᵘ-inf x) (≤ᵘ-inf y) = <ᵘ-inf (≤′-trans x y)

opaque

  -- The relation _<ᵘ_ is contained in _≤ᵘ_.

  <ᵘ→≤ᵘ : l₁ <ᵘ l₂ → l₁ ≤ᵘ l₂
  <ᵘ→≤ᵘ (<ᵘ-fin x) = ≤ᵘ-fin (<′→≤′ x)
  <ᵘ→≤ᵘ <ᵘ-fin-inf = ≤ᵘ-fin-inf
  <ᵘ→≤ᵘ (<ᵘ-inf x) = ≤ᵘ-inf (<′→≤′ x)

-- The relation _<ᵘ_ is well-founded.

private
  fin-accessible : ∀ n → Acc _<ᵘ_ (0ᵘ+ n)
  fin-wfrec : ∀ n → WfRec _<ᵘ_ (Acc _<ᵘ_) (0ᵘ+ n)

  fin-accessible n = acc (fin-wfrec n)

  fin-wfrec .(1+ n) (<ᵘ-fin {l = n} ≤′-refl) = fin-accessible n
  fin-wfrec .(1+ n) (<ᵘ-fin (≤′-step {n} p)) = fin-wfrec n (<ᵘ-fin p)

  inf-accessible : ∀ n → Acc _<ᵘ_ (ωᵘ+ n)
  inf-wfrec : ∀ n → WfRec _<ᵘ_ (Acc _<ᵘ_) (ωᵘ+ n)

  inf-accessible n = acc (inf-wfrec n)

  inf-wfrec n (<ᵘ-fin-inf {l}) = fin-accessible l
  inf-wfrec .(1+ n) (<ᵘ-inf {l = n} ≤′-refl) = inf-accessible n
  inf-wfrec .(1+ n) (<ᵘ-inf (≤′-step {n} p)) = inf-wfrec n (<ᵘ-inf p)

<ᵘ-wellFounded : WellFounded _<ᵘ_
<ᵘ-wellFounded (0ᵘ+ n) = fin-accessible n
<ᵘ-wellFounded (ωᵘ+ n) = inf-accessible n

<ᵘ-Rec : ∀ {ℓ} → RecStruct Universe-level ℓ ℓ
<ᵘ-Rec = WfRec _<ᵘ_

module _ {ℓ} where
  open All <ᵘ-wellFounded ℓ public
    renaming ( wfRecBuilder to <ᵘ-recBuilder
             ; wfRec        to <ᵘ-rec
             )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- Properties related to _⊔ᵘ_

opaque

  -- The level l₁ is bounded by the maximum of l₁ and l₂.

  ≤ᵘ⊔ᵘʳ : l₁ ≤ᵘ l₁ ⊔ᵘ l₂
  ≤ᵘ⊔ᵘʳ {0ᵘ+ x} {0ᵘ+ y} = ≤ᵘ-fin ≤′⊔ʳ
  ≤ᵘ⊔ᵘʳ {0ᵘ+ x} {ωᵘ+ y} = ≤ᵘ-fin-inf
  ≤ᵘ⊔ᵘʳ {ωᵘ+ x} {0ᵘ+ y} = ≤ᵘ-refl
  ≤ᵘ⊔ᵘʳ {ωᵘ+ x} {ωᵘ+ y} = ≤ᵘ-inf ≤′⊔ʳ

opaque

  -- The level l₂ is bounded by the maximum of l₁ and l₂.

  ≤ᵘ⊔ᵘˡ : l₂ ≤ᵘ l₁ ⊔ᵘ l₂
  ≤ᵘ⊔ᵘˡ {0ᵘ+ x} {0ᵘ+ y} = ≤ᵘ-fin ≤′⊔ˡ
  ≤ᵘ⊔ᵘˡ {0ᵘ+ x} {ωᵘ+ y} = ≤ᵘ-fin-inf
  ≤ᵘ⊔ᵘˡ {ωᵘ+ x} {0ᵘ+ y} = ≤ᵘ-refl
  ≤ᵘ⊔ᵘˡ {ωᵘ+ x} {ωᵘ+ y} = ≤ᵘ-inf ≤′⊔ˡ

opaque

  -- The function _⊔ᵘ_ is monotone.

  ⊔ᵘ-mono : l₁ ≤ᵘ l₁′ → l₂ ≤ᵘ l₂′ → l₁ ⊔ᵘ l₂ ≤ᵘ l₁′ ⊔ᵘ l₂′
  ⊔ᵘ-mono (≤ᵘ-fin x) (≤ᵘ-fin y) = ≤ᵘ-fin (⊔-mono x y)
  ⊔ᵘ-mono (≤ᵘ-fin x) ≤ᵘ-fin-inf = ≤ᵘ-fin-inf
  ⊔ᵘ-mono (≤ᵘ-fin x) (≤ᵘ-inf y) = ≤ᵘ-inf y
  ⊔ᵘ-mono ≤ᵘ-fin-inf (≤ᵘ-fin x) = ≤ᵘ-fin-inf
  ⊔ᵘ-mono ≤ᵘ-fin-inf ≤ᵘ-fin-inf = ≤ᵘ-fin-inf
  ⊔ᵘ-mono ≤ᵘ-fin-inf (≤ᵘ-inf x) = ≤ᵘ-inf (≤′-trans x ≤′⊔ˡ)
  ⊔ᵘ-mono (≤ᵘ-inf x) (≤ᵘ-fin y) = ≤ᵘ-inf x
  ⊔ᵘ-mono (≤ᵘ-inf x) ≤ᵘ-fin-inf = ≤ᵘ-inf (≤′-trans x ≤′⊔ʳ)
  ⊔ᵘ-mono (≤ᵘ-inf x) (≤ᵘ-inf y) = ≤ᵘ-inf (⊔-mono x y)

opaque

  -- 0 is a left identity for _⊔ᵘ_.

  ⊔ᵘ-identityˡ : 0ᵘ ⊔ᵘ l ≡ l
  ⊔ᵘ-identityˡ {0ᵘ+ l} = refl
  ⊔ᵘ-identityˡ {ωᵘ+ l} = refl

opaque

  -- The function _⊔ᵘ_ is idempotent.

  ⊔ᵘ-idem : l ⊔ᵘ l ≡ l
  ⊔ᵘ-idem {0ᵘ+ l} = cong 0ᵘ+_ (⊔-idem l)
  ⊔ᵘ-idem {ωᵘ+ l} = cong ωᵘ+_ (⊔-idem l)

------------------------------------------------------------------------
-- Properties related to Empty-con and _or-empty_

opaque

  -- Empty-con is decidable.

  Empty-con? : Dec (Empty-con Γ)
  Empty-con? {Γ = ε}     = yes ε
  Empty-con? {Γ = _ ∙ _} = no (λ ())

opaque

  -- A characterisation lemma for _or-empty_.

  or-empty⇔ : A or-empty Γ ⇔ (A ⊎ Empty-con Γ)
  or-empty⇔ =
      (λ where
         (possibly-nonempty ⦃ ok ⦄) → inj₁ ok
         ε                          → inj₂ ε)
    , (λ where
         (inj₁ x) → possibly-nonempty ⦃ ok = x ⦄
         (inj₂ ε) → ε)

opaque

  -- If A is decided, then A or-empty_ is decidable.

  infix 4 _or-empty?

  _or-empty? : Dec A → Dec (A or-empty Γ)
  A? or-empty? = Dec-map (sym⇔ or-empty⇔) (A? ⊎-dec Empty-con?)

opaque

  -- If the size of Γ is positive, then A or-empty Γ implies A.

  or-empty-1+→ :
    {Γ : Con P (1+ n)}
    ⦃ ok : A or-empty Γ ⦄ →
    A
  or-empty-1+→ ⦃ ok = possibly-nonempty ⦃ ok ⦄ ⦄ = ok

opaque

  -- A or-empty Γ ∙ B implies A or-empty Γ.

  or-empty-∙→ :
    ⦃ ok : A or-empty Γ ∙ B ⦄ →
    A or-empty Γ
  or-empty-∙→ = possibly-nonempty ⦃ ok = or-empty-1+→ ⦄

opaque

  -- A map function for _or-empty_.

  or-empty-map :
    (A → B) → A or-empty Γ → B or-empty Γ
  or-empty-map f =
    or-empty⇔ .proj₂ ∘→ ⊎.map f idᶠ ∘→ or-empty⇔ .proj₁

------------------------------------------------------------------------
-- Other properties

-- Decidability of Strength equality
decStrength : Decidable (_≡_ {A = Strength})
decStrength 𝕤 𝕤 = yes refl
decStrength 𝕤 𝕨 = no λ{()}
decStrength 𝕨 𝕤 = no λ{()}
decStrength 𝕨 𝕨 = yes refl

-- Decidability of equality for BinderMode.
decBinderMode : Decidable (_≡_ {A = BinderMode})
decBinderMode = λ where
  BMΠ      BMΠ      → yes refl
  BMΠ      (BMΣ _)  → no (λ ())
  (BMΣ _)  BMΠ      → no (λ ())
  (BMΣ s₁) (BMΣ s₂) → case decStrength s₁ s₂ of λ where
    (yes refl) → yes refl
    (no s₁≢s₂)    → no λ where
      refl → s₁≢s₂ refl
