------------------------------------------------------------------------
-- Soundness of the extraction function.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Consequences.Soundness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions M)
  where

open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Untyped M hiding (_∷_)

open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
import Definition.Typed.Consequences.Canonicity TR as TC
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.LogicalRelation TR

open import Graded.Context 𝕄
import Graded.Derived.Erased.Typed TR as ET
import Graded.Derived.Erased.Untyped 𝕄 as Erased
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

import Graded.Erasure.Target as T
import Graded.Erasure.Extraction 𝕄 as E
open import Graded.Erasure.SucRed TR
import Graded.Erasure.LogicalRelation TR as LR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Fundamental TR UR as LRF
import Graded.Erasure.LogicalRelation.Irrelevance TR as LRI
import Graded.Erasure.LogicalRelation.Subsumption TR as LRS

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation
import Tools.PropositionalEquality as PE hiding (trans)
open import Tools.Sum

private
  variable
    n : Nat
    Γ Δ : Con Term _
    t t′ u F : Term n
    G : Term (1+ n)
    v v′ w : T.Term n
    p : M
    s : Strength

-- WH reduction soundness of natural numbers

-- Canonical representation of natural numbers

sucᵏ : (k : Nat) → Term n
sucᵏ 0      = zero
sucᵏ (1+ n) = suc (sucᵏ n)

sucᵏ′ : (k : Nat) → T.Term n
sucᵏ′ 0      = T.zero
sucᵏ′ (1+ n) = T.suc (sucᵏ′ n)

-- Some results that are proved under the assumption that the
-- modality's zero is well-bahved.

module _
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

  open E is-𝟘?

  -- The following results make use of some assumptions.

  module Soundness′
    (FA : Fundamental-assumptions Δ)
    {{eqrel : EqRelSet TR}}
    where

    open Fundamental-assumptions FA

    open LR is-𝟘? well-formed
    open LRF.Fundamental FA
    open LRI is-𝟘? well-formed
    open LRS is-𝟘? well-formed

    -- Helper lemma for WH reduction soundness of zero
    -- If t ® v ∷ℕ  and t ⇒* zero then v ⇒* zero

    soundness-zero′ : t ® v ∷ℕ → Δ ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
    soundness-zero′ (zeroᵣ t⇒zero′ v⇒zero) t⇒zero = v⇒zero
    soundness-zero′ (sucᵣ t⇒suc v⇒suc t®v) t⇒zero
      with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
    ... | ()

    -- WH reduction soundness of zero
    -- If t ⇒* zero and 𝟘ᶜ ▸ t then erase t ⇒* zero

    soundness-zero :
      Δ ⊢ t ⇒* zero ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.zero
    soundness-zero t⇒zero 𝟘▸t =
      let ⊢t = redFirst*Term t⇒zero
          [ℕ] , t®t′ = fundamentalErased ⊢t 𝟘▸t
          t®t″ = irrelevanceTerm {l′ = ¹} [ℕ]
                   (ℕᵣ (idRed:*: (ℕⱼ well-formed)))
                   (t®t′ ◀≢𝟘 non-trivial)
      in  soundness-zero′ t®t″ t⇒zero

    -- Helper lemma for WH reduction soundness of suc
    -- If t ® v ∷ℕ  and t ⇒* suc t′ then v ⇒* suc v′ and t′ ® v′ ∷ℕ
    -- for some v′

    soundness-suc′ : t ® v ∷ℕ → Δ ⊢ t ⇒* suc t′ ∷ ℕ
                   → ∃ λ v′ → v T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
    soundness-suc′ (zeroᵣ t⇒zero v⇒zero) t⇒suc
      with whrDet*Term (t⇒zero , zeroₙ) (t⇒suc , sucₙ)
    ... | ()
    soundness-suc′ (sucᵣ {v′ = v′} t⇒suc′ v⇒suc t®v) t⇒suc
      with whrDet*Term (t⇒suc , sucₙ) (t⇒suc′ , sucₙ)
    ... | PE.refl = v′ , (v⇒suc , t®v)

    -- WH reduction soundness of suc
    -- If t ⇒* suc t′ and 𝟘ᶜ ▸ t then erase t ⇒* suc v′ and t′ ® v′ ∷ℕ
    -- for some v′

    soundness-suc : Δ ⊢ t ⇒* suc t′ ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
                  → ∃ λ v′ → erase t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
    soundness-suc t⇒suc 𝟘▸t =
      let ⊢t = redFirst*Term t⇒suc
          [ℕ] , t®t′ = fundamentalErased ⊢t 𝟘▸t
          t®t″ = irrelevanceTerm {l′ = ¹} [ℕ]
                   (ℕᵣ (idRed:*: (ℕⱼ well-formed)))
                   (t®t′ ◀≢𝟘 non-trivial)
      in  soundness-suc′ t®t″ t⇒suc

    -- Helper lemma for soundness of natural numbers

    soundness-ℕ′ :
      t ® v ∷ℕ → ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × v ⇒ˢ* sucᵏ′ n
    soundness-ℕ′ (zeroᵣ x x₁) = 0 , whred* x , whred*′ x₁
    soundness-ℕ′ (sucᵣ x x₁ t®v) =
      let n , d , d′ = soundness-ℕ′ t®v
      in  1+ n , ⇒ˢ*∷ℕ-trans (whred* x) (sucred* d)
               , ⇒ˢ*-trans (whred*′ x₁) (sucred*′ d′)

    -- Helper lemma for WH reduction soundness of unit

    soundness-star′ : t ® v ∷Unit⟨ s ⟩ → v T.⇒* T.star
    soundness-star′ (starᵣ _ v⇒star) = v⇒star

  -- The following results make use of some assumptions.

  module Soundness (FA⁻ : Fundamental-assumptions⁻ Δ) where

    private module L (⊢Δ : ⊢ Δ) where

      open import Definition.Typed.EqRelInstance TR public

      FA : Fundamental-assumptions Δ
      FA = record
        { well-formed       = ⊢Δ
        ; other-assumptions = FA⁻
        }

      open Soundness′ FA public

      open LRF.Fundamental FA public
      open LRI is-𝟘? ⊢Δ public
      open LRS is-𝟘? ⊢Δ public

    -- Soundness for erasure of natural numbers
    -- Well-typed terms of the natural number type reduce to numerals
    -- if erased matches are disallowed or the term is closed.
    --
    -- Note the assumptions of the local module Soundness.

    soundness-ℕ : Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
                → ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase t ⇒ˢ* sucᵏ′ n
    soundness-ℕ ⊢t 𝟘▸t =
      let [ℕ] , t®v = fundamentalErased ⊢t 𝟘▸t
      in  soundness-ℕ′ $
          irrelevanceTerm {l′ = ¹} [ℕ] (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
            (t®v ◀≢𝟘 non-trivial)
      where
      ⊢Δ = wfTerm ⊢t

      open L ⊢Δ

    -- A variant of soundness-ℕ which only considers the source
    -- language.
    --
    -- Note the assumptions of the local module Soundness.

    soundness-ℕ-only-source :
      Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
    soundness-ℕ-only-source ⊢t ▸t =
      case soundness-ℕ ⊢t ▸t of λ {
        (n , t⇒ˢ*n , _) →
          n , t⇒ˢ*n }

    -- WH reduction soundness of unit
    --
    -- Note the assumptions of the local module Soundness.

    soundness-star :
      Δ ⊢ t ∷ Unit s → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → erase t T.⇒* T.star
    soundness-star ⊢t γ▸t =
      let [⊤] , t®t′ = fundamentalErased ⊢t γ▸t
          ok = ⊢∷Unit→Unit-allowed ⊢t
          t®t″ = irrelevanceTerm {l′ = ¹}
                   [⊤]
                   (Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok))
                   (t®t′ ◀≢𝟘 non-trivial)
      in  soundness-star′ t®t″
      where
      ⊢Δ = wfTerm ⊢t

      open L ⊢Δ

  -- If the context is empty, then the results in Soundness hold
  -- without any further assumptions.

  module Soundness₀ where

    open Soundness fundamental-assumptions⁻₀ public

-- If Prodrec-allowed 𝟘 p 𝟘 holds for some p (which means that certain
-- kinds of erased matches are allowed), and if additionally
-- Σʷ-allowed p 𝟘 holds, then there is a counterexample to
-- soundness-ℕ-only-source without the assumption "erased matches are
-- not allowed unless the context is empty" (and without the
-- assumption that the modality's zero is well-behaved).

soundness-ℕ-only-source-counterexample₁ :
  Prodrec-allowed 𝟘 p 𝟘 →
  Σʷ-allowed p 𝟘 →
  let Δ = ε ∙ (Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
      t = prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero
  in
  Consistent Δ ×
  Δ ⊢ t ∷ ℕ ×
  𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
  ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
soundness-ℕ-only-source-counterexample₁ {p = p} P-ok Σʷ-ok =
    inhabited-consistent
      (singleSubst (prodⱼ ε⊢ℕ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok))
  , ⊢prodrec
  , sub
      (prodrecₘ var
         (sub zeroₘ $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟙 · 𝟘 · p ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-zeroˡ _) ∙ PE.refl ⟩
            𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘      ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                      ∎)
         (sub ℕₘ $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                ∎)
         P-ok)
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         𝟘ᶜ                           ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ                     ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝) +ᶜ 𝟘ᶜ  ∎)
  , λ where
      (0    , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _)))
      (1+ _ , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _)))
  where
  ε⊢ℕ = ℕⱼ ε
  ⊢εℕ = ε ∙ ε⊢ℕ
  εℕ⊢ℕ = ℕⱼ ⊢εℕ
  ε⊢Σ = ΠΣⱼ ε⊢ℕ εℕ⊢ℕ Σʷ-ok
  ⊢εΣ = ε ∙ ε⊢Σ
  εΣ⊢ℕ = ℕⱼ ⊢εΣ
  ⊢εΣℕ = ⊢εΣ ∙ εΣ⊢ℕ
  εΣℕ⊢ℕ = ℕⱼ ⊢εΣℕ
  εΣ⊢Σ = ΠΣⱼ εΣ⊢ℕ εΣℕ⊢ℕ Σʷ-ok
  ⊢εΣΣ = ⊢εΣ ∙ εΣ⊢Σ
  εΣΣ⊢ℕ = ℕⱼ ⊢εΣΣ
  ⊢εΣℕℕ = ⊢εΣℕ ∙ εΣℕ⊢ℕ
  ⊢prodrec =
    prodrecⱼ {r = 𝟘} εΣ⊢ℕ εΣℕ⊢ℕ εΣΣ⊢ℕ (var₀ ε⊢Σ) (zeroⱼ ⊢εΣℕℕ) Σʷ-ok

opaque

  -- If []-cong-allowed holds, then there is a counterexample to
  -- soundness-ℕ-only-source without the assumption "erased matches
  -- are not allowed unless the context is empty" (and without the
  -- assumption that the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₂ :
    []-cong-allowed s →
    let Δ = ε ∙ Id ℕ zero zero
        open Erased s
        t = J 𝟘 𝟘 (Erased ℕ) ([ zero ]) ℕ zero ([ zero ])
              ([]-cong s ℕ zero zero (var {n = 1} x0))
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₂ {s = s} ok =
    case ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))
    , Jⱼ′ (ℕⱼ (J-motive-context ([]ⱼ (zeroⱼ ⊢Id))))
        (zeroⱼ ⊢Id) ([]-congⱼ′ ok (var ⊢Id here))
    , Jₘ′ (▸Erased s ℕₘ) (▸[] s zeroₘ)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         sub ℕₘ $ begin
           𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                  ∎)
        zeroₘ (▸[] s zeroₘ) ([]-congₘ ℕₘ zeroₘ zeroₘ var)
        (≤ᶜ-reflexive (≈ᶜ-sym ω·ᶜ⋀ᶜ⁵𝟘ᶜ))
    , (λ where
         (0 , whred J⇒ ⇨ˢ _) →
           whnfRedTerm J⇒ (ne (Jₙ ([]-congₙ (var _))))
         (1+ _ , whred J⇒ ⇨ˢ _) →
           whnfRedTerm J⇒ (ne (Jₙ ([]-congₙ (var _))))) }
    where
    open ET ([]-cong→Erased ok)

opaque

  -- If Erased-matches-for-J holds, then there is a counterexample to
  -- soundness-ℕ-only-source without the assumption "erased matches
  -- are not allowed unless the context is empty" (and without the
  -- assumption that the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₃ :
    Erased-matches-for-J →
    let Δ = ε ∙ Id ℕ zero zero
        t = J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0)
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₃ ok =
    case ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))
    , Jⱼ′ (ℕⱼ (J-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
    , J₀ₘ ok ℕₘ zeroₘ
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         sub ℕₘ $ begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                              ∎)
        zeroₘ zeroₘ var
    , (λ where
         (0    , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne (Jₙ (var _)))
         (1+ _ , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne (Jₙ (var _)))) }

opaque

  -- If K-allowed and Erased-matches-for-K hold, then there is a
  -- counterexample to soundness-ℕ-only-source without the assumption
  -- "erased matches are not allowed unless the context is empty" (and
  -- without the assumption that the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₄ :
    K-allowed →
    Erased-matches-for-K →
    let Δ = ε ∙ Id ℕ zero zero
        t = K 𝟘 ℕ zero ℕ zero (var {n = 1} x0)
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₄ K-ok K₀-ok =
    case ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))
    , Kⱼ′ (ℕⱼ (K-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
        K-ok
    , K₀ₘ K₀-ok ℕₘ zeroₘ
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         sub ℕₘ $ begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                ∎)
        zeroₘ var
    , (λ where
         (0    , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne (Kₙ (var _)))
         (1+ _ , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne (Kₙ (var _)))) }

module _ (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘)) where

  open E is-𝟘?

  -- Run-time canonicity for a given term with respect to a given
  -- context.

  Run-time-canonicity-for : Con Term n → Term n → Set a
  Run-time-canonicity-for Δ t =
    ∃₂ λ n u → Δ ⊢ u ∷ Id ℕ t (sucᵏ n) × erase t ⇒ˢ* sucᵏ′ n

  -- Above some counterexamples to variants of soundness-ℕ-only-source
  -- are presented. Those counterexamples are (at the time of writing)
  -- not counterexamples to "run-time canonicity holds for well-typed,
  -- well-resourced terms of type ℕ in consistent contexts".

  soundness-ℕ-only-target-not-counterexample₁ :
    Σʷ-allowed p 𝟘 →
    Run-time-canonicity-for
      (ε ∙ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
      (prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero)
  soundness-ℕ-only-target-not-counterexample₁ {p} ok
    with is-𝟘? 𝟘
  ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
  ... | yes _ =
      0
    , subst ℕ² (Id ℕ pr zero) 0,0 (var x0) η rfl
    , ⊢subst (Idⱼ ⊢pr (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ])))
        (⊢Σʷ-η-prodʷ-fstʷ-sndʷ (var₀ (⊢ℕ² ε)))
        (rflⱼ′
           (prodrec 𝟘 p 𝟘 ℕ 0,0 zero  ≡⟨ prodrec-β-≡ (ℕⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
                                           (fstʷⱼ (var₀ (⊢ℕ² ε))) (sndʷⱼ (var₀ (⊢ℕ² ε)))
                                           (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ℕⱼ ] ∙[ ℕⱼ ])) ok ⟩⊢∎
            zero                      ∎))
    , trans (whred T.prodrec-β) refl
    where
    open Fstʷ-sndʷ 𝟘 𝟘

    ℕ² : Term n
    ℕ² = Σʷ p , 𝟘 ▷ ℕ ▹ ℕ

    Δ′ : Con Term 1
    Δ′ = ε ∙ ℕ²

    pr : Term 2
    pr = prodrec _ _ _ _ (var x0) zero

    0,0 : Term 1
    0,0 = prodʷ _ (fstʷ _ _ (var x0)) (sndʷ _ _ ℕ ℕ (var x0))

    η : Term 1
    η = Σʷ-η-prodʷ-fstʷ-sndʷ _ _ _ _ (var x0)

    ⊢ℕ² : ⊢ Γ → Γ ⊢ ℕ²
    ⊢ℕ² ⊢Γ = ΠΣⱼ′ (ℕⱼ (⊢Γ ∙[ ℕⱼ ])) ok

    ⊢pr : Δ′ ∙ ℕ² ⊢ pr ∷ ℕ
    ⊢pr =
      prodrecⱼ′ (ℕⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
        (var₀ (⊢ℕ² (ε ∙[ ⊢ℕ² ])))
        (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ℕⱼ ] ∙[ ℕⱼ ]))

  opaque

    soundness-ℕ-only-target-not-counterexample₂ :
      []-cong-allowed s →
      let open Erased s in
      Run-time-canonicity-for
        (ε ∙ Id ℕ zero zero)
        (J 𝟘 𝟘 (Erased ℕ) ([ zero ]) ℕ zero ([ zero ])
           ([]-cong s ℕ zero zero (var {n = 1} x0)))
    soundness-ℕ-only-target-not-counterexample₂ {s} ok =
        _
      , J 𝟘 𝟘 ℕ zero
          (Id ℕ
              (J 𝟘 𝟘 (Erased ℕ) Er.[ zero ] ℕ zero Er.[ var x1 ]
                 ([]-cong s ℕ zero (var x1) (var x0)))
              zero)
          rfl zero (var x0)
      , Jⱼ′
          (Idⱼ
             (Jⱼ′ (ℕⱼ (J-motive-context ([]ⱼ ⊢zero))) ⊢zero
                ([]-congⱼ′ ok
                   (var₀ (J-motive-context-type (zeroⱼ ⊢Δ)))))
             ⊢zero)
          (rflⱼ′
             (J 𝟘 𝟘 (Erased ℕ) Er.[ zero ] ℕ zero Er.[ zero ]
                ([]-cong s ℕ zero zero rfl)                        ≡⟨ J-cong′ (refl (Erasedⱼ (ℕⱼ ⊢Δ))) (refl ([]ⱼ (zeroⱼ ⊢Δ))) (refl ⊢ℕ)
                                                                        (refl (zeroⱼ ⊢Δ)) (refl ([]ⱼ (zeroⱼ ⊢Δ)))
                                                                        ([]-cong-β (zeroⱼ ⊢Δ) PE.refl ok) ⟩⊢

              J 𝟘 𝟘 (Erased ℕ) Er.[ zero ] ℕ zero Er.[ zero ] rfl  ≡⟨ J-β-≡ ([]ⱼ (zeroⱼ ⊢Δ)) ⊢ℕ (zeroⱼ ⊢Δ) ⟩⊢∎

              zero                                                 ∎))
          (var₀ ⊢0≡0)
      , refl
      where
      open module Er = Erased s using (Erased)
      open ET ([]-cong→Erased ok)

      Δ′ : Con Term 1
      Δ′ = ε ∙ Id ℕ zero zero

      ⊢0≡0 : ε ⊢ Id ℕ zero zero
      ⊢0≡0 = Idⱼ (zeroⱼ ε) (zeroⱼ ε)

      ⊢Δ : ⊢ Δ′
      ⊢Δ = ε ∙ ⊢0≡0

      ⊢ℕ : Δ′ ∙ Erased ℕ ∙ Id (Erased ℕ) Er.[ zero ] (var x0) ⊢ ℕ
      ⊢ℕ = ℕⱼ (J-motive-context ([]ⱼ (zeroⱼ ⊢Δ)))

      ⊢zero : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
      ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

  opaque

    soundness-ℕ-only-target-not-counterexample₃ :
      Run-time-canonicity-for
        (ε ∙ Id ℕ zero zero)
        (J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0))
    soundness-ℕ-only-target-not-counterexample₃ =
        _
      , J 𝟘 𝟘 ℕ zero
          (Id ℕ (J 𝟘 𝟘 ℕ zero ℕ zero (var x1) (var x0)) zero)
          rfl zero (var x0)
      , Jⱼ′
          (Idⱼ
             (Jⱼ′ (ℕⱼ (J-motive-context ⊢zero)) ⊢zero
                (var₀ (J-motive-context-type (zeroⱼ ⊢Δ))))
             ⊢zero)
          (rflⱼ′
             (J 𝟘 𝟘 ℕ zero ℕ zero zero rfl  ≡⟨ J-β-≡ (zeroⱼ ⊢Δ) ⊢ℕ (zeroⱼ ⊢Δ) ⟩⊢∎
              zero                          ∎))
          (var₀ ⊢0≡0)
      , refl
      where
      Δ′ : Con Term 1
      Δ′ = ε ∙ Id ℕ zero zero

      ⊢0≡0 : ε ⊢ Id ℕ zero zero
      ⊢0≡0 = Idⱼ (zeroⱼ ε) (zeroⱼ ε)

      ⊢Δ : ⊢ Δ′
      ⊢Δ = ε ∙ ⊢0≡0

      ⊢ℕ : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ ℕ
      ⊢ℕ = ℕⱼ (J-motive-context (zeroⱼ ⊢Δ))

      ⊢zero : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
      ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

  opaque

    soundness-ℕ-only-target-not-counterexample₄ :
      K-allowed →
      Run-time-canonicity-for
        (ε ∙ Id ℕ zero zero)
        (K 𝟘 ℕ zero ℕ zero (var {n = 1} x0))
    soundness-ℕ-only-target-not-counterexample₄ ok =
        _
      , K 𝟘 ℕ zero
          (Id ℕ (K 𝟘 ℕ zero ℕ zero (var x0)) zero)
          rfl (var x0)
      , Kⱼ′
          (Idⱼ
             (Kⱼ′ (ℕⱼ (K-motive-context ⊢zero)) ⊢zero
                (var₀ (K-motive-context-type (zeroⱼ ⊢Δ))) ok)
             ⊢zero)
          (rflⱼ′
             (K 𝟘 ℕ zero ℕ zero rfl  ≡⟨ K-β-≡ ⊢ℕ (zeroⱼ ⊢Δ) ok ⟩⊢∎
              zero                   ∎))
          (var₀ ⊢0≡0)
          ok
      , refl
      where
      Δ′ : Con Term 1
      Δ′ = ε ∙ Id ℕ zero zero

      ⊢0≡0 : ε ⊢ Id ℕ zero zero
      ⊢0≡0 = Idⱼ (zeroⱼ ε) (zeroⱼ ε)

      ⊢Δ : ⊢ Δ′
      ⊢Δ = ε ∙ ⊢0≡0

      ⊢ℕ : Δ′ ∙ Id ℕ zero zero ⊢ ℕ
      ⊢ℕ = ℕⱼ (K-motive-context (zeroⱼ ⊢Δ))

      ⊢zero : Δ′ ∙ Id ℕ zero zero ⊢ zero ∷ ℕ
      ⊢zero = zeroⱼ (K-motive-context (zeroⱼ ⊢Δ))
