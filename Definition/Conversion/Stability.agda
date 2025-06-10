------------------------------------------------------------------------
-- Stability of algorithmic equality (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Stability
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R
import Definition.Typed.Weakening R as W
open import Definition.Conversion R
open import Definition.Conversion.Level R
open import Definition.Conversion.Soundness R

open import Tools.Bool
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.List as L
import Data.List.Properties as L
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any

private
  variable
    n : Nat
    Γ Δ : Con Term n
    d : Bool

mutual
  -- Stability of algorithmic equality of neutrals.
  stability~↑ : ∀ {k l A}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑ A
              → Δ ⊢ k ~ l ↑ A
  stability~↑ Γ≡Δ (var-refl x x≡y) =
    var-refl (stabilityTerm Γ≡Δ x) x≡y
  stability~↑ Γ≡Δ (app-cong k~l x) =
    app-cong (stability~↓ Γ≡Δ k~l) (stabilityConv↑Term Γ≡Δ x)
  stability~↑ Γ≡Δ (fst-cong p~r) =
    fst-cong (stability~↓ Γ≡Δ p~r)
  stability~↑ Γ≡Δ (snd-cong p~r) =
    snd-cong (stability~↓ Γ≡Δ p~r)
  stability~↑ Γ≡Δ (natrec-cong x₁ x₂ x₃ k~l) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        ⊢F = proj₁ (syntacticEq (soundnessConv↑ x₁))
    in natrec-cong (stabilityConv↑ (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ))) x₁)
                   (stabilityConv↑Term Γ≡Δ x₂)
                   ((stabilityConv↑Term (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ) ∙ refl ⊢F) x₃))
                   (stability~↓ Γ≡Δ k~l)
  stability~↑ Γ≡Δ (prodrec-cong x x₁ x₂) =
    let ⊢Σ , _ = syntacticEqTerm (soundness~↓ x₁)
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢Σ
    in  prodrec-cong (stabilityConv↑ (Γ≡Δ ∙ refl ⊢Σ) x)
          (stability~↓ Γ≡Δ x₁)
          (stabilityConv↑Term (Γ≡Δ ∙ refl ⊢F ∙ refl ⊢G) x₂)
  stability~↑ Γ≡Δ (emptyrec-cong x₁ k~l) =
    emptyrec-cong (stabilityConv↑ Γ≡Δ x₁)
                  (stability~↓ Γ≡Δ k~l)
  stability~↑ Γ≡Δ (unitrec-cong l x x₁ x₂ no-η) =
    let k≡l = soundness~∷ x₁
        ⊢Unit = proj₁ (syntacticEqTerm k≡l)
    in  unitrec-cong (stabilityConv↑Term Γ≡Δ l) (stabilityConv↑ (Γ≡Δ ∙ refl ⊢Unit) x)
          (stability~∷ Γ≡Δ x₁) (stabilityConv↑Term Γ≡Δ x₂) no-η
  stability~↑ Γ≡Δ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case syntacticEq (soundnessConv↑ A₁≡A₂) .proj₁ of λ {
      ⊢A₁ →
    case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    J-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑
         (Γ≡Δ ∙ refl ⊢A₁ ∙ refl (Idⱼ′ (W.wkTerm₁ ⊢A₁ ⊢t₁) (var₀ ⊢A₁)))
         B₁≡B₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stabilityConv↑Term Γ≡Δ v₁≡v₂)
      (stability~↓ Γ≡Δ w₁~w₂) (stabilityEq Γ≡Δ ≡Id) }}
  stability~↑ Γ≡Δ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    K-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑ (Γ≡Δ ∙ refl (Idⱼ′ ⊢t₁ ⊢t₁)) B₁≡B₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stability~↓ Γ≡Δ v₁~v₂)
      (stabilityEq Γ≡Δ ≡Id) ok }
  stability~↑ Γ≡Δ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    []-cong-cong (stabilityConv↑ Γ≡Δ A₁≡A₂)
      (stabilityConv↑Term Γ≡Δ t₁≡t₂) (stabilityConv↑Term Γ≡Δ u₁≡u₂)
      (stability~↓ Γ≡Δ v₁~v₂) (stabilityEq Γ≡Δ ≡Id) ok

  -- Stability of algorithmic equality of neutrals of types in WHNF.
  stability~↓ : ∀ {k l A}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓ A
              → Δ ⊢ k ~ l ↓ A
  stability~↓ Γ≡Δ ([~] A (D , whnfA) k~l) =
    [~] A (stabilityRed* Γ≡Δ D , whnfA) (stability~↑ Γ≡Δ k~l)

  stability~∷ : ∀ {k l A}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ∷ A
              → Δ ⊢ k ~ l ∷ A
  stability~∷ Γ≡Δ (↑ A≡B k~l) =
    ↑ (stabilityEq Γ≡Δ A≡B) (stability~↑ Γ≡Δ k~l)

  -- Stability of algorithmic equality of types.
  stabilityConv↑ : ∀ {A B}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↑] B
                 → Δ ⊢ A [conv↑] B
  stabilityConv↑ Γ≡Δ ([↑] A′ B′ D D′ A′<>B′) =
    [↑] A′ B′ (stabilityRed↘ Γ≡Δ D) (stabilityRed↘ Γ≡Δ D′)
        (stabilityConv↓ Γ≡Δ A′<>B′)

  -- Stability of algorithmic equality of types in WHNF.
  stabilityConv↓ : ∀ {A B}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↓] B
                 → Δ ⊢ A [conv↓] B
  stabilityConv↓ Γ≡Δ (Level-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Level-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (U-cong x) =
    U-cong (stabilityConv↑Term Γ≡Δ x)
  stabilityConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Unit-cong x ok) =
    Unit-cong (stabilityConv↑Term Γ≡Δ x) ok
  stabilityConv↓ Γ≡Δ (ne x) =
    ne (stability~↓ Γ≡Δ x)
  stabilityConv↓ Γ≡Δ (ΠΣ-cong A<>B A<>B₁ ok) =
    ΠΣ-cong (stabilityConv↑ Γ≡Δ A<>B)
      (stabilityConv↑
         (Γ≡Δ ∙ refl (syntacticEq (soundnessConv↑ A<>B) .proj₁)) A<>B₁)
      ok
  stabilityConv↓ Γ≡Δ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂)

  -- Stability of algorithmic equality of terms.
  stabilityConv↑Term : ∀ {t u A}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↑] u ∷ A
                     → Δ ⊢ t [conv↑] u ∷ A
  stabilityConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ B t′ u′ (stabilityRed↘ Γ≡Δ D) (stabilityRed↘Term Γ≡Δ d)
                 (stabilityRed↘Term Γ≡Δ d′)
                 (stabilityConv↓Term Γ≡Δ t<>u)

  stabilityLevelAtom : ⊢ Γ ≡ Δ → LevelAtom Γ → LevelAtom Δ
  stabilityLevelAtom Γ≡Δ zeroᵘ = zeroᵘ
  stabilityLevelAtom Γ≡Δ (ne x) = ne (stability~↓ Γ≡Δ x)

  stabilityLevelPlus : ⊢ Γ ≡ Δ → LevelPlus Γ → LevelPlus Δ
  stabilityLevelPlus Γ≡Δ (n , l) = n , stabilityLevelAtom Γ≡Δ l

  stabilityLevelView : ⊢ Γ ≡ Δ → LevelView Γ → LevelView Δ
  stabilityLevelView Γ≡Δ L.[] = L.[]
  stabilityLevelView Γ≡Δ (x L.∷ xs) = stabilityLevelPlus Γ≡Δ x L.∷ stabilityLevelView Γ≡Δ xs

  stabilityLevelAtom→Term : (Γ≡Δ : ⊢ Γ ≡ Δ) (t : LevelAtom Γ) → LevelAtom→Term (stabilityLevelAtom Γ≡Δ t) PE.≡ LevelAtom→Term t
  stabilityLevelAtom→Term Γ≡Δ zeroᵘ = PE.refl
  stabilityLevelAtom→Term Γ≡Δ (ne x) = PE.refl

  stabilityLevelPlus→Term : (Γ≡Δ : ⊢ Γ ≡ Δ) (t : LevelPlus Γ) → LevelPlus→Term (stabilityLevelPlus Γ≡Δ t) PE.≡ LevelPlus→Term t
  stabilityLevelPlus→Term Γ≡Δ (n , a) = PE.cong (sucᵘᵏ n) (stabilityLevelAtom→Term Γ≡Δ a)

  stabilityLevelView→Term : ∀ {t} → (Γ≡Δ : ⊢ Γ ≡ Δ) → LevelView→Term (stabilityLevelView Γ≡Δ t) PE.≡ LevelView→Term t
  stabilityLevelView→Term {t = L.[]} Γ≡Δ = PE.refl
  stabilityLevelView→Term {t = x L.∷ t} Γ≡Δ = PE.cong₂ _maxᵘ_ (stabilityLevelPlus→Term Γ≡Δ x) (stabilityLevelView→Term Γ≡Δ)

  stability-≡ⁿ : (Γ≡Δ : ⊢ Γ ≡ Δ) → {t u : Term n} → ≡ⁿ Γ t u d → ≡ⁿ Δ t u d
  stability-≡ⁿ Γ≡Δ (ne≡ x) = ne≡ (stability~↓ Γ≡Δ x)
  stability-≡ⁿ Γ≡Δ (ne≡' x) = ne≡' (stability~↓ Γ≡Δ x)

  stability-≤⁺ : (Γ≡Δ : ⊢ Γ ≡ Δ) → (t u : LevelPlus Γ) → ≤⁺ d t u → ≤⁺ d (stabilityLevelPlus Γ≡Δ t) (stabilityLevelPlus Γ≡Δ u)
  stability-≤⁺ Γ≡Δ t u (x , zeroᵘ≤) = x , zeroᵘ≤
  stability-≤⁺ Γ≡Δ t u (x , ne≤ y) = x , ne≤ (stability-≡ⁿ Γ≡Δ y)

  stability-≤⁺ᵛ : (Γ≡Δ : ⊢ Γ ≡ Δ) → (t : LevelPlus Γ) → (u : LevelView Γ) → ≤⁺ᵛ d t u → ≤⁺ᵛ d (stabilityLevelPlus Γ≡Δ t) (stabilityLevelView Γ≡Δ u)
  stability-≤⁺ᵛ Γ≡Δ t u (Any.here px) = Any.here (stability-≤⁺ Γ≡Δ _ _ px)
  stability-≤⁺ᵛ Γ≡Δ t u (Any.there t≤u) = Any.there (stability-≤⁺ᵛ Γ≡Δ _ _ t≤u)

  stability-≤ᵛ : (Γ≡Δ : ⊢ Γ ≡ Δ) → (t u : LevelView Γ) → ≤ᵛ d t u → ≤ᵛ d (stabilityLevelView Γ≡Δ t) (stabilityLevelView Γ≡Δ u)
  stability-≤ᵛ Γ≡Δ t u All.[] = All.[]
  stability-≤ᵛ Γ≡Δ t u (px All.∷ t≤u) = stability-≤⁺ᵛ Γ≡Δ _ _ px All.∷ stability-≤ᵛ Γ≡Δ _ _ t≤u

  stability-≡ᵛ : (Γ≡Δ : ⊢ Γ ≡ Δ) → (t u : LevelView Γ) → t ≡ᵛ u → stabilityLevelView Γ≡Δ t ≡ᵛ stabilityLevelView Γ≡Δ u
  stability-≡ᵛ Γ≡Δ t u (t≤u , u≤t) = stability-≤ᵛ Γ≡Δ t u t≤u , stability-≤ᵛ Γ≡Δ u t u≤t

  stability-sucᵛ : (Γ≡Δ : ⊢ Γ ≡ Δ) → (v v′ : LevelView Γ) → v PE.≡ sucᵛ v′ → stabilityLevelView Γ≡Δ v PE.≡ sucᵛ (stabilityLevelView Γ≡Δ v′)
  stability-sucᵛ Γ≡Δ v v′ PE.refl = PE.cong (_ L.∷_) (stability-map-suc⁺ Γ≡Δ _ _ PE.refl)

  stability-map-suc⁺ : (Γ≡Δ : ⊢ Γ ≡ Δ) → (v v′ : LevelView Γ) → v PE.≡ map-suc⁺ v′ → stabilityLevelView Γ≡Δ v PE.≡ map-suc⁺ (stabilityLevelView Γ≡Δ v′)
  stability-map-suc⁺ Γ≡Δ L.[] L.[] PE.refl = PE.refl
  stability-map-suc⁺ Γ≡Δ L.[] (x L.∷ v′) ()
  stability-map-suc⁺ Γ≡Δ (x L.∷ v) L.[] ()
  stability-map-suc⁺ Γ≡Δ ((n , a) L.∷ v) ((n′ , a′) L.∷ v′) PE.refl = PE.cong (_ L.∷_) (stability-map-suc⁺ Γ≡Δ v v′ PE.refl)

  stabilityLevelPlus-cong : ∀ (Γ≡Δ : ⊢ Γ ≡ Δ) (a b : LevelPlus Γ) → a PE.≡ b → stabilityLevelPlus Γ≡Δ a PE.≡ stabilityLevelPlus Γ≡Δ b
  stabilityLevelPlus-cong Γ≡Δ a b PE.refl = PE.refl
  stabilityLevelView-cong : ∀ (Γ≡Δ : ⊢ Γ ≡ Δ) (a b : LevelView Γ) → a PE.≡ b → stabilityLevelView Γ≡Δ a PE.≡ stabilityLevelView Γ≡Δ b
  stabilityLevelView-cong Γ≡Δ a b PE.refl = PE.refl

  stability-maxᵛ : (Γ≡Δ : ⊢ Γ ≡ Δ) (v v′ v″ : LevelView Γ) → v PE.≡ maxᵛ v′ v″ → stabilityLevelView Γ≡Δ v PE.≡ maxᵛ (stabilityLevelView Γ≡Δ v′) (stabilityLevelView Γ≡Δ v″)
  stability-maxᵛ Γ≡Δ L.[] L.[] v″ PE.refl = PE.refl
  stability-maxᵛ Γ≡Δ L.[] (x L.∷ v′) v″ ()
  stability-maxᵛ Γ≡Δ (x L.∷ v) L.[] v″ PE.refl = PE.refl
  stability-maxᵛ Γ≡Δ (x L.∷ v) (x₁ L.∷ v′) v″ eq =
    let a , b = L.∷-injective eq
    in PE.cong₂ L._∷_ (stabilityLevelPlus-cong Γ≡Δ x x₁ a) (stability-maxᵛ Γ≡Δ _ _ v″ b)

  stability-↑ᵛ
    : ∀ {t} {v : LevelView Γ}
    → (Γ≡Δ : ⊢ Γ ≡ Δ)
    → Γ ⊢ t ↑ᵛ v
    → Δ ⊢ t ↑ᵛ stabilityLevelView Γ≡Δ v
  stability-↑ᵛ Γ≡Δ ([↑]ᵛ d t↓v) = [↑]ᵛ (stabilityRed↘Term Γ≡Δ d) (stability-↓ᵛ Γ≡Δ t↓v)

  stability-↓ᵛ
    : ∀ {t} {v : LevelView Γ}
    → (Γ≡Δ : ⊢ Γ ≡ Δ)
    → Γ ⊢ t ↓ᵛ v
    → Δ ⊢ t ↓ᵛ stabilityLevelView Γ≡Δ v
  stability-↓ᵛ Γ≡Δ (zeroᵘ-↓ᵛ x) = zeroᵘ-↓ᵛ (contextConvSubst Γ≡Δ .proj₂ .proj₁)
  stability-↓ᵛ {Γ} {Δ} Γ≡Δ (sucᵘ-↓ᵛ {v} {v′} y t≡v) =
    sucᵘ-↓ᵛ (stability-sucᵛ Γ≡Δ _ _ y) (stability-↑ᵛ Γ≡Δ t≡v)
  stability-↓ᵛ Γ≡Δ (maxᵘ-↓ᵛ {v′} {v″} w y t≡v t≡v₁) =
    maxᵘ-↓ᵛ w (stability-maxᵛ Γ≡Δ _ v′ v″ y) (stability-↑ᵛ Γ≡Δ t≡v) (stability-↑ᵛ Γ≡Δ t≡v₁)
  stability-↓ᵛ Γ≡Δ (ne-↓ᵛ [t′] x₁) =
    ne-↓ᵛ (stability~↓ Γ≡Δ [t′]) (stabilityLevelView-cong Γ≡Δ _ _ x₁)

  stabilityConv↓Level : ∀ {t u}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↓] u ∷Level
                     → Δ ⊢ t [conv↓] u ∷Level
  stabilityConv↓Level Γ≡Δ ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u) =
    [↓]ˡ (stabilityLevelView Γ≡Δ tᵛ) (stabilityLevelView Γ≡Δ uᵛ)
      (stability-↓ᵛ Γ≡Δ t≡)
      (stability-↓ᵛ Γ≡Δ u≡)
      (stability-≡ᵛ Γ≡Δ tᵛ uᵛ t≡u)

  -- Stability of algorithmic equality of terms in WHNF.
  stabilityConv↓Term : ∀ {t u A}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↓] u ∷ A
                     → Δ ⊢ t [conv↓] u ∷ A
  stabilityConv↓Term Γ≡Δ (Level-ins x) =
    Level-ins (stabilityConv↓Level Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (ℕ-ins x) =
    ℕ-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Empty-ins x) =
    Empty-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Unitʷ-ins ok t~u) =
    Unitʷ-ins ok (stability~∷ Γ≡Δ t~u)
  stabilityConv↓Term Γ≡Δ (Σʷ-ins x x₁ x₂) =
    Σʷ-ins (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stability~↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (ne-ins t u neN x) =
    ne-ins (stabilityTerm Γ≡Δ t) (stabilityTerm Γ≡Δ u) neN (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (U-ins x) = U-ins (stability~∷ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Level-refl x) =
    Level-refl (stabilityEqTerm Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (U-cong x y) = U-cong (stabilityConv↑Term Γ≡Δ x) (stabilityEqTerm Γ≡Δ y)
  stabilityConv↓Term Γ≡Δ (ℕ-refl x) =
    ℕ-refl (stabilityEqTerm Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Empty-refl x) =
    Empty-refl (stabilityEqTerm Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Unit-cong x ok y) = Unit-cong (stabilityConv↑Term Γ≡Δ x) ok (stabilityEqTerm Γ≡Δ y)
  stabilityConv↓Term Γ≡Δ (ΠΣ-cong ⊢l₁ ⊢l₂ x x₁ x₂ y) =
    ΠΣ-cong (stabilityTerm Γ≡Δ ⊢l₁) (stabilityTerm Γ≡Δ ⊢l₂)
      (stabilityConv↑Term Γ≡Δ x)
      (stabilityConv↑Term (Γ≡Δ ∙ refl (syntacticEq (univ (soundnessConv↑Term x)) .proj₁)) x₁)
      x₂
      (stabilityEqTerm Γ≡Δ y)
  stabilityConv↓Term Γ≡Δ (Id-cong x x₁ x₂) = Id-cong (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityConv↑Term Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (starʷ-cong x y ok no-η) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  starʷ-cong (stabilityEqTerm Γ≡Δ x) (stabilityEqTerm Γ≡Δ y) ok no-η
  stabilityConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (stabilityConv↑Term Γ≡Δ t<>u)
  stabilityConv↓Term Γ≡Δ (prod-cong x₁ x₂ x₃ ok) =
    prod-cong (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf x₁))) x₁)
      (stabilityConv↑Term Γ≡Δ x₂) (stabilityConv↑Term Γ≡Δ x₃) ok
  stabilityConv↓Term Γ≡Δ (η-eq x x₁ y y₁ t<>u) =
    let ⊢F , ⊢G , _ = inversion-ΠΣ (syntacticTerm x)
    in  η-eq (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
             y y₁ (stabilityConv↑Term (Γ≡Δ ∙ (refl ⊢F)) t<>u)
  stabilityConv↓Term Γ≡Δ (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (stabilityTerm Γ≡Δ ⊢p) (stabilityTerm Γ≡Δ ⊢r)
        pProd rProd
        (stabilityConv↑Term Γ≡Δ fstConv) (stabilityConv↑Term Γ≡Δ sndConv)
  stabilityConv↓Term Γ≡Δ (η-unit l [t] [u] tUnit uUnit ok₁ ok₂) =
    let [t] = stabilityTerm Γ≡Δ [t]
        [u] = stabilityTerm Γ≡Δ [u]
    in  η-unit (stabilityTerm Γ≡Δ l) [t] [u] tUnit uUnit ok₁ ok₂
  stabilityConv↓Term Γ≡Δ (Id-ins ⊢v₁ v₁~v₂) =
    Id-ins (stabilityTerm Γ≡Δ ⊢v₁) (stability~↓ Γ≡Δ v₁~v₂)
  stabilityConv↓Term Γ≡Δ (rfl-refl t≡u) =
    rfl-refl (stabilityEqTerm Γ≡Δ t≡u)
