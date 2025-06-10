------------------------------------------------------------------------
-- Equal terms of type U are equal types (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Equality R
open import Definition.Conversion R
open import Definition.Conversion.Reduction R
open import Definition.Conversion.Lift R
open import Definition.Conversion.Inversion R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    Γ   : Con Term n
    A B l : Term _

-- The relation _⊢_[conv↓]_∷ U l is contained in _⊢_[conv↓]_.

mutual

  univConv↓ :
    ⦃ no-equality-reflection : No-equality-reflection ⦄ →
    Γ ⊢ A [conv↓] B ∷ U l →
    Γ ⊢ A [conv↓] B
  univConv↓ (ne-ins x x₁ () x₃)
  univConv↓ (U-ins (↑ A≡B k~↑l)) =
    case whNorm ⦃ possibly-nonempty ⦄ (syntacticEq A≡B .proj₂) of λ
      (B′ , whnfB′ , B⇒B′) →
    case U≡A ⦃ possibly-nonempty ⦄ (trans A≡B (subset* B⇒B′)) whnfB′ of λ {
      (_ , PE.refl) →
    ne ([~] _ (B⇒B′ , Uₙ) k~↑l) }
  univConv↓ (Level-refl x) = Level-refl (wfEqTerm x)
  univConv↓ (U-cong x x₁) = U-cong x
  univConv↓ (ℕ-refl x) = ℕ-refl (wfEqTerm x)
  univConv↓ (Empty-refl x) = Empty-refl (wfEqTerm x)
  univConv↓ (Unit-cong x x₁ x₂) = Unit-cong x x₁
  univConv↓ (ΠΣ-cong x x₁ x₂ x₃ x₄ x₅) = ΠΣ-cong (univConv↑ x₂) (univConv↑ x₃) x₄
  univConv↓ (Id-cong x x₁ x₂) = Id-cong (univConv↑ x) x₁ x₂

  -- The relation _⊢_[conv↑]_∷ U l is contained in _⊢_[conv↑]_ (if
  -- equality reflection is not allowed).

  univConv↑ :
    ⦃ no-equality-reflection : No-equality-reflection ⦄ →
    Γ ⊢ A [conv↑] B ∷ U l →
    Γ ⊢ A [conv↑] B
  univConv↑ ([↑]ₜ _ _ _ (D , _) (d , _) (d′ , _) t<>u)
        rewrite PE.sym (whnfRed* D Uₙ) =
    reductionConv↑ (univ* d) (univ* d′) (liftConv (univConv↓ t<>u))
