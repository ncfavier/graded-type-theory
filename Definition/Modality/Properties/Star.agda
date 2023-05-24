open import Definition.Modality

module Definition.Modality.Properties.Star
  {a} {M : Set a} (𝕄 : Semiring-with-meet-and-star M) where

open Semiring-with-meet-and-star 𝕄

open import Definition.Modality.Properties.PartialOrder semiring-with-meet
open import Definition.Modality.Properties.Meet semiring-with-meet

open import Tools.Algebra M
open import Tools.PropositionalEquality

private
  variable
    p p′ q q′ r r′ : M

-- Variants of ⊛-congurence

⊛-cong : p ≈ p′ → q ≈ q′ → r ≈ r′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r′
⊛-cong = cong₃ _⊛_▷_

⊛ᵣ-cong : p ≈ p′ → q ≈ q′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r
⊛ᵣ-cong p≈p′ q≈q′ = ⊛-cong p≈p′ q≈q′ ≈-refl

⊛ᵣ-congˡ : q ≈ q′ → p ⊛ q ▷ r ≈ p ⊛ q′ ▷ r
⊛ᵣ-congˡ q≈q′ = ⊛ᵣ-cong ≈-refl q≈q′

⊛ᵣ-congʳ : p ≈ p′ → p ⊛ q ▷ r ≈ p′ ⊛ q ▷ r
⊛ᵣ-congʳ p≈p′ = ⊛ᵣ-cong p≈p′ ≈-refl

-- ⊛ is monotone on the first two arguments
-- If p ≤ p′ and q ≤ q′ then p ⊛ q ▷ r ≤ p′ ⊛ q′ ≤ r

⊛-monotone : p ≤ p′ → q ≤ q′ → p ⊛ q ▷ r ≤ p′ ⊛ q′ ▷ r
⊛-monotone {p} {p′} {q} {q′} {r} p≤p′ q≤q′ = begin
  p ⊛ q ▷ r
    ≈⟨ ⊛ᵣ-cong p≤p′ q≤q′ ⟩
  (p ∧ p′) ⊛ (q ∧ q′) ▷ r
    ≤⟨ ⊛-sub-distribˡ-∧ r (p ∧ p′) q q′ ⟩
  ((p ∧ p′) ⊛ q ▷ r) ∧ ((p ∧ p′) ⊛ q′ ▷ r)
    ≤⟨ ∧-monotone (⊛-sub-distribʳ-∧ r q p p′) (⊛-sub-distribʳ-∧ r q′ p p′) ⟩
  ((p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r)) ∧ (p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r)
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p′ ⊛ q′ ▷ r ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset

-- ⊛ is idempotent on 𝟘 w.r.t the first two arguments
-- 𝟘 ⊛ 𝟘 ▷ r ≈ 𝟘
⊛-idem-𝟘 : (r : M) → (_⊛_▷ r) IdempotentOn 𝟘
⊛-idem-𝟘 r = ≤-antisym (⊛-ineq₂ 𝟘 𝟘 r) 𝟘≤𝟘⊛𝟘
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
  𝟘≤𝟘⊛𝟘 = begin
    𝟘                     ≈˘⟨ ·-zeroʳ (𝟘 ⊛ 𝟘 ▷ r) ⟩
    (𝟘 ⊛ 𝟘 ▷ r) · 𝟘       ≤⟨ ·-sub-distribʳ-⊛ r 𝟘 𝟘 𝟘 ⟩
    (𝟘 · 𝟘) ⊛ (𝟘 · 𝟘) ▷ r ≈⟨ ⊛ᵣ-cong (·-zeroˡ 𝟘) (·-zeroˡ 𝟘) ⟩
    𝟘 ⊛ 𝟘 ▷ r ∎
