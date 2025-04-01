------------------------------------------------------------------------
-- Irrelevance lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality


module Definition.LogicalRelation.Irrelevance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (Wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Properties.Kit R {{eqrel}}
open import Definition.LogicalRelation.Properties.Primitive R {{eqrel}}
open import Definition.LogicalRelation.Properties.Reflexivity R {{eqrel}}
open import Definition.LogicalRelation.Properties.Whnf R {{eqrel}}
open import Definition.LogicalRelation.ShapeView R {{eqrel}}

open import Tools.Function
open import Tools.Level hiding (_⊔_)
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Γ′ : Con Term n
    A A′ B B′ C C′ t : Term _
    l l′ : Universe-level

-- Irrelevance for level reflection.

opaque
  unfolding ↑ᵘ′_

  mutual
    ↑ᵘ′-cong-ne
      : ∀ {t t′ u u′} (t≡t′ : Γ ⊩neLvl t ≡ t′ ∷Level) (u≡u′ : Γ ⊩neLvl u ≡ u′ ∷Level)
      → Γ ⊩neLvl t ≡ u ∷Level → ↑ᵘ′-ne t≡t′ PE.≡ ↑ᵘ′-ne u≡u′
    ↑ᵘ′-cong-ne (neLvlₜ₌ a b p) (neLvlₜ₌ c d q) (neLvlₜ₌ e f r) = ↑ᵘ′-neprop-cong p q r

    ↑ᵘ′-cong
      : ∀ {t t′ u u′} (t≡t′ : Γ ⊩Level t ≡ t′ ∷Level) (u≡u′ : Γ ⊩Level u ≡ u′ ∷Level)
      → Γ ⊩Level t ≡ u ∷Level → ↑ᵘ′ t≡t′ PE.≡ ↑ᵘ′ u≡u′
    ↑ᵘ′-cong (Levelₜ₌ _ _ t⇒ t′⇒ [t]) (Levelₜ₌ _ _ u⇒ u′⇒ [u]) (Levelₜ₌ _ _ t⇒′ u⇒′ t≡u) =
      case whrDet*Term (t⇒ , lsplit [t] .proj₁) (t⇒′ , lsplit t≡u .proj₁) of λ {
        PE.refl →
      case whrDet*Term (u⇒ , lsplit [u] .proj₁) (u⇒′ , lsplit t≡u .proj₂) of λ {
        PE.refl →
      ↑ᵘ′-prop-cong [t] [u] t≡u }}

    ↑ᵘ′-neprop-cong
      : ∀ {t t′ u u′} (t≡t′ : [neLevel]-prop Γ t t′) (u≡u′ : [neLevel]-prop Γ u u′)
      → [neLevel]-prop Γ t u → ↑ᵘ′-neprop t≡t′ PE.≡ ↑ᵘ′-neprop u≡u′
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x₂ x₃) (maxᵘˡᵣ x₄ x₅) (maxᵘˡᵣ x x₁) = PE.cong₂ _⊔_ (↑ᵘ′-cong-ne x₂ x₄ x) (↑ᵘ′-cong x₃ x₅ x₁)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x₂ x₃) (maxᵘʳᵣ x₄ x₅) (maxᵘʳᵣ x x₁) = PE.cong₂ (λ x y → 1+ x ⊔ y) (↑ᵘ′-cong x₂ x₄ x) (↑ᵘ′-cong-ne x₃ x₅ x₁)
    ↑ᵘ′-neprop-cong (ne x₁) (ne x₂) (ne x) = PE.refl
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x₂ x₃) (maxᵘʳᵣ x₄ x₅) (maxᵘˡᵣ (neLvlₜ₌ _ (ne ()) _) x₁)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x₂ x₃) (ne (neNfₜ₌ _ () _ _)) (maxᵘˡᵣ x x₁)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x₂ x₃) _ (maxᵘˡᵣ (neLvlₜ₌ (ne ()) _ _) x₁)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () _ _)) _ (maxᵘˡᵣ x x₁)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (neLvlₜ₌ (ne ()) _ _) x₃) _ (maxᵘʳᵣ x x₁)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x₂ x₃) (maxᵘˡᵣ (neLvlₜ₌ (ne ()) _ _) x₅) (maxᵘʳᵣ x x₁)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x₂ x₃) (ne (neNfₜ₌ _ () _ _)) (maxᵘʳᵣ x x₁)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () _ _)) b (maxᵘʳᵣ x x₁)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x₁ x₂) b (ne (neNfₜ₌ _ () _ _))
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x₁ x₂) b (ne (neNfₜ₌ _ () _ _))
    ↑ᵘ′-neprop-cong (ne x₁) (maxᵘˡᵣ x₂ x₃) (ne (neNfₜ₌ _ _ () _))
    ↑ᵘ′-neprop-cong (ne x₁) (maxᵘʳᵣ x₂ x₃) (ne (neNfₜ₌ _ _ () _))

    ↑ᵘ′-prop-cong
      : ∀ {t t′ u u′} (t≡t′ : [Level]-prop Γ t t′) (u≡u′ : [Level]-prop Γ u u′)
      → [Level]-prop Γ t u → ↑ᵘ′-prop t≡t′ PE.≡ ↑ᵘ′-prop u≡u′
    ↑ᵘ′-prop-cong zeroᵘᵣ zeroᵘᵣ zeroᵘᵣ = PE.refl
    ↑ᵘ′-prop-cong (sucᵘᵣ a) (sucᵘᵣ b) (sucᵘᵣ x) = PE.cong 1+ (↑ᵘ′-cong a b x)
    ↑ᵘ′-prop-cong (ne a) (ne b) (ne x) = ↑ᵘ′-cong-ne a b x
    ↑ᵘ′-prop-cong zeroᵘᵣ (ne (neLvlₜ₌ (ne ()) _ _)) zeroᵘᵣ
    ↑ᵘ′-prop-cong (ne (neLvlₜ₌ (ne ()) _ _)) _ zeroᵘᵣ
    ↑ᵘ′-prop-cong (sucᵘᵣ _) (ne (neLvlₜ₌ (ne ()) _ _)) (sucᵘᵣ _)
    ↑ᵘ′-prop-cong (ne (neLvlₜ₌ (ne ()) _ _)) _ (sucᵘᵣ _)
    ↑ᵘ′-prop-cong zeroᵘᵣ _ (ne (neLvlₜ₌ (ne ()) _ _))
    ↑ᵘ′-prop-cong (sucᵘᵣ _) _ (ne (neLvlₜ₌ (ne ()) _ _))
    ↑ᵘ′-prop-cong (ne _) zeroᵘᵣ (ne (neLvlₜ₌ _ (ne ()) _))
    ↑ᵘ′-prop-cong (ne _) (sucᵘᵣ _) (ne (neLvlₜ₌ _ (ne ()) _))

  ↑ᵘ-cong
    : ∀ {t t′ u u′} (t≡t′ : Γ ⊩Level t ≡ t′ ∷Level) (u≡u′ : Γ ⊩Level u ≡ u′ ∷Level)
    → Γ ⊩Level t ≡ u ∷Level → ↑ᵘ t≡t′ PE.≡ ↑ᵘ u≡u′
  ↑ᵘ-cong t≡t′ u≡u′ t≡u = PE.cong 0ᵘ+_ (↑ᵘ′-cong t≡t′ u≡u′ t≡u)

  ↑ᵘ-prop-cong
    : ∀ {t t′ u u′} (t≡t′ : [Level]-prop Γ t t′) (u≡u′ : [Level]-prop Γ u u′)
    → [Level]-prop Γ t u → ↑ᵘ-prop t≡t′ PE.≡ ↑ᵘ-prop u≡u′
  ↑ᵘ-prop-cong t≡t′ u≡u′ t≡u = PE.cong 0ᵘ+_ (↑ᵘ′-prop-cong t≡t′ u≡u′ t≡u)

↑ᵘ′-irrelevance
  : ∀ {t u u′} (t≡u : Γ ⊩Level t ≡ u ∷Level) (t≡u′ : Γ ⊩Level t ≡ u′ ∷Level)
  → ↑ᵘ′ t≡u PE.≡ ↑ᵘ′ t≡u′
↑ᵘ′-irrelevance t≡u t≡u′ = ↑ᵘ′-cong t≡u t≡u′ (wf-⊩Level t≡u .proj₁)

↑ᵘ-irrelevance
  : ∀ {t u u′} (t≡u : Γ ⊩Level t ≡ u ∷Level) (t≡u′ : Γ ⊩Level t ≡ u′ ∷Level)
  → ↑ᵘ t≡u PE.≡ ↑ᵘ t≡u′
↑ᵘ-irrelevance t≡u t≡u′ = PE.cong 0ᵘ+_ (↑ᵘ′-irrelevance t≡u t≡u′)

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A
             → Γ ⊩⟨ l ⟩ A′
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  ⊩⟨ l ⟩ A
              → Γ′ ⊩⟨ l ⟩ A′
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {A B l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {A A′ B l l′} (eq : A PE.≡ A′)
                   (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                 → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B / q
  irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {A A′ B B′ l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {A B B′ l} (eqB : B PE.≡ B′) (p : Γ ⊩⟨ l ⟩ A)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l ⟩ A ≡ B′ / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types
  -- and contexts.
  irrelevanceEq‴ :
    A PE.≡ A′ → B PE.≡ B′ → Γ PE.≡ Γ′ →
    (⊩A : Γ ⊩⟨ l ⟩ A) (⊩A′ : Γ′ ⊩⟨ l′ ⟩ A′) →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A → Γ′ ⊩⟨ l′ ⟩ A′ ≡ B′ / ⊩A′
  irrelevanceEq‴ PE.refl PE.refl PE.refl = irrelevanceEq

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                       → ShapeView Γ l l′ A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEqT (Levelᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Unitᵥ (Unitᵣ _ _ _ A⇒*Unit₁ _) (Unitᵣ _ _ _ A⇒*Unit₂ _)) (Unit₌ k′ D k≡k′) =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    Unit₌ k′ D k≡k′ }
  irrelevanceEqT
    (ne (ne _ _ D neK _) (ne _ K₁ D₁ neK₁ K≡K₁)) (ne₌ inc M D′ neM K≡M)
    rewrite whrDet* (D , ne (ne neK)) (D₁ , ne (ne neK₁)) =
    ne₌ inc M D′ neM K≡M
  irrelevanceEqT
    {Γ = Γ}
    (Bᵥ W (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁       = whrDet* (D , ⟦ W ⟧ₙ) (D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity W W ΠFG≡ΠF₁G₁
    in  B₌ F′ G′ D′
           (PE.subst (λ x → Γ ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ {_} {ρ} [ρ] → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁)
                              ([F] [ρ]) ([F]₁ [ρ]) ([F≡F′] [ρ]))
           (λ {_} {ρ} [ρ] [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ]) ([F] [ρ]) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                    ([G] [ρ] [a]) ([G]₁ [ρ] [a]₁) ([G≡G′] [ρ] [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _ D1) (Uᵣ _ _ _ D2)) A≡B
    = case whrDet* (D1 , Uₙ) (D2 , Uₙ) of λ { PE.refl →
        U₌ k′ ⇒*U′ k≡k′ }
    where
    open _⊩₁U≡_/_ A≡B
  irrelevanceEqT (Idᵥ ⊩A@record{} ⊩A′) A≡B =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
    record
      { ⇒*Id′    = ⇒*Id′
      ; Ty≡Ty′   = irrelevanceEq (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) Ty≡Ty′
      ; lhs≡lhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) lhs≡lhs′
      ; rhs≡rhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) rhs≡rhs′
      ; lhs≡rhs→lhs′≡rhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs≡rhs→lhs′≡rhs′ ∘→
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A′) (_⊩ₗId_.⊩Ty ⊩A)
      ; lhs′≡rhs′→lhs≡rhs =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs′≡rhs′→lhs≡rhs ∘→
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A′) (_⊩ₗId_.⊩Ty ⊩A)
      } }
    where
    open _⊩ₗId_≡_/_ A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                  → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceEqTerm p q t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {A A′ t l l′} (eq : A PE.≡ A′)
                     (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                   → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A′ / q
  irrelevanceTerm′ PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {A A′ t t′ l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                    → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ∷ A′ / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A)
                       ([A′] : Γ′ ⊩⟨ l′ ⟩ A′)
                     → Γ  ⊩⟨ l  ⟩ t ∷ A  / [A]
                     → Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {A t u l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                    → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {A A′ t u l l′} (eq : A PE.≡ A′)
                       (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                     → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ / q
  irrelevanceEqTerm′ PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {A A′ t t′ u u′ l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {A t u} {l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                           → ShapeView Γ l l′ A A p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (Levelᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Unitᵥ (Unitᵣ _ _ _ A⇒*Unit₁ _) (Unitᵣ _ _ _ A⇒*Unit₂ _)) t≡u =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    t≡u }
  irrelevanceEqTermT
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    with whrDet* (D₁ , ne (ne neK₁)) (D , ne (ne neK))
  … | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΠ! x@(Bᵣ F G D A≡A [F] [G] G-ext _)
       x₁@(Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
    case B-PE-injectivity BΠ! BΠ!
           (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)) of λ where
      (PE.refl , PE.refl , _) →
        Πₜ₌ f g d d′ funcF funcG f≡g
        λ [ρ] ⊩v ⊩w v≡w →
          let ⊩v′ = irrelevanceTerm ([F]₁ [ρ]) ([F] [ρ]) ⊩v in
          irrelevanceEqTerm ([G] [ρ] ⊩v′) ([G]₁ [ρ] ⊩v) $
          [f≡g] [ρ] ⊩v′ (irrelevanceTerm ([F]₁ [ρ]) ([F] [ρ]) ⊩w)
            (irrelevanceEqTerm ([F]₁ [ρ]) ([F] [ρ]) v≡w)
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣˢ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′
                    (PE.cong (λ x → wk (lift id) x [ fst _ p ]₀) G≡G₁)
                    ([G] _ [fstp]) ([G]₁ _ [fstp]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            ([fstp]′ , [fstr]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
       (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁] , [r₁] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [p₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _) ([F]₁ _) [p₁]
        [r₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _) ([F]₁ _) [r₁]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]₀) G≡G₁)
                    ([G] _ [p₁]) ([G]₁ _ [p₁]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) prodₙ prodₙ
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (PE.refl , PE.refl , PE.refl , PE.refl ,
             [p₁]′ , [r₁]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r (inc , p~r)) =
    let ΣFG≡ΣF₁G₁ = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        p~r′ = PE.subst (λ x → Γ ⊢ p ~ r ∷ x) ΣFG≡ΣF₁G₁ p~r
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) (ne x) (ne y)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (inc , p~r′)
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ prodₙ (ne _) _ (lift ()))
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ (ne _) prodₙ _ (lift ()))
  irrelevanceEqTermT (Uᵥ (Uᵣ k [k] k< ⇒*U1) (Uᵣ k′ [k′] k′< ⇒*U2))
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
    with whrDet* (⇒*U1 , Uₙ) (⇒*U2 ,  Uₙ)
  ... | PE.refl = Uₜ₌ A B d d′ typeA typeB A≡B _
    (irrelevance-⊩< (↑ᵘ-irrelevance [k] [k′]) k< k′< [u])
    (irrelevance-⊩<≡ (↑ᵘ-irrelevance [k] [k′]) k< k′< [t≡u])
  irrelevanceEqTermT
    (Idᵥ ⊩A@record{} ⊩A′) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
      _ , _ , t⇒*t′ , u⇒*u′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
         (ne inc t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , inc , t′~u′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , irrelevanceEqTerm
               (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) lhs≡rhs) }
