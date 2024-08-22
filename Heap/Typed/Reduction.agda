------------------------------------------------------------------------
-- Type preservation/subject reduction for the heap semantics
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Heap.Options

module Heap.Typed.Reduction
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Type-restrictions TR
open Options opts

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR as T
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Weakening TR using (id; step; _∷_⊇_)
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inequality TR
open import Definition.Typed.Consequences.Injectivity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
import Graded.Derived.Erased.Typed TR as ET

open import Heap.Reduction type-variant UR opts
open import Heap.Reduction.Properties type-variant UR opts
open import Heap.Typed UR TR ℕ-fullred
open import Heap.Typed.Inversion UR TR ℕ-fullred
open import Heap.Typed.Properties UR TR ℕ-fullred
open import Heap.Typed.Substitution UR TR ℕ-fullred
open import Heap.Typed.Weakening UR TR ℕ-fullred
open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum hiding (id; sym)

private variable
  n : Nat
  Γ Δ : Con Term _
  H H′ : Heap _ _
  e : Elim _
  t t′ u A B C : Term _
  y : Ptr _
  c : Closure _ _
  S S′ : Stack _
  s s′ : State _ _ _
  E E′ : Env _ _
  p q q′ r : M

------------------------------------------------------------------------
-- Typing is preserved by heap lookups

opaque

  -- Eliminator typing is preserved by heap lookups/updates

  heapUpdate-⊢ᵉ : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B → H ⊢ y ↦[ q ] c ⨾ H′ → Δ ⨾ H′ ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
  heapUpdate-⊢ᵉ {H} {H′} (∘ₑ {E} {u} {A} {B} {p} {q} ⊢u ⊢B) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk E u [ x ] ∷ _) H≡H′ ⊢u of λ
      ⊢u′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ ∘ₑ p u E ⟨ _ ⟩∷ _ ↝ B [ wk E u [ x ] ]₀)
      (PE.sym H≡H′) (∘ₑ {A = A} {B = B} ⊢u′ ⊢B)
  heapUpdate-⊢ᵉ (fstₑ ⊢A ⊢B) d =
    fstₑ ⊢A ⊢B
  heapUpdate-⊢ᵉ {t} {H′} (sndₑ {B} ⊢A ⊢B) d =
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ t ⟩∷ _ ↝ B [ fst _ t [ x ] ]₀)
      (PE.sym (heapUpdateSubst d))
      (sndₑ ⊢A ⊢B)
  heapUpdate-⊢ᵉ {Δ} {H} {t} {H′} (prodrecₑ {E} {u} {A} ⊢u ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → Δ ∙ _ ∙ _ ⊢
                          wk (liftn E 2) u [ liftSubstn x 2 ] ∷
                          wk (lift E) A [ liftSubst x ] [ _ ]↑²)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst (λ x → Δ ∙ _ ⊢ wk (lift E) A [ liftSubst x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → Δ ⨾ H′ ⊢ᵉ _ ⟨ _ ⟩∷ _ ↝ wk (lift E) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (prodrecₑ ⊢u′ ⊢A′)
  heapUpdate-⊢ᵉ {H} {t} {H′} (natrecₑ {E} {z} {A} {s} ⊢z ⊢s ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk E z [ x ] ∷ wk (lift E) A [ liftSubst x ] [ zero ]₀)
           H≡H′ ⊢z of λ
      ⊢z′ →
    case PE.subst (λ x → _ ∙ ℕ ∙ wk (lift E) A [ liftSubst x ] ⊢
                         wk (liftn E 2) s [ liftSubstn x 2 ] ∷
                         wk (lift E) A [ liftSubst x ] [ suc (var x1) ]↑²)
           H≡H′ ⊢s of λ
      ⊢s′ →
    case PE.subst (λ x → _ ∙ ℕ ⊢ wk (lift E) A [ liftSubst x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ _ ⟩∷ ℕ ↝ wk (lift E) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (natrecₑ ⊢z′ ⊢s′ ⊢A′)
  heapUpdate-⊢ᵉ {H} {t} {H′} (unitrecₑ {E} {u} {A} ⊢u ⊢A no-η) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk E u [ x ] ∷ (wk (lift E)) A [ liftSubst x ] [ starʷ ]₀)
            H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst (λ x → _ ∙ Unitʷ ⊢ wk (lift E) A [ liftSubst x ])
           H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ _ ⟩∷ Unitʷ ↝ wk (lift E) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (unitrecₑ ⊢u′ ⊢A′ no-η)
  heapUpdate-⊢ᵉ {H} {t} {H′} (emptyrecₑ {E} {A} ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk E A [ x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ t ⟩∷ Empty ↝ (wk E A [ x ]))
      (PE.sym H≡H′) (emptyrecₑ ⊢A′)
  heapUpdate-⊢ᵉ {t = w} {H′} (Jₑ {E} {A} {B} {t} {u} {v} {p} {q} ⊢u ⊢B) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst
           (λ x → _ ⊢ wk E u [ x ] ∷ wk (liftn E 2) B [ liftSubstn x 2 ] [ wk E t [ x ] , rfl ]₁₀)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst
           (λ x → _ ∙ wk E A [ x ] ∙ Id (wk1 (wk E A [ x ])) (wk1 (wk E t [ x ])) (var x0) ⊢ wk (liftn E 2) B [ liftSubstn x 2 ])
           H≡H′ ⊢B  of λ
      ⊢B′ →
    PE.subst
      (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ w ⟩∷ wk E (Id A t v) [ x ] ↝ ((wk (liftn E 2) B [ liftSubstn x 2 ]) [ wk E v [ x ] , w [ x ] ]₁₀))
      (PE.sym H≡H′) (Jₑ ⊢u′ ⊢B′)
  heapUpdate-⊢ᵉ {t = v} {H′} (Kₑ {E} {u} {B} {A} {t} {p} ⊢u ⊢B ok) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst
           (λ x → _ ⊢ wk E u [ x ] ∷ wk (lift E) B [ liftSubst x ] [ rfl ]₀)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst
           (λ x → _ ∙ wk E (Id A t t) [ x ] ⊢ wk (lift E) B [ liftSubst x ])
           H≡H′ ⊢B of λ
      ⊢B′ →
    PE.subst
      (λ x → _ ⨾ H′ ⊢ᵉ Kₑ p A t B u E ⟨ v ⟩∷ wk E (Id A t t) [ x ] ↝ wk (lift E) B [ liftSubst x ] [ v [ x ] ]₀)
      (PE.sym H≡H′) (Kₑ ⊢u′ ⊢B′ ok)
  heapUpdate-⊢ᵉ {t = v} {H′} ([]-congₑ {s′ = s} {A} {t} {u} {E} ok) d =
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ []-congₑ s A t u E ⟨ v ⟩∷ wk E (Id A t u) [ x ] ↝ wk E (Id (E.Erased A) E.[ t ] E.[ u ]) [ x ])
      (PE.sym (heapUpdateSubst d)) ([]-congₑ ok)
    where
    import Graded.Derived.Erased.Untyped 𝕄 s as E
  heapUpdate-⊢ᵉ sucₑ d = sucₑ
  heapUpdate-⊢ᵉ (conv ⊢e x) d =
    conv (heapUpdate-⊢ᵉ ⊢e d) x

opaque

  -- Stack typing is preserved by heap lookups/updates

  heapUpdate-⊢ˢ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B → H ⊢ y ↦[ q ] c ⨾ H′ → Δ ⨾ H′ ⊢ S ⟨ t ⟩∷ A ↝ B
  heapUpdate-⊢ˢ ε d = ε
  heapUpdate-⊢ˢ {H} {S = e ∙ S} {t} (⊢e ∙ ⊢S) d =
      heapUpdate-⊢ᵉ ⊢e d ∙ heapUpdate-⊢ˢ ⊢S d

opaque

  -- Heap typing is preserved by heap lookups/updates

  heapUpdate-⊢ʰ : Δ ⊢ʰ H ∷ Γ → H ⊢ y ↦[ q ] c ⨾ H′ → Δ ⊢ʰ H′ ∷ Γ
  heapUpdate-⊢ʰ (⊢H ∙ ⊢t) (here _) = ⊢H ∙ ⊢t
  heapUpdate-⊢ʰ {c = u , _} (_∙_ {E = E} {t} {A = A} ⊢H ⊢t) (there d) =
    case heapUpdate-⊢ʰ ⊢H d of λ
      ⊢H′ →
    case heapUpdateSubst d of λ
      H≡H′ →
    ⊢H′ ∙ PE.subst₂ (_ ⊢_∷_) (PE.cong (wk E t [_]) H≡H′)
            (PE.cong (A [_]) H≡H′) ⊢t
  heapUpdate-⊢ʰ (_∙●_ {Δ} {A} ⊢H ⊢A) (there● d) =
    case heapUpdate-⊢ʰ ⊢H d of λ
      ⊢H′ →
    case heapUpdateSubst d of λ
      H≡H′ →
    PE.subst (λ x → Δ ∙ A [ x ] ⊢ʰ _ ∷ _) (PE.sym H≡H′) (⊢H′ ∙● ⊢A)

------------------------------------------------------------------------
-- State typing is preserved by reduction


opaque

  ⊢ₛ-⇒ᵥ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′
        → ∃₂ λ ρ Γ′ → (ρ ∷ Γ′ ⊇ Γ) × Δ ⨾ Γ′ ⊢ s′ ∷ A
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢λt , ⊢e ∙ ⊢S) (lamₕ {H} {p} {t} {E} {u} {E′}) =
    case inversion-∘ₑ ⊢e of λ {
      (F , G , q , ⊢u , PE.refl , B≡Gu) →
    case inversion-lam-Π ⊢λt of λ
      (⊢t , _ , ok) →
    case substTerm ⊢t ⊢u of λ
      ⊢t′ →
    case singleSubstComp (wk E′ u [ H ]ₕ)
         (toSubstₕ H) (wk (lift E) t) of λ
      t≡t′ →
    _ , _ , step {A = wk (toWkₕ H) F} id , _
      , ⊢H ∙ PE.subst (_ ⊢ _ ∷_) (PE.sym (toWkₕ-toSubstₕ H F)) ⊢u
      , conv (PE.subst (_ ⊢_∷ _) t≡t′ ⊢t′) (sym B≡Gu)
      , ⊢ˢ-convₜ (wk-⊢ˢ (step id) ⊢S)
          (conv
            (wk1 (lam p (wk (lift E) t) ∘ wk E′ u) [ H ∙ (p , u , E′) ]ₕ ≡⟨ wk1-tail (lam p (wk (lift E) t) ∘ wk E′ u) ⟩⊢≡
            (lam p (wk (lift E) t) ∘⟨ p ⟩ wk E′ u) [ H ]ₕ                 ≡⟨⟩⊢
            (wk E (lam p t) [ H ]ₕ) ∘⟨ p ⟩ (wk E′ u [ H ]ₕ)               ≡⟨ β-red-≡ ⊢t ⊢u ok ⟩⊢∎≡
            (wk (lift E) t [ H ]⇑ₕ) [ wk E′ u [ H ]ₕ ]₀                  ≡⟨ singleSubstComp (wk E′ u [ H ]ₕ) (toSubstₕ H) (wk (lift E) t) ⟩
            wk (lift E) t [ H ∙ (p , u , E′) ]ₕ                          ∎)
            (sym B≡Gu) )}

  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₁ =
    case inversion-fstₑ ⊢e of λ {
      (F , G , q , ⊢F , ⊢G , PE.refl , B≡F) →
    case inversion-prod-Σ ⊢t of λ
      (⊢t₁ , ⊢t₂ , _ , _ , ok) →
    _ , _ , id , _ , ⊢H , conv ⊢t₁ (sym B≡F)
      , ⊢ˢ-convₜ ⊢S (conv (Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok) (sym B≡F))}

  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₂ =
    case inversion-sndₑ ⊢e of λ {
      (F , G , q , ⊢F , ⊢G , PE.refl , B≡G₊) →
    case inversion-prod-Σ ⊢t of λ
      (⊢t₁ , ⊢t₂ , _ , _ , ok) →
    case Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok of λ
      fstt≡t₁ →
    _ , _ , id , _ , ⊢H
      , conv ⊢t₂ (sym (trans (B≡G₊ ⊢t) (substTypeEq (refl ⊢G) fstt≡t₁)))
      , ⊢ˢ-convₜ ⊢S
         (conv (Σ-β₂-≡ ⊢G ⊢t₁ ⊢t₂ ok) (sym (B≡G₊ ⊢t))) }

  ⊢ₛ-⇒ᵥ {(k)} {(_)} {(m)} (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) (prodʷₕ {H} {p} {t₁} {t₂} {E} {r} {q} {A} {u} {E′} {S}) =
    case inversion-prodrecₑ ⊢e of λ {
      (F , G , _ , ⊢u , ⊢A , PE.refl , B≡A₊) →
    case inversion-prod-Σ ⊢t of λ
      (⊢t₁ , ⊢t₂ , _ , _ , ok) →
    case begin
          (wk (liftn E′ 2) u) [ liftSubstn (toSubstₕ H) 2 ] [ wk E t₁ [ H ]ₕ , wk E t₂ [ H ]ₕ ]₁₀
            ≡⟨ doubleSubstComp (wk (liftn E′ 2) u) _ _ _ ⟩
          wk (liftn E′ 2) u [ consSubst (consSubst (toSubstₕ H) (wk E t₁ [ H ]ₕ)) (wk E t₂ [ H ]ₕ) ]
            ≡˘⟨ PE.cong (λ x → wk (liftn E′ 2) u [ consSubst (toSubstₕ H₁) x ]) (step-consSubst t₂) ⟩
          wk (liftn E′ 2) u [ H₂ ]ₕ ∎ of λ
      u≡u′ →
    case substitutionTerm {σ = consSubst (sgSubst (wk E t₁ [ H ]ₕ)) (wk E t₂ [ H ]ₕ)}
           ⊢u (singleSubst ⊢t₁ , ⊢t₂) (wfTerm ⊢t₁) of λ
      ⊢u′ →
    case begin
           wk (lift E′) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑² [ wk E t₁ [ H ]ₕ , wk E t₂ [ H ]ₕ ]₁₀
             ≡˘⟨ substCompProdrec (wk (lift E′) A [ H ]⇑ₕ) _ _ idSubst ⟩
           wk (lift E′) A [ H ]⇑ₕ [ liftSubst idSubst ] [ wk E (prodʷ p t₁ t₂) [ H ]ₕ ]₀
             ≡⟨ PE.cong (_[ prodʷ p (wk E t₁ [ H ]ₕ) (wk E t₂ [ H ]ₕ) ]₀) (substVar-to-subst subst-lift-id (wk (lift E′) A [ H ]⇑ₕ)) ⟩
           wk (lift E′) A [ H ]⇑ₕ [ idSubst ] [ wk E (prodʷ p t₁ t₂) [ H ]ₕ ]₀
             ≡⟨ PE.cong (_[ prodʷ p (wk E t₁ [ H ]ₕ) (wk E t₂ [ H ]ₕ) ]₀) (subst-id (wk (lift E′) A [ H ]⇑ₕ)) ⟩
           wk (lift E′) A [ H ]⇑ₕ [ wk E (prodʷ p t₁ t₂) [ H ]ₕ ]₀ ∎ of λ
      A₊≡ →
    case PE.subst₂ (_ ⊢_∷_) u≡u′ A₊≡ ⊢u′ of λ
      ⊢u″ →
    case begin
           G [ wk E t₁ [ H ]ₕ ]₀               ≡⟨ substVar-to-subst (λ { x0 → PE.refl
                                                                      ; (x +1) → PE.sym (toWkₕ-toSubstₕ-var H x)
                                                                      }) G ⟩
           G [ toSubstₕ H₁ ₛ• lift (toWkₕ H) ] ≡˘⟨ subst-wk G ⟩
           wk (lift (toWkₕ H)) G [ H₁ ]ₕ       ∎ of λ
      Gt₁≡ →
    _ , _ , step {A = wk (lift (toWkₕ H)) G} (step {A = wk (toWkₕ H) F} id) , _
      , ⊢H ∙ PE.subst (_ ⊢ _ ∷_) (PE.sym (toWkₕ-toSubstₕ H F)) ⊢t₁
           ∙ PE.subst₂ (_ ⊢_∷_) (PE.sym (step-consSubst t₂)) Gt₁≡ ⊢t₂
      , conv ⊢u″ (sym (B≡A₊ ⊢t))
      , ⊢ˢ-convₜ (wk-⊢ˢ (step (step id)) ⊢S) (conv
         (wk (step (step id)) (prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u)) [ H₂ ]ₕ
           ≡⟨ step-consSubst (prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u)) ⟩⊢≡
         wk (step id) (prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u)) [ H₁ ]ₕ
           ≡⟨ step-consSubst (prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u)) ⟩⊢≡
         wk id (prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u)) [ H ]ₕ
           ≡⟨ PE.cong (_[ H ]ₕ) (wk-id (prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u))) ⟩⊢≡
         prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u) [ H ]ₕ
           ≡⟨ prodrec-β-≡ ⊢A ⊢t₁ ⊢t₂ ⊢u ok ⟩⊢∎≡
         (wk (liftn E′ 2) u) [ liftSubstn (toSubstₕ H) 2 ] [ wk E t₁ [ H ]ₕ , wk E t₂ [ H ]ₕ ]₁₀
           ≡⟨ u≡u′ ⟩
         wk (liftn E′ 2) u [ H₂ ]ₕ ∎)
         (sym (B≡A₊ ⊢t)))}
    where
    H₁ : Heap k (1+ m)
    H₁ = H ∙ (∣ S ∣ · r · p , t₁ , E)
    H₂ : Heap k (2+ m)
    H₂ = H ∙ (∣ S ∣ · r · p , t₁ , E) ∙ (∣ S ∣ · r , t₂ , step E)

  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) zeroₕ =
    case inversion-natrecₑ ⊢e of λ {
      (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
    _ , _ , id , _ , ⊢H
      , conv ⊢z (sym (B≡ ⊢t))
      , ⊢ˢ-convₜ ⊢S (conv (natrec-zero ⊢A ⊢z ⊢s) (sym (B≡ ⊢t))) }
  ⊢ₛ-⇒ᵥ {Δ} (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) (sucₕ {H} {t} {E} {p} {q} {r} {(n)} {A} {z} {s} {E′}) =
    case inversion-natrecₑ ⊢e of λ {
      (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
    case inversion-suc ⊢t of λ
      (⊢t′ , _) →
    case natrecⱼ ⊢A ⊢z ⊢s ⊢t′ of λ
      ⊢natrec →
    case PE.subst₂ (Δ ⊢_∷_) (lift-step-natrec A z s _)
          (singleSubstComp (wk E t [ H ]ₕ) (toSubstₕ H) (wk (lift E′) A))
          ⊢natrec of λ
      ⊢natrec′ →
    case PE.subst₂ (Δ ⊢_≡_∷ wk (lift E′) A [ H ]⇑ₕ [ suc (wk E t [ H ]ₕ) ]₀)
           (lift-step-natrec′ {σ = toSubstₕ H} {ρ = E′} A z s (suc (wk E t)))
           (PE.trans (substCompEq (wk (liftn E′ 2) s))
             (substVar-to-subst (λ { x0 → lift-step-natrec A z s _
                                   ; (x0 +1) → PE.refl
                                   ; (x +2) → PE.trans (wk1-tail (wk1 (toSubstₕ H x))) (wk1-sgSubst (toSubstₕ H x) _)})
               (wk (liftn E′ 2) s)))
           (natrec-suc ⊢A ⊢z ⊢s ⊢t′) of λ
      nr-β-≡ →
    case syntacticEqTerm nr-β-≡ of λ
      (_ , _ , ⊢s₊) →
    _ , _ , step {A = wk (lift E′) A} (step {A = ℕ} id) , _
      , ⊢H ∙ ⊢t′ ∙ ⊢natrec′
      , conv ⊢s₊ (sym (B≡ ⊢t))
      , ⊢ˢ-convₜ (wk-⊢ˢ (step (step id)) ⊢S)
          (conv nr-β-≡ (sym (B≡ ⊢t)))}
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) starʷₕ =
    case inversion-unitrecₑ ⊢e of λ {
      (⊢u , ⊢A , no-η , PE.refl , B≡) →
    case ⊢∷Unit→Unit-allowed ⊢t of λ
      ok →
    _ , _ , id , _
      , ⊢H , conv ⊢u (sym (B≡ ⊢t))
      , ⊢ˢ-convₜ ⊢S (conv (unitrec-β-≡ ⊢A ⊢u) (sym (B≡ ⊢t))) }
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢S) (unitrec-ηₕ η) =
    case inversion-unitrec ⊢t of λ
      (⊢A , ⊢t , ⊢u , A≡) →
    _ , _ , id , _ , ⊢H
      , conv ⊢u (trans (substTypeEq (refl ⊢A) (Unit-η-≡ (inj₂ η) ⊢t)) (sym A≡))
      , ⊢ˢ-convₜ ⊢S (conv (unitrec-β-η-≡ ⊢A ⊢t ⊢u η) (sym A≡))
  ⊢ₛ-⇒ᵥ (_ , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) (rflₕⱼ {H} {p} {q} {A} {t} {B} {u} {v} {E′}) =
    case inversion-Jₑ ⊢e of λ {
      (⊢u , ⊢B , PE.refl , B′≡) →
    case inversion-rfl-Id ⊢rfl of λ
      t≡v →
    case syntacticEqTerm t≡v of λ
      (⊢A , ⊢t , ⊢v) →
    case J-motive-rfl-cong (refl ⊢B) t≡v of λ
      Bt≡Bv →
    _ , _ , id , _ , ⊢H
      , conv ⊢u (trans Bt≡Bv (sym (B′≡ ⊢rfl)))
      , ⊢ˢ-convₜ ⊢S (conv
        (⦅ Jₑ p q A t B u v E′ ⦆ᵉ rfl [ H ]ₕ
          ≡⟨ J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (sym t≡v) (refl (rflⱼ′ t≡v)) ⟩⊢
        ⦅ Jₑ p q A t B u t E′ ⦆ᵉ rfl [ H ]ₕ
          ≡⟨ conv (J-β-≡ ⊢t ⊢B ⊢u) (J-motive-rfl-cong (refl ⊢B) t≡v) ⟩⊢∎
        wk E′ u [ H ]ₕ ∎)
        (sym (B′≡ ⊢rfl))) }
  ⊢ₛ-⇒ᵥ (_ , ⊢H , ⊢rfl , ⊢e ∙ ⊢S)  (rflₕₖ {H} {p} {A} {t} {B} {u} {E′}) =
    case inversion-Kₑ ⊢e of λ {
      (⊢u , ⊢B , ok , PE.refl , B′≡) →
    _ , _ , id , _ , ⊢H
      , conv ⊢u (sym (B′≡ ⊢rfl))
      , ⊢ˢ-convₜ ⊢S (conv (K-β-≡ ⊢B ⊢u ok) (sym (B′≡ ⊢rfl))) }
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕₑ =
    case inversion-[]-congₑ ⊢e of λ {
      (ok , PE.refl , B≡) →
    case inversion-rfl-Id ⊢rfl of λ
      t≡u →
    case syntacticEqTerm t≡u of λ
      (⊢A , ⊢t , ⊢u) →
    _ , _ , id , _ , ⊢H
      , conv (rflⱼ′ (ET.[]-cong′ ([]-cong→Erased ok) t≡u)) (sym (B≡ ⊢t ⊢u))
      , ⊢ˢ-convₜ ⊢S (conv ([]-cong-β-≡ t≡u ok) (sym (B≡ ⊢t ⊢u))) }

opaque

  ⊢ₛ-⇒ₙ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ₙ s′
        → Δ ⨾ Γ ⊢ s′ ∷ A
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) (varₕ {t} d) =
    case heapUpdate-⊢ʰ ⊢H d of λ
      ⊢H′ →
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (_ ⊢ _ ≡_∷ A)
           (heapSubstVar d) (refl ⊢t) of λ
      x[H]≡t[H] →
    _ , ⊢H′
      , PE.subst (_ ⊢_∷ A)
          (PE.trans (heapSubstVar d)
            (PE.cong (wk _ t [_]) H≡H′)) ⊢t
      , heapUpdate-⊢ˢ (⊢ˢ-convₜ ⊢S x[H]≡t[H]) d
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) (varₕ′ d) =
    case PE.subst (_ ⊢ _ ≡_∷ A)
           (heapSubstVar′ d) (refl ⊢t) of λ
      x[H]≡t[H] →
    _ , ⊢H , PE.subst (_ ⊢_∷ A) (heapSubstVar′ d) ⊢t
      , ⊢ˢ-convₜ ⊢S x[H]≡t[H]
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) appₕ =
    case inversion-app ⊢t of λ
      (F , G , q , ⊢t , ⊢u , A≡Gu) →
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ
      (⊢F , ⊢G , ok) →
     _ , ⊢H , ⊢t
       , conv (∘ₑ ⊢u ⊢G) (sym A≡Gu) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) fstₕ =
    case inversion-fst ⊢t of λ
      (F , G , q , ⊢F , ⊢G , ⊢t , A≡F) →
    _ , ⊢H , ⊢t
      , conv (fstₑ ⊢F ⊢G) (sym A≡F) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) sndₕ =
    case inversion-snd ⊢t of λ
      (F , G , q , ⊢F , ⊢G , ⊢t , A≡Gt) →
    _ , ⊢H , ⊢t
      , conv (sndₑ ⊢F ⊢G) (sym A≡Gt) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) prodrecₕ =
    case inversion-prodrec ⊢t of λ
      (F , G , q , ⊢F , ⊢G , ⊢B , ⊢t , ⊢u , A≡Bt) →
    _ , ⊢H , ⊢t , conv (prodrecₑ ⊢u ⊢B) (sym A≡Bt) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) natrecₕ =
    case inversion-natrec ⊢t of λ
      (⊢A , ⊢z , ⊢s , ⊢n , C≡) →
    _ , ⊢H , ⊢n
      , conv (natrecₑ ⊢z ⊢s ⊢A) (sym C≡) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) (unitrecₕ no-η) =
    case inversion-unitrec ⊢t of λ
      (⊢A , ⊢t , ⊢u , B≡At) →
    _ , ⊢H , ⊢t
      , conv (unitrecₑ ⊢u ⊢A no-η) (sym B≡At) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) emptyrecₕ =
    case inversion-emptyrec ⊢t of λ
      (⊢A , ⊢t , A≡) →
    _ , ⊢H , ⊢t , conv (emptyrecₑ ⊢A) (sym A≡) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) Jₕ =
    case inversion-J ⊢t of λ
      (_ , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , A≡B₊) →
     _ , ⊢H , ⊢w , conv (Jₑ ⊢u ⊢B) (sym A≡B₊) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) Kₕ =
    case inversion-K ⊢t of λ
      (_ , ⊢t , ⊢B , ⊢u , ⊢v , ok , A≡B₊) →
    _ , ⊢H , ⊢v , conv (Kₑ ⊢u ⊢B ok) (sym A≡B₊) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) []-congₕ =
    case inversion-[]-cong ⊢t of λ
      (_ , ⊢t , ⊢u , ⊢v , ok , A≡Id) →
    _ , ⊢H , ⊢v , conv ([]-congₑ ok) (sym A≡Id) ∙ ⊢S

opaque

  ⊢ₛ-⇒ₙ* : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ₙ* s′
         → Δ ⨾ Γ ⊢ s′ ∷ A
  ⊢ₛ-⇒ₙ* ⊢s id = ⊢s
  ⊢ₛ-⇒ₙ* ⊢s (d ⇨ d′) = ⊢ₛ-⇒ₙ* (⊢ₛ-⇒ₙ ⊢s d) d′

opaque

  ⊢ₛ-⇒ₛ : ⦃ ℕ-Fullred ⦄
        → Δ ⨾ Γ ⊢ s ∷ A → s ⇒ₛ s′
        → Δ ⨾ Γ ⊢ s′ ∷ A
  ⊢ₛ-⇒ₛ (A , ⊢H , ⊢t , ⊢S) (sucₕ x) =
    case inversion-suc ⊢t of λ
      (⊢t , A≡ℕ) →
    _ , ⊢H , ⊢t , conv sucₑ (sym A≡ℕ) ∙ ⊢S
  ⊢ₛ-⇒ₛ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) (numₕ x) =
    case inversion-sucₑ ⊢e of λ {
      (ok , PE.refl , B≡ℕ) →
    _ , ⊢H , conv (sucⱼ ⊢t) (sym (B≡ℕ (wfTerm ⊢t))) , ⊢S}

opaque

  ⊢ₛ-⇒ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ s′
       → ∃₂ λ ρ Γ′ → (ρ ∷ Γ′ ⊇ Γ) × Δ ⨾ Γ′ ⊢ s′ ∷ A
  ⊢ₛ-⇒ ⊢s (⇒ₙ d) = _ , _ , id , ⊢ₛ-⇒ₙ ⊢s d
  ⊢ₛ-⇒ ⊢s (⇒ᵥ d) = ⊢ₛ-⇒ᵥ ⊢s d
  ⊢ₛ-⇒ ⊢s (⇒ₛ d) = _ , _ , id , ⊢ₛ-⇒ₛ ⊢s d


opaque

  ⊢ₛ-⇒* : Δ ⨾ Γ ⊢ s ∷ A → s ⇒* s′
        → ∃₂ λ ρ Γ′ → (ρ ∷ Γ′ ⊇ Γ) × Δ ⨾ Γ′ ⊢ s′ ∷ A
  ⊢ₛ-⇒* ⊢s id = _ , _ , id , ⊢s
  ⊢ₛ-⇒* ⊢s (d ⇨ d′) =
    case ⊢ₛ-⇒ ⊢s d of λ
      (_ , _ , ρ , ⊢s′) →
    case ⊢ₛ-⇒* ⊢s′ d′ of λ
      (_ , _ , ρ′ , ⊢s″) →
    _ , _ , (ρ′ W.•ₜ ρ) , ⊢s″

private

  opaque

    -- A relation which is either definitional equality or reduction
    -- depending on a boolean.
    -- Used to reduce code duplication between ⇒ᵥ→⇒ and ⇒ᵥ→≡ below.

    _⊢⟨_⟩_⇒/≡_∷_ : (Γ : Con Term n) (b : Bool) (t u A : Term n) → Set a
    Γ ⊢⟨ true ⟩ t ⇒/≡ u ∷ A = _⊢_⇒_∷_ Γ t u A
    Γ ⊢⟨ false ⟩ t ⇒/≡ u ∷ A = Γ ⊢ t ≡ u ∷ A

  opaque
    unfolding _⊢⟨_⟩_⇒/≡_∷_

    ⊢⦅⦆ˢ-subst/cong : (b : Bool) → (T b → ¬ℕ-Fullred)
                   → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
                   → Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A
                   → Δ ⊢⟨ b ⟩ ⦅ S ⦆ˢ t [ H ]ₕ ⇒/≡ ⦅ S ⦆ˢ u [ H ]ₕ ∷ B
    ⊢⦅⦆ˢ-subst/cong true prop ⊢S t⇒u = ⊢⦅⦆ˢ-subst ⦃ prop _ ⦄ ⊢S t⇒u
    ⊢⦅⦆ˢ-subst/cong false _ ⊢S t≡u = ⊢⦅⦆ˢ-cong ⊢S (subsetTerm t≡u)

  opaque

    ⇒ᵥ→⇒/≡ : (b : Bool) → (T b → ¬ℕ-Fullred)
           → Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′
           → Δ ⊢⟨ b ⟩ ⦅ s ⦆ ⇒/≡ ⦅ s′ ⦆ ∷ A
    ⇒ᵥ→⇒/≡ {A} b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S)
           (lamₕ {H} {p} {t} {E} {u} {E′} {S}) =
      case inversion-∘ₑ ⊢e of λ {
        (F , G , q , ⊢u , PE.refl , C≡Gu) →
      case PE.subst (_ ⊢ (wk E (lam p t) ∘⟨ p ⟩ wk E′ u) [ H ]ₕ ⇒_∷ _)
             (PE.trans (singleSubstComp (wk E′ u [ H ]ₕ) (toSubstₕ H) (wk (lift E) t))
               (substConsId {t = wk E′ u} (wk (lift E) t)))
             (β-red-⇒₁ ⊢t ⊢u) of λ
        β-⇒ →
      PE.subst (_ ⊢⟨ b ⟩ ⦅ S ⦆ˢ (wk E (lam p t) ∘ wk E′ u) [ H ]ₕ ⇒/≡_∷ A) lemma
        (⊢⦅⦆ˢ-subst/cong {u = wk (lift E) t [ wk E′ u ]₀} b prop ⊢S (conv β-⇒ (sym C≡Gu)))}
      where
      lemma : ⦅ S ⦆ˢ (wk (lift E) t [ wk E′ u ]₀) [ H ]ₕ
            PE.≡ ⦅ wk1ˢ S ⦆ˢ (wk (lift E) t) [ H ∙ (p , u , E′) ]ₕ
      lemma = begin
        ⦅ S ⦆ˢ (wk (lift E) t [ wk E′ u ]₀) [ H ]ₕ
          ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-sgSubst S) ⟩
        ⦅ wk1ˢ S ⦆ˢ (wk (lift E) t) [ wk E′ u ]₀ [ H ]ₕ
          ≡⟨ singleSubstLift (⦅ wk1ˢ S ⦆ˢ (wk (lift E) t)) (wk E′ u) ⟩
        ⦅ wk1ˢ S ⦆ˢ (wk (lift E) t) [ liftSubst (toSubstₕ H) ] [ wk E′ u [ H ]ₕ ]₀
          ≡⟨ singleSubstComp _ (toSubstₕ H) (⦅ wk1ˢ S ⦆ˢ (wk (lift E) t)) ⟩
        ⦅ wk1ˢ S ⦆ˢ (wk (lift E) t) [ H ∙ (p , u , E′) ]ₕ ∎

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₁ =
      case inversion-fstₑ ⊢e of λ {
      (F′ , G′ , q′ , ⊢F′ , ⊢G′ , PE.refl , C≡F′) →
      case inversion-prod ⊢t of λ
        (F , G , q , ⊢F , ⊢G , ⊢t₁ , ⊢t₂ , B≡Σ , ok) →
      case Σ-injectivity (sym B≡Σ) of λ
        (F≡F′ , _) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (Σ-β₁-⇒ ⊢G ⊢t₁ ⊢t₂ ok)
        (trans F≡F′ (sym C≡F′))) }

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₂ =
      case inversion-sndₑ ⊢e of λ {
        (F′ , G′ , q′ , ⊢F′ , ⊢G′ , PE.refl , C≡G′₊) →
      case inversion-prod ⊢t of λ
        (F , G , q , ⊢F , ⊢G , ⊢t₁ , ⊢t₂ , B≡Σ , ok) →
      case Σ-injectivity (sym B≡Σ) of λ
        (F≡F′ , G≡G′ , _) →
      case substTypeEq G≡G′ (refl (conv (fstⱼ′ ⊢t) (sym F≡F′))) of λ
        G₊≡G′₊ →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (Σ-β₂-⇒ ⊢G ⊢t₁ ⊢t₂ ok)
        (trans G₊≡G′₊ (sym (C≡G′₊ ⊢t)))) }

    ⇒ᵥ→⇒/≡ {(k)} {(_)} {(m)} b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S)
           (prodʷₕ {H} {p} {t₁} {t₂} {E} {r} {q} {A} {u} {E′} {S}) =
      case inversion-prodrecₑ ⊢e of λ {
        (F , G , q′ , ⊢u , ⊢A , PE.refl , C≡) →
      case PE.subst (_ ⊢ prodrec r p q (wk (lift E′) A) (wk E (prodʷ p t₁ t₂)) (wk (liftn E′ 2) u) [ H ]ₕ ⇒_∷ _)
             (PE.sym ([,]-[]-commute {u = wk E t₁} {v = wk E t₂} (wk (liftn E′ 2) u)))
             (prodrec-β-⇒₁ ⊢A ⊢t ⊢u) of λ
        β-⇒ →
      PE.subst (_ ⊢⟨ b ⟩ ⦅ S ⦆ˢ (prodrec r p q _ _ _) [ H ]ₕ ⇒/≡_∷ _) lemma
        (⊢⦅⦆ˢ-subst/cong {u = wk (liftn E′ 2) u [ wk E t₁ , wk E t₂ ]₁₀}
                       b prop ⊢S (conv β-⇒ (sym (C≡ ⊢t))))}
      where
      H₂ : Heap k (2+ m)
      H₂ = H ∙ (∣ S ∣ · r · p , t₁ , E) ∙ (∣ S ∣ · r , t₂ , step E)
      lemma : ⦅ S ⦆ˢ ((wk (liftn E′ 2) u) [ wk E t₁ , wk E t₂ ]₁₀) [ H ]ₕ
            PE.≡ ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) u) [ H₂ ]ₕ
      lemma = begin
        ⦅ S ⦆ˢ ((wk (liftn E′ 2) u) [ wk E t₁ , wk E t₂ ]₁₀) [ H ]ₕ
          ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-[,] S) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) u) [ wk E t₁ , wk E t₂ ]₁₀ [ H ]ₕ
          ≡⟨ [,]-[]-fusion (⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) u)) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) u) [ consSubst (consSubst (toSubstₕ H) (wk E t₁ [ H ]ₕ)) (wk E t₂ [ H ]ₕ) ]
          ≡⟨ PE.cong (λ x → ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) u) [ consSubst _ x ]) (PE.sym (step-consSubst t₂)) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) u) [ H₂ ]ₕ ∎


    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) zeroₕ =
      case inversion-natrecₑ ⊢e of λ {
        (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (natrec-zero ⊢A ⊢z ⊢s)
        (sym (B≡ ⊢t))) }

    ⇒ᵥ→⇒/≡ {(k)} {(_)} {(m)} b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S)
      (sucₕ {H} {t} {E} {p} {q} {r} {(n)} {A} {z} {s} {E′} {S}) =
      case inversion-natrecₑ ⊢e of λ {
        (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
      case PE.subst (_ ⊢ nr (wk E (suc t)) [ H ]ₕ ⇒_∷ _)
             (PE.sym ([,]-[]-commute (wk (liftn E′ 2) s)))
             (natrec-suc ⊢A ⊢z ⊢s (inversion-suc ⊢t .proj₁)) of λ
        β-⇒ →
      case ⊢⦅⦆ˢ-subst/cong {u = wk (liftn E′ 2) s [ wk E t , nr (wk E t) ]₁₀}
             b prop ⊢S (conv β-⇒ (sym (B≡ ⊢t))) of λ
        d →
      PE.subst (_ ⊢⟨ b ⟩ ⦅ S ⦆ˢ (nr (wk E (suc t))) [ H ]ₕ ⇒/≡_∷ _)
        lemma d }
      where
      nr : Term m → Term m
      nr = natrec p q r (wk (lift E′) A) (wk E′ z) (wk (liftn E′ 2) s)
      nr′ : Term (1+ n)
      nr′ = natrec p q r (wk (lift (step id)) A) (wk1 z) (wk (liftn (step id) 2) s) (var x0)
      H₂ : Heap k (2+ m)
      H₂ = H ∙ (p + r , t , E) ∙ (r , nr′ , lift E′)
      lemma′ : nr (wk E t) [ H ]ₕ PE.≡ wk (lift E′) nr′ [ H ∙ (p + r , t , E) ]ₕ
      lemma′ = begin
        nr (wk E t) [ H ]ₕ ≡⟨ lift-step-natrec A z s _ ⟩
        wk (lift E′) nr′ [ H ∙ (p + r , t , E) ]ₕ ∎
      lemma : ⦅ S ⦆ˢ ((wk (liftn E′ 2) s) [ wk E t , nr (wk E t) ]₁₀) [ H ]ₕ
            PE.≡ ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) s) [ H₂ ]ₕ
      lemma = begin
        ⦅ S ⦆ˢ ((wk (liftn E′ 2) s) [ wk E t , nr (wk E t) ]₁₀) [ H ]ₕ
          ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-[,] S) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) s) [ wk E t , nr (wk E t) ]₁₀ [ H ]ₕ
              ≡⟨ [,]-[]-fusion (⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) s)) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) s) [ consSubst (consSubst (toSubstₕ H) (wk E t [ H ]ₕ)) (nr (wk E t) [ H ]ₕ) ]
          ≡⟨ PE.cong (λ x → ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) s) [ consSubst (consSubst (toSubstₕ H) (wk E t [ H ]ₕ)) x ]) lemma′ ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn E′ 2) s) [ H₂ ]ₕ ∎

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) starʷₕ =
      case inversion-unitrecₑ ⊢e of λ {
        (⊢u , ⊢A , no-η , PE.refl , C≡A₊) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (unitrec-β-⇒ ⊢A ⊢u) (sym (C≡A₊ ⊢t)))}
    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢S) (unitrec-ηₕ η) =
      case inversion-unitrec ⊢t of λ
        (⊢A , ⊢t , ⊢u , A≡) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S
        (conv (unitrec-β-η-⇒ ⊢A ⊢t ⊢u η) (sym A≡))

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕⱼ =
      case inversion-Jₑ ⊢e of λ {
        (⊢w , ⊢B , PE.refl , ≡B) →
      case inversion-rfl-Id ⊢rfl of λ
        t≡v →
      case trans (J-motive-rfl-cong (refl ⊢B) t≡v) (sym (≡B ⊢rfl)) of λ
        ≡B′ →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (J-β-⇒ t≡v ⊢B ⊢w) ≡B′)}
    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕₖ =
      case inversion-Kₑ ⊢e of λ {
        (⊢v , ⊢B , ok , PE.refl , B′≡)  →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (K-β-⇒ ⊢B ⊢v ok) (sym (B′≡ ⊢rfl)))}
    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕₑ =
      case inversion-[]-congₑ ⊢e of λ {
        (ok , PE.refl , B′≡) →
      case inversion-rfl-Id ⊢rfl of λ
        t≡u →
      case syntacticEqTerm t≡u of λ
        (_ , ⊢t , ⊢u) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv ([]-cong-β-⇒ t≡u ok) (sym (B′≡ ⊢t ⊢u))) }

opaque
  unfolding _⊢⟨_⟩_⇒/≡_∷_

  -- Reduction of values correspond to one step in the wh cbn reduction

  ⇒ᵥ→⇒ : ⦃ ¬fr : ¬ℕ-Fullred ⦄
       → Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′ → _⊢_⇒_∷_ Δ ⦅ s ⦆ ⦅ s′ ⦆ A
  ⇒ᵥ→⇒ ⦃ ¬fr ⦄ = ⇒ᵥ→⇒/≡ true (λ _ → ¬fr)

opaque
  unfolding _⊢⟨_⟩_⇒/≡_∷_

  -- Reduction of values preserves definitional equality

  ⇒ᵥ→≡ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′ → _⊢_≡_∷_ Δ ⦅ s ⦆ ⦅ s′ ⦆ A
  ⇒ᵥ→≡ = ⇒ᵥ→⇒/≡ false (λ ())

opaque

  -- Reduction preserves definitional equality

  ⇒→≡ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ s′ → _⊢_≡_∷_ Δ ⦅ s ⦆ ⦅ s′ ⦆ A
  ⇒→≡ (_ , _ , ⊢t , ⊢S) (⇒ₙ d) =
    PE.subst (_ ⊢ _ ≡_∷ _) (⇒ₙ-⦅⦆-≡ d) (refl (⊢⦅⦆ˢ ⊢S ⊢t))
  ⇒→≡ ⊢s (⇒ᵥ d) =
    ⇒ᵥ→≡ ⊢s d
  ⇒→≡ (_ , _ , ⊢t , ⊢S) (⇒ₛ d) =
    PE.subst (_ ⊢ _ ≡_∷ _) (⇒ₛ-⦅⦆-≡ d) (refl (⊢⦅⦆ˢ ⊢S ⊢t))

opaque

  -- Reduction preserves definitional equality

  ⇒*→≡ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒* s′ → _⊢_≡_∷_ Δ ⦅ s ⦆ ⦅ s′ ⦆ A
  ⇒*→≡ (_ , _ , ⊢t , ⊢S) id = refl (⊢⦅⦆ˢ ⊢S ⊢t)
  ⇒*→≡ ⊢s (x ⇨ d) =
    trans (⇒→≡ ⊢s x) (⇒*→≡ (⊢ₛ-⇒ ⊢s x .proj₂ .proj₂ .proj₂) d)

opaque

  -- Values in non-empty stacks always reduce

  ⊢Value-⇒ᵥ : ⦃ ¬fr : ¬ℕ-Fullred ⦄
            → Consistent Δ
            → Δ ⨾ Γ ⊢ ⟨ H , t , E , e ∙ S ⟩ ∷ A → Value t
            → ∃₃ λ m n (s : State _ m n) → ⟨ H , t , E , e ∙ S ⟩ ⇒ᵥ s
  ⊢Value-⇒ᵥ {e = ∘ₑ p u E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-∘ₑ ⊢e of λ {
      (_ , _ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam-Π ⊢t of λ {
          (_ , PE.refl , _) →
        _ , _ , _ , lamₕ}
      zeroᵥ  → ⊥-elim (ℕ≢Π (sym (inversion-zero ⊢t)))
      sucᵥ   → ⊥-elim (ℕ≢Π (sym (inversion-suc ⊢t .proj₂)))
      starᵥ  → ⊥-elim (Unit≢Πⱼ (sym (inversion-star ⊢t .proj₁)))
      prodᵥ  →
        case inversion-prod ⊢t of λ
          (_ , _ , _ , _ , _ , _ , _ , Π≡Σ , _) →
        ⊥-elim (Π≢Σⱼ Π≡Σ)
      rflᵥ   →
        case inversion-rfl ⊢t of λ
          (_ , _ , _ , _ , Π≡Id) →
        ⊥-elim (Id≢Π (sym Π≡Id))
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Π≡U , _) →
        ⊥-elim (U≢Π (sym Π≡U))
      ℕᵥ     → ⊥-elim (U≢Π (sym (inversion-ℕ ⊢t)))
      Unitᵥ  → ⊥-elim (U≢Π (sym (inversion-Unit-U ⊢t .proj₁)))
      Emptyᵥ → ⊥-elim (U≢Π (sym (inversion-Empty ⊢t)))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Π≡U) →
        ⊥-elim (U≢Π (sym Π≡U))}
  ⊢Value-⇒ᵥ {e = fstₑ x} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-fstₑ ⊢e of λ {
      (_ , _ , _ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Σ≡Π , _) →
        ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
      zeroᵥ  → ⊥-elim (ℕ≢Σ (sym (inversion-zero ⊢t)))
      sucᵥ   → ⊥-elim (ℕ≢Σ (sym (inversion-suc ⊢t .proj₂)))
      starᵥ  → ⊥-elim (Unit≢Σⱼ (sym (inversion-star ⊢t .proj₁)))
      prodᵥ  →
        case inversion-prod-Σ ⊢t of λ {
          (_ , _ , PE.refl , PE.refl , _) →
        _ , _ , _ , prodˢₕ₁}
      rflᵥ   →
        case inversion-rfl ⊢t of λ
          (_ , _ , _ , _ , Σ≡Id) →
        ⊥-elim (Id≢Σ (sym Σ≡Id))
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Σ≡U , _) →
        ⊥-elim (U≢Σ (sym Σ≡U))
      ℕᵥ     → ⊥-elim (U≢Σ (sym (inversion-ℕ ⊢t)))
      Unitᵥ  → ⊥-elim (U≢Σ (sym (inversion-Unit-U ⊢t .proj₁)))
      Emptyᵥ → ⊥-elim (U≢Σ (sym (inversion-Empty ⊢t)))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Σ≡U) →
        ⊥-elim (U≢Σ (sym Σ≡U))}
  ⊢Value-⇒ᵥ {e = sndₑ x} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-sndₑ ⊢e of λ {
      (_ , _ , _ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Σ≡Π , _) →
        ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
      zeroᵥ  → ⊥-elim (ℕ≢Σ (sym (inversion-zero ⊢t)))
      sucᵥ   → ⊥-elim (ℕ≢Σ (sym (inversion-suc ⊢t .proj₂)))
      starᵥ  → ⊥-elim (Unit≢Σⱼ (sym (inversion-star ⊢t .proj₁)))
      prodᵥ  →
        case inversion-prod-Σ ⊢t of λ {
          (_ , _ , PE.refl , PE.refl , _) →
        _ , _ , _ , prodˢₕ₂}
      rflᵥ   →
        case inversion-rfl ⊢t of λ
          (_ , _ , _ , _ , Σ≡Id) →
        ⊥-elim (Id≢Σ (sym Σ≡Id))
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Σ≡U , _) →
        ⊥-elim (U≢Σ (sym Σ≡U))
      ℕᵥ     → ⊥-elim (U≢Σ (sym (inversion-ℕ ⊢t)))
      Unitᵥ  → ⊥-elim (U≢Σ (sym (inversion-Unit-U ⊢t .proj₁)))
      Emptyᵥ → ⊥-elim (U≢Σ (sym (inversion-Empty ⊢t)))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Σ≡U) →
        ⊥-elim (U≢Σ (sym Σ≡U))}
  ⊢Value-⇒ᵥ {e = prodrecₑ r p q A u E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-prodrecₑ ⊢e of λ {
      (_ , _ , _ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Σ≡Π , _) →
        ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
      zeroᵥ  → ⊥-elim (ℕ≢Σ (sym (inversion-zero ⊢t)))
      sucᵥ   → ⊥-elim (ℕ≢Σ (sym (inversion-suc ⊢t .proj₂)))
      starᵥ  → ⊥-elim (Unit≢Σⱼ (sym (inversion-star ⊢t .proj₁)))
      prodᵥ  →
        case inversion-prod-Σ ⊢t of λ {
          (_ , _ , PE.refl , PE.refl , _) →
        _ , _ , _ , prodʷₕ}
      rflᵥ   →
        case inversion-rfl ⊢t of λ
          (_ , _ , _ , _ , Σ≡Id) →
        ⊥-elim (Id≢Σ (sym Σ≡Id))
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Σ≡U , _) →
        ⊥-elim (U≢Σ (sym Σ≡U))
      ℕᵥ     → ⊥-elim (U≢Σ (sym (inversion-ℕ ⊢t)))
      Unitᵥ  → ⊥-elim (U≢Σ (sym (inversion-Unit-U ⊢t .proj₁)))
      Emptyᵥ → ⊥-elim (U≢Σ (sym (inversion-Empty ⊢t)))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Σ≡U) →
        ⊥-elim (U≢Σ (sym Σ≡U))}
  ⊢Value-⇒ᵥ {e = natrecₑ p q r A z s E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-natrecₑ ⊢e of λ {
      (_ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , ℕ≡Π , _) →
        ⊥-elim (ℕ≢ΠΣⱼ ℕ≡Π)
      zeroᵥ → _ , _ , _ , zeroₕ
      sucᵥ → _ , _ , _ , sucₕ
      starᵥ → ⊥-elim (ℕ≢Unitⱼ (inversion-star ⊢t .proj₁))
      prodᵥ →
        case inversion-prod ⊢t of λ
          (_ , _ , _ , _ , _ , _ , _ , ℕ≡Σ , _) →
        ⊥-elim (ℕ≢ΠΣⱼ ℕ≡Σ)
      rflᵥ →
        case inversion-rfl ⊢t of λ
          (_ , _ , _ , _ , ℕ≡Id) →
        ⊥-elim (Id≢ℕ (sym ℕ≡Id))
      Uᵥ → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , ℕ≡U , _) →
        ⊥-elim (U≢ℕ (sym ℕ≡U))
      ℕᵥ → ⊥-elim (U≢ℕ (sym (inversion-ℕ ⊢t)))
      Unitᵥ → ⊥-elim (U≢ℕ (sym (inversion-Unit-U ⊢t .proj₁)))
      Emptyᵥ → ⊥-elim (U≢ℕ (sym (inversion-Empty ⊢t)))
      Idᵥ →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , ℕ≡U) →
        ⊥-elim (U≢ℕ (sym ℕ≡U))}
  ⊢Value-⇒ᵥ {e = unitrecₑ p q A u E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-unitrecₑ ⊢e of λ {
      (_ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Unit≡Π , _) →
        ⊥-elim (Unit≢Πⱼ Unit≡Π)
      zeroᵥ  → ⊥-elim (ℕ≢Unitⱼ (sym (inversion-zero ⊢t)))
      sucᵥ   → ⊥-elim (ℕ≢Unitⱼ (sym (inversion-suc ⊢t .proj₂)))
      starᵥ  →
        case inversion-star-Unit ⊢t of λ {
          (PE.refl , _) →
        _ , _ , _ , starʷₕ}
      prodᵥ  →
        case inversion-prod ⊢t of λ
          (_ , _ , _ , _ , _ , _ , _ , Unit≡Σ , _) →
        ⊥-elim (Unit≢Σⱼ Unit≡Σ)
      rflᵥ   →
        case inversion-rfl ⊢t of λ
          (_ , _ , _ , _ , Unit≡Id) →
        ⊥-elim (Id≢Unit (sym Unit≡Id))
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Unit≡U , _) →
        ⊥-elim (U≢Unitⱼ (sym Unit≡U))
      ℕᵥ     → ⊥-elim (U≢Unitⱼ (sym (inversion-ℕ ⊢t)))
      Unitᵥ  → ⊥-elim (U≢Unitⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
      Emptyᵥ → ⊥-elim (U≢Unitⱼ (sym (inversion-Empty ⊢t)))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Unit≡U) →
        ⊥-elim (U≢Unitⱼ (sym Unit≡U))}
  ⊢Value-⇒ᵥ {e = emptyrecₑ p A E} consistent (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-emptyrecₑ ⊢e of λ {
      (_ , PE.refl , _) →
    ⊥-elim (consistent _ ⊢t)}
  ⊢Value-⇒ᵥ {e = Jₑ p q A t B u w E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-Jₑ ⊢e of λ {
      (_ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Id≡Π , _) →
        ⊥-elim (Id≢Π Id≡Π)
      zeroᵥ  → ⊥-elim (Id≢ℕ (inversion-zero ⊢t))
      sucᵥ   → ⊥-elim (Id≢ℕ (inversion-suc ⊢t .proj₂))
      starᵥ  → ⊥-elim (Id≢Unit (inversion-star ⊢t .proj₁))
      prodᵥ  →
        case inversion-prod ⊢t of λ
          (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
        ⊥-elim (Id≢Σ Id≡Σ)
      rflᵥ   → _ , _ , _ , rflₕⱼ
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Id≡U , _) →
        ⊥-elim (Id≢U Id≡U)
      ℕᵥ     → ⊥-elim (Id≢U (inversion-ℕ ⊢t))
      Unitᵥ  → ⊥-elim (Id≢U (inversion-Unit-U ⊢t .proj₁))
      Emptyᵥ → ⊥-elim (Id≢U (inversion-Empty ⊢t))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Id≡U) →
        ⊥-elim (Id≢U Id≡U)}
  ⊢Value-⇒ᵥ {e = Kₑ p A t B u E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-Kₑ ⊢e of λ {
      (_ , _ , _ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Id≡Π , _) →
        ⊥-elim (Id≢Π Id≡Π)
      zeroᵥ  → ⊥-elim (Id≢ℕ (inversion-zero ⊢t))
      sucᵥ   → ⊥-elim (Id≢ℕ (inversion-suc ⊢t .proj₂))
      starᵥ  → ⊥-elim (Id≢Unit (inversion-star ⊢t .proj₁))
      prodᵥ  →
        case inversion-prod ⊢t of λ
          (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
        ⊥-elim (Id≢Σ Id≡Σ)
      rflᵥ   → _ , _ , _ , rflₕₖ
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Id≡U , _) →
        ⊥-elim (Id≢U Id≡U)
      ℕᵥ     → ⊥-elim (Id≢U (inversion-ℕ ⊢t))
      Unitᵥ  → ⊥-elim (Id≢U (inversion-Unit-U ⊢t .proj₁))
      Emptyᵥ → ⊥-elim (Id≢U (inversion-Empty ⊢t))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Id≡U) →
        ⊥-elim (Id≢U Id≡U)}
  ⊢Value-⇒ᵥ {e = []-congₑ s A t u E} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-[]-congₑ ⊢e of λ {
      (_ , PE.refl , _) →
    case v of λ where
      lamᵥ   →
        case inversion-lam ⊢t of λ
          (_ , _ , _ , _ , _ , Id≡Π , _) →
        ⊥-elim (Id≢Π Id≡Π)
      zeroᵥ  → ⊥-elim (Id≢ℕ (inversion-zero ⊢t))
      sucᵥ   → ⊥-elim (Id≢ℕ (inversion-suc ⊢t .proj₂))
      starᵥ  → ⊥-elim (Id≢Unit (inversion-star ⊢t .proj₁))
      prodᵥ  →
        case inversion-prod ⊢t of λ
          (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
        ⊥-elim (Id≢Σ Id≡Σ)
      rflᵥ   → _ , _ , _ , rflₕₑ
      Uᵥ     → ⊥-elim (inversion-U ⊢t)
      ΠΣᵥ    →
        case inversion-ΠΣ-U ⊢t of λ
          (_ , _ , Id≡U , _) →
        ⊥-elim (Id≢U Id≡U)
      ℕᵥ     → ⊥-elim (Id≢U (inversion-ℕ ⊢t))
      Unitᵥ  → ⊥-elim (Id≢U (inversion-Unit-U ⊢t .proj₁))
      Emptyᵥ → ⊥-elim (Id≢U (inversion-Empty ⊢t))
      Idᵥ    →
        case inversion-Id-U ⊢t of λ
          (_ , _ , _ , Id≡U) →
        ⊥-elim (Id≢U Id≡U)}
  ⊢Value-⇒ᵥ {e = sucₑ} _ (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) v =
    case inversion-sucₑ ⊢e of λ
      (fr , _ , _) →
    ⊥-elim (not-ℕ-Fullred-and-¬ℕ-Fullred ⦃ fr ⦄)
