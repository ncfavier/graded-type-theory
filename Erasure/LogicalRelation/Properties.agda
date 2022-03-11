{-# OPTIONS --without-K --safe #-}

open import Tools.Fin

open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Properties {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure′
import Definition.LogicalRelation.Fundamental Erasure′ as F
open import Definition.LogicalRelation.Fundamental.Reducibility  Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
import Definition.LogicalRelation.Irrelevance Erasure′ as I
open import Definition.LogicalRelation.Substitution.Properties Erasure′

open import Definition.Modality.Context ErasureModality

open import Definition.Typed Erasure′
open import Definition.Typed.Consequences.Canonicity Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.RedSteps Erasure′ as RS
open import Definition.Typed.Weakening Erasure′

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure as UP using (noClosedNe ; wk-id ; wk-lift-id)

open import Erasure.Extraction
open import Erasure.Extraction.Properties
open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Conversion
open import Erasure.Target as T hiding (_⇒_; _⇒*_)
open import Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum hiding (id ; sym)
open import Tools.Unit

private
  variable
    n : Nat
    t t′ A : U.Term 0
    v v′ : T.Term 0
    Γ : Con U.Term n
    F G : U.Term n
    p q : Erasure
    γ δ : Conₘ n

-- Subsumption of quantified logical relation
-- If t ® v ◂ p and p ≤ q then t ® v ◂ q

subsumption″ : ∀ {l [A]} → t ®⟨ l ⟩ v ∷ A ◂ p / [A] → p ≤ q
             → t ®⟨ l ⟩ v ∷ A ◂ q / [A]
subsumption″ {p = 𝟘} {𝟘} t®v q≤p = t®v
subsumption″ {p = ω} {𝟘} t®v q≤p = tt
subsumption″ {p = ω} {ω} t®v q≤p = t®v

-- Subsumption of related substitutions
-- If σ ® σ′ ∷ Γ ◂ γ and γ ≤ᶜ δ then σ ® σ′ ∷ Γ ◂ δ

subsumption′ : ∀ {l σₜ σᵥ [Γ] [σ]} → σₜ ®⟨ l ⟩ σᵥ ∷ Γ ◂ γ / [Γ] / [σ] → γ ≤ᶜ δ
             → σₜ ®⟨ l ⟩ σᵥ ∷ Γ ◂ δ / [Γ] / [σ]
subsumption′ {Γ = ε} {ε} {ε} {[Γ] = ε} {lift tt} tt ε = tt
subsumption′ {Γ = Γ ∙ x} {γ ∙ p} {δ ∙ q} {l = l} {[Γ] = [Γ] ∙ [A]} {_ , _} (σ®σ′ , t®v) (γ≤δ ∙ p≤q) =
  subsumption′ {l = l} σ®σ′ γ≤δ , subsumption″ t®v p≤q

-- Subsumption of erasure validity
-- If γ ▸ Γ ⊩ʳ t ∷ A and δ ≤ᶜ γ then δ ▸ Γ ⊩ʳ t ∷ A

subsumption : ∀ {l} {Γ : Con U.Term n} {t A : U.Term n}
            → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A] → δ ≤ᶜ γ
            → δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ A / [Γ] / [A]
subsumption {l = l} [Γ] [A] γ⊩ʳt δ≤γ [σ] σ®σ′ = γ⊩ʳt [σ] (subsumption′ {l = l} σ®σ′ δ≤γ)


-- Logical relation for erasure is preserved under a single reduction backwards on the left term
-- If t′ ® v ∷ A and ε ⊢ t ⇒ t′ ∷ A then t ® v ∷ A

®-redˡ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
       → ε ⊢ t ⇒ t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
®-redˡ (Uᵣ _) (Uᵣ _) t⇒t′ = Uᵣ (redFirstTerm t⇒t′)
®-redˡ (ℕᵣ ([ ⊢A , ⊢B , D ])) (zeroᵣ t′⇒zero v⇒v′) t⇒t′ =
  zeroᵣ ((conv t⇒t′ (subset* D)) ⇨ t′⇒zero) v⇒v′
®-redˡ (ℕᵣ ([ ⊢A , ⊢B , D ])) (sucᵣ t′⇒suc v⇒v′ t®v) t⇒t′ =
  sucᵣ ((conv t⇒t′ (subset* D)) ⇨ t′⇒suc) v⇒v′ t®v
®-redˡ (Unitᵣ ([ ⊢A , ⊢B , D ])) (starᵣ x v⇒star) t⇒t′ =
  starᵣ (conv (redFirstTerm t⇒t′) (subset* D)) v⇒star
®-redˡ (ne′ K D neK K≡K) t®v t⇒t′ = ⊥-elim (noClosedNe neK)
®-redˡ (Bᵣ′ (BΠ 𝟘 q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] =
  let t®v = t®v′ [a]
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-subst (conv t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (_⊢_⇒_∷_ ε _ _) (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G))) t∘a⇒t′∘w′
  in ®-redˡ ([G] id ε [a]) t®v t∘a⇒t′∘w
®-redˡ (Bᵣ′ (BΠ ω q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-subst (conv t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (_⊢_⇒_∷_ ε _ _) (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G))) t∘a⇒t′∘w′
  in ®-redˡ ([G] id ε [a]) t®v t∘a⇒t′∘w
®-redˡ (Bᵣ′ (BΣ p) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
       (t₁ , t₂ , v₁ , v₂ , t′⇒u , v⇒v′ , t®v) t⇒t′ =
         t₁ , t₂ , v₁ , v₂ , ((conv t⇒t′ (subset* D)) ⇨ t′⇒u) , v⇒v′ , t®v
®-redˡ (emb 0<1 [A]) t®v t⇒t′ = ®-redˡ [A] t®v t⇒t′


-- Logical relation for erasure is preserved under reduction closure backwards on the left term
-- If t′ ® v ∷ A and ε ⊢ t ⇒* t′ ∷ A then t ® v ∷ A

®-red*ˡ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
        → ε ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
®-red*ˡ [A] t′®v (id x) = t′®v
®-red*ˡ [A] t′®v (x ⇨ t⇒t′) = ®-redˡ [A] (®-red*ˡ [A] t′®v t⇒t′) x


-- Logical relation for erasure is preserved under a single reduction backwards on the right term
-- If t ® v′ ∷ A and v ⇒ v′ then t ® v ∷ A

®-redʳ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A]
       → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-redʳ (Uᵣ x) (Uᵣ x₁) v⇒v′ = Uᵣ x₁
®-redʳ (ℕᵣ x) (zeroᵣ t′⇒zero v′⇒zero) v⇒v′ = zeroᵣ t′⇒zero (trans v⇒v′ v′⇒zero)
®-redʳ (ℕᵣ x) (sucᵣ t′⇒suc v′⇒suc t®v) v⇒v′ = sucᵣ t′⇒suc (trans v⇒v′ v′⇒suc) t®v
®-redʳ (Unitᵣ x) (starᵣ x₁ v′⇒star) v⇒v′ = starᵣ x₁ (trans v⇒v′ v′⇒star)
®-redʳ (ne′ K D neK K≡K) t®v′ v⇒v′ = ⊥-elim (noClosedNe neK)
®-redʳ (Bᵣ′ (BΠ 𝟘 q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ {a = a} [a] =
  let t®v = t®v′ [a]
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] id ε [a]
  in ®-redʳ [G[a]] t®v v∘w⇒v′∘w′
®-redʳ (Bᵣ′ (BΠ ω q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
       t®v′ v⇒v′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] id ε [a]
  in ®-redʳ [G[a]] t®v v∘w⇒v′∘w′
®-redʳ (Bᵣ′ (BΣ q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
       (t₁ , t₂ , v₁ , v₂ , t⇒t′ , v′⇒w , t®v′) v⇒v′ =
         t₁ , t₂ , v₁ , v₂ , t⇒t′ , trans v⇒v′ v′⇒w , t®v′
®-redʳ (emb 0<1 [A]) t®v′ v⇒v′ = ®-redʳ [A] t®v′ v⇒v′


-- Logical relation for erasure is preserved under reduction closure backwards on the right term
-- If t ® v′ ∷ A and v ⇒* v′ then t ® v ∷ A

®-red*ʳ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A] → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-red*ʳ [A] t®v′ refl = t®v′
®-red*ʳ [A] t®v′ (trans x v⇒v′) = ®-redʳ [A] (®-red*ʳ [A] t®v′ v⇒v′) x


-- Logical relation for erasure is preserved under reduction closure backwards
-- If t′ ® v′ ∷ A and ε ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t ® v ∷ A

®-red₁ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
       → ε ⊢ t ⇒ t′ ∷ A → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-red₁ [A] t′®v′ t⇒t′ v⇒v′ = ®-redʳ [A] (®-redˡ [A] t′®v′ t⇒t′) v⇒v′


-- Logical relation for erasure is preserved under reduction closure backwards
-- If t′ ® v′ ∷ A and ε ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t ® v ∷ A

®-red* : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
       → ε ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-red* [A] t′®v′ t⇒t′ v⇒v′ = ®-red*ʳ [A] (®-red*ˡ [A] t′®v′ t⇒t′) v⇒v′


-- Logical relation for erasure is preserved under one reduction step on the left
-- If t ® v ∷ A and ε ⊢ t ⇒ t′ ∷ A  then t′ ® v ∷ A

®-redˡ′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
        → ε ⊢ t ⇒ t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
®-redˡ′ (Uᵣ x) (Uᵣ x₁) t⇒t′ with syntacticRedTerm (redMany t⇒t′)
... | _ , _ , ε⊢t′∷U = Uᵣ ε⊢t′∷U
®-redˡ′ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t⇒zero v⇒zero) t⇒t′ with whrDet↘Term (t⇒zero , zeroₙ) (conv* (redMany t⇒t′) (subset* D))
... | t′⇒zero = zeroᵣ t′⇒zero v⇒zero
®-redˡ′ (ℕᵣ [ ⊢A , ⊢B , D ]) (sucᵣ t⇒suc v⇒suc t®v) t⇒t′ with whrDet↘Term (t⇒suc , sucₙ) (conv* (redMany t⇒t′) (subset* D))
... | t′⇒suc = sucᵣ t′⇒suc v⇒suc t®v
®-redˡ′ (Unitᵣ x) (starᵣ x₁ v⇒star) t⇒t′ with syntacticRedTerm (redMany t⇒t′)
... | _ , _ , ε⊢t′∷Unit = starᵣ (conv ε⊢t′∷Unit (subset* (red x))) v⇒star
®-redˡ′ (ne′ K D neK K≡K) t®v t⇒t′ = ⊥-elim (noClosedNe neK)
®-redˡ′ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] =
  let t®v = t®v′ [a]
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-subst (conv t⇒t′ (subset* (red D))) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⊢_⇒_∷_ ε _ _)
                          (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  ®-redˡ′ ([G] id ε [a]) t®v t∘a⇒t′∘a
®-redˡ′ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-subst (conv t⇒t′ (subset* (red D))) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⊢_⇒_∷_ ε _ _)
                          (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  ®-redˡ′ ([G] id ε [a]) t®v t∘a⇒t′∘a
®-redˡ′ (Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
        (t₁ , t₂ , v₁ , v₂ , t⇒u , v⇒v′ , t®v) t⇒t′ =
         t₁ , t₂ , v₁ , v₂ , reddet (conv t⇒t′ (subset* (red D))) (t⇒u , prodₙ) , v⇒v′ , t®v
    where
    reddet : ∀ {t t′ u A} → ε ⊢ t ⇒ t′ ∷ A → ε ⊢ t ↘ u ∷ A → ε ⊢ t′ ⇒* u ∷ A
    reddet t⇒t′ ((id x) , w) rewrite whnfRed*Term (redMany t⇒t′) w = id x
    reddet t⇒t′ ((x ⇨ t⇒u) , w) rewrite whrDetTerm t⇒t′ x = t⇒u
®-redˡ′ (emb 0<1 [A]) t®v t⇒t′ = ®-redˡ′ [A] t®v t⇒t′


-- Logical relation for erasure is preserved under reduction closure on the left
-- If t ® v ∷ A and ε ⊢ t ⇒* t′ ∷ A  then t′ ® v ∷ A

®-red*ˡ′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
         → ε ⊢ t ⇒* t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
®-red*ˡ′ [A] t®v (id x) = t®v
®-red*ˡ′ [A] t®v (x ⇨ t⇒t′) = ®-red*ˡ′ [A] (®-redˡ′ [A] t®v x) t⇒t′


-- Logical relation for erasure is preserved under one reduction step on the right
-- If t ® v ∷ A and v ⇒ v′  then t ® v′ ∷ A

®-redʳ′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
        → v T.⇒ v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
®-redʳ′ (Uᵣ x) (Uᵣ x₁) v⇒v′ = Uᵣ x₁
®-redʳ′ (ℕᵣ x) (zeroᵣ x₁ v⇒zero) v⇒v′ with red*Det v⇒zero (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite zero-noRed x₂ = zeroᵣ x₁ T.refl
... | inj₂ x₂ = zeroᵣ x₁ x₂
®-redʳ′ (ℕᵣ x) (sucᵣ x₁ v⇒suc t®v) v⇒v′ with red*Det v⇒suc (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite suc-noRed x₂ = sucᵣ x₁ T.refl t®v
... | inj₂ x₂ = sucᵣ x₁ x₂ t®v
®-redʳ′ (Unitᵣ x) (starᵣ x₁ v⇒star) v⇒v′ with red*Det v⇒star (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite star-noRed x₂ = starᵣ x₁ T.refl
... | inj₂ x₂ = starᵣ x₁ x₂
®-redʳ′ (ne′ K D neK K≡K) t®v v⇒v′ = ⊥-elim (noClosedNe neK)
®-redʳ′ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [a] =
  let t®v = t®v′ [a]
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  ®-redʳ′ ([G] id ε [a]) t®v v∘w⇒v′∘w
®-redʳ′ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [a] a®w =
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  ®-redʳ′ ([G] id ε [a]) t®v v∘w⇒v′∘w
®-redʳ′ (Bᵣ′ (BΣ p) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
        (t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒w , t®v′) v⇒v′ =
    let v₁⇒v′₁ = T.fst-subst v⇒v′
        v₂⇒v′₂ = T.snd-subst v⇒v′
        v′⇒w = cases (red*Det (trans v⇒v′ T.refl) v⇒w)
                     (λ x → x)
                     (λ x → PE.subst (T._⇒* (T.prod v₁ v₂))
                                     (PE.sym (prod-noRed x)) T.refl)
    in  t₁ , t₂ , v₁ , v₂ , t⇒t′ , v′⇒w , t®v′
®-redʳ′ (emb 0<1 [A]) t®v v⇒v′ = ®-redʳ′ [A] t®v v⇒v′


-- Logical relation for erasure is preserved under reduction closure on the left
-- If t ® v ∷ A and v ⇒* v′ then t ® v′ ∷ A

®-red*ʳ′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
         → v T.⇒* v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
®-red*ʳ′ [A] t®v refl = t®v
®-red*ʳ′ [A] t®v (trans x v⇒v′) = ®-red*ʳ′ [A] (®-redʳ′ [A] t®v x) v⇒v′


-- Logical relation for erasure is preserved under reduction closure
-- If t ® v ∷ A and ε ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t′ ® v′ ∷ A

®-red*′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
       → ε ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
®-red*′ [A] t®v t⇒t′ v⇒v′ = ®-red*ʳ′ [A] (®-red*ˡ′ [A] t®v t⇒t′) v⇒v′
