------------------------------------------------------------------------
-- ShapeView: A view for constructor equality for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.ShapeView
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Properties.Reflexivity R

open import Tools.Function
open import Tools.Level hiding (Level)
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B C K t u : Term n
    p q : M
    s : Strength
    l l′ l″ l₁ l₁′ l₂ l₂′ l₃ l₃′ : Universe-level

-- Views for reducible types

data LevelView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  Levelᵣ : ∀ LevelA → LevelView (Levelᵣ LevelA)

Level-elim′ : Γ ⊢ A ⇒* Level → (⊩A : Γ ⊩⟨ l ⟩ A) → LevelView ⊩A
Level-elim′ D (Levelᵣ D′) = Levelᵣ D′
Level-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , Levelₙ) (D' , Uₙ)
... | ()
Level-elim′ D (ℕᵣ D′) with whrDet* (D , Levelₙ) (D′ , ℕₙ)
... | ()
Level-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Level≢ne neK (whrDet* (D , Levelₙ) (D′ , ne neK)))
Level-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (Level≢B W (whrDet* (D , Levelₙ) (D′ , ⟦ W ⟧ₙ)))
Level-elim′ D (Emptyᵣ D′) with whrDet* (D , Levelₙ) (D′ , Emptyₙ)
... | ()
Level-elim′ D (Unitᵣ′ _ _ _ D′ _) with whrDet* (D , Levelₙ) (D′ , Unitₙ)
... | ()
Level-elim′ A⇒*Level (Idᵣ ⊩A) =
  case whrDet* (A⇒*Level , Levelₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()

Level-elim : (⊩A : Γ ⊩⟨ l ⟩ Level) → LevelView ⊩A
Level-elim [Level] = Level-elim′ (id (escape [Level])) [Level]

data UView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  Uᵣ : ∀ UA → UView (Uᵣ UA)

U-elim′ : Γ ⊢ A ⇒* U t → (⊩A : Γ ⊩⟨ l ⟩ A) → UView ⊩A
U-elim′ A⇒U (Levelᵣ D) with whrDet* (A⇒U , Uₙ) (D , Levelₙ)
... | ()
U-elim′ _ (Uᵣ ⊩U) = Uᵣ ⊩U
U-elim′ A⇒U (ℕᵣ D) with whrDet* (A⇒U , Uₙ) (D , ℕₙ)
... | ()
U-elim′ A⇒U (Emptyᵣ D) with whrDet* (A⇒U , Uₙ) (D , Emptyₙ)
... | ()
U-elim′ A⇒U (Unitᵣ′ _ _ _ D _) with whrDet* (A⇒U , Uₙ) (D , Unitₙ)
... | ()
U-elim′ A⇒U (ne′ _ D neK K≡K) =
  ⊥-elim (U≢ne neK (whrDet* (A⇒U , Uₙ) (D , ne neK)))
U-elim′ A⇒U (Bᵣ′ W _ _ D _ _ _ _ _) =
  ⊥-elim (U≢B W (whrDet* (A⇒U , Uₙ) (D , ⟦ W ⟧ₙ)))
U-elim′ A⇒U (Idᵣ ⊩A) =
  case whrDet* (A⇒U , Uₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()

U-elim : (⊩A : Γ ⊩⟨ l ⟩ U t) → UView ⊩A
U-elim ⊩U = U-elim′ (id (escape ⊩U)) ⊩U

data ℕView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  ℕᵣ : ∀ ℕA → ℕView (ℕᵣ ℕA)

ℕ-elim′ : Γ ⊢ A ⇒* ℕ → (⊩A : Γ ⊩⟨ l ⟩ A) → ℕView ⊩A
ℕ-elim′ D (Levelᵣ D′) with whrDet* (D , ℕₙ) (D′ , Levelₙ)
... | ()
ℕ-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , ℕₙ) (D' , Uₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = ℕᵣ D′
ℕ-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (D′ , Emptyₙ)
... | ()
ℕ-elim′ D (Unitᵣ′ _ _ _ D′ _) with whrDet* (D , ℕₙ) (D′ , Unitₙ)
... | ()
ℕ-elim′ A⇒*Nat (Idᵣ ⊩A) =
  case whrDet* (A⇒*Nat , ℕₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()

ℕ-elim : (⊩A : Γ ⊩⟨ l ⟩ ℕ) → ℕView ⊩A
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

data EmptyView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  Emptyᵣ : ∀ EmptyA → EmptyView (Emptyᵣ EmptyA)

Empty-elim′ : Γ ⊢ A ⇒* Empty → (⊩A : Γ ⊩⟨ l ⟩ A) → EmptyView ⊩A
Empty-elim′ D (Levelᵣ D′) with whrDet* (D , Emptyₙ) (D′ , Levelₙ)
... | ()
Empty-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , Emptyₙ) (D' , Uₙ)
... | ()
Empty-elim′ D (Emptyᵣ D′) = Emptyᵣ D′
Empty-elim′ D (Unitᵣ′ _ _ _ D′ _)
  with whrDet* (D , Emptyₙ) (D′ , Unitₙ)
... | ()
Empty-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (D′ , ne neK)))
Empty-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (D′ , ⟦ W ⟧ₙ)))
Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (D′ , ℕₙ)
... | ()
Empty-elim′ A⇒*Empty (Idᵣ ⊩A) =
  case whrDet* (A⇒*Empty , Emptyₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()

Empty-elim : (⊩A : Γ ⊩⟨ l ⟩ Empty) → EmptyView ⊩A
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

data UnitView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  Unitᵣ : ∀ {s} (UnitA : Γ ⊩Unit⟨ l , s ⟩ A) → UnitView (Unitᵣ UnitA)

Unit-elim′ : Γ ⊢ A ⇒* Unit s t → (⊩A : Γ ⊩⟨ l ⟩ A) → UnitView ⊩A
Unit-elim′ D (Levelᵣ D′) with whrDet* (D , Unitₙ) (D′ , Levelₙ)
... | ()
Unit-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , Unitₙ) (D' , Uₙ)
... | ()
Unit-elim′ D (Unitᵣ [A]@(Unitᵣ _ _ _ D′ _))
  with whrDet* (D′ , Unitₙ) (D , Unitₙ)
... | PE.refl = Unitᵣ [A]
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (D′ , ne neK)))
Unit-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (D′ , ⟦ W ⟧ₙ)))
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (D′ , ℕₙ)
... | ()
Unit-elim′ A⇒*Unit (Idᵣ ⊩A) =
  case whrDet* (A⇒*Unit , Unitₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()

Unit-elim : (⊩A : Γ ⊩⟨ l ⟩ Unit s t) → UnitView ⊩A
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

data NeutralView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  ne : ∀ neA → NeutralView (ne neA)

ne-elim′ : Γ ⊢ A ⇒* K → Neutral K → (⊩A : Γ ⊩⟨ l ⟩ A) → NeutralView ⊩A
ne-elim′ D neK (Levelᵣ D′) =
  ⊥-elim (Level≢ne neK (whrDet* (D′ , Levelₙ) (D , ne neK)))
ne-elim′ D neK (Uᵣ′ _ _ _ D') =
  ⊥-elim (U≢ne neK (whrDet* (D' , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ′ _ _ _ D′ _) =
  ⊥-elim (Unit≢ne neK (whrDet* (D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne [A]) = ne [A]
ne-elim′ D neK (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ A⇒*ne n (Idᵣ ⊩A) =
  ⊥-elim (Id≢ne n (whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (A⇒*ne , ne n)))

ne-elim : Neutral K  → (⊩K : Γ ⊩⟨ l ⟩ K) → NeutralView ⊩K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

data BView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  Bᵣ : ∀ W BA → BView (Bᵣ W BA)

B-elim′ : ∀ {A F G} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → (⊩A : Γ ⊩⟨ l ⟩ A) → BView ⊩A
B-elim′ W D (Levelᵣ D') = ⊥-elim (Level≢B W (whrDet* (D' , Levelₙ) (D ,  ⟦ W ⟧ₙ)))
B-elim′ W D (Uᵣ′ _ _ _ D') = ⊥-elim (U≢B W (whrDet* (D' , Uₙ) (D ,  ⟦ W ⟧ₙ)))
B-elim′ W D (ℕᵣ D′) =
  ⊥-elim (ℕ≢B W (whrDet* (D′ , ℕₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Emptyᵣ D′) =
  ⊥-elim (Empty≢B W (whrDet* (D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Unitᵣ′ _ _ _ D′ _) =
  ⊥-elim (Unit≢B W (whrDet* (D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ne′ _ D′ neK K≡K) =
  ⊥-elim (B≢ne W neK (whrDet* (D , ⟦ W ⟧ₙ) (D′ , ne neK)))
B-elim′ BΠ! D (Bᵣ′ BΣ! _ _ D′ _ _ _ _ _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
B-elim′ BΣ! D (Bᵣ′ BΠ! _ _ D′ _ _ _ _ _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
B-elim′ BΠ! D (Bᵣ′ BΠ! F G D′ A≡A [F] [G] G-ext ok)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵣ BΠ! (Bᵣ F G D′ A≡A [F] [G] G-ext ok)
B-elim′ BΣ! D (Bᵣ′ BΣ! F G D′ A≡A [F] [G] G-ext ok)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵣ BΣ! (Bᵣ F G D′ A≡A [F] [G] G-ext ok)
B-elim′ _ A⇒*B (Idᵣ ⊩A) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (A⇒*B , ⟦ _ ⟧ₙ)

B-elim : ∀ {F G} W → (⊩A : Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G) → BView ⊩A
B-elim W [Π] = B-elim′ W (id (escape [Π])) [Π]

data IdView {Γ : Con Term n} {l A} : (p : Γ ⊩⟨ l ⟩ A) → Set a where
  Idᵣ : ∀ IdA → IdView (Idᵣ IdA)

Id-elim′ : Γ ⊢ A ⇒* Id B t u → (⊩A : Γ ⊩⟨ l ⟩ A) → IdView ⊩A
Id-elim′ ⇒*Id (Levelᵣ D') with whrDet* (⇒*Id , Idₙ) (D' , Levelₙ)
... | ()
Id-elim′ ⇒*Id (Uᵣ′ _ _ _ D') with whrDet* (⇒*Id , Idₙ) (D' , Uₙ)
... | ()
Id-elim′ ⇒*Id (ℕᵣ ⇒*ℕ) =
  case whrDet* (⇒*ℕ , ℕₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Emptyᵣ ⇒*Empty) =
  case whrDet* (⇒*Empty , Emptyₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Unitᵣ ⊩Unit) =
  case whrDet* (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩Unit , Unitₙ) (⇒*Id , Idₙ)
  of λ ()
Id-elim′ ⇒*Id (ne′ _ ⇒*ne n _) =
  ⊥-elim (Id≢ne n (whrDet* (⇒*Id , Idₙ) (⇒*ne , ne n)))
Id-elim′ ⇒*Id (Bᵣ′ _ _ _ ⇒*B _ _ _ _ _) =
  ⊥-elim (Id≢⟦⟧▷ _ (whrDet* (⇒*Id , Idₙ) (⇒*B , ⟦ _ ⟧ₙ)))
Id-elim′ _ (Idᵣ ⊩A) = Idᵣ ⊩A

opaque

  Id-elim : (⊩A : Γ ⊩⟨ l ⟩ Id A t u) → IdView ⊩A
  Id-elim ⊩Id = Id-elim′ (id (escape ⊩Id)) ⊩Id

-- A view for constructor equality of types
data ShapeView (Γ : Con Term n) : ∀ l l′ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B) → Set a where
  Levelᵥ : ∀ {A B l l′} LevelA LevelB → ShapeView Γ l l′ A B (Levelᵣ LevelA) (Levelᵣ LevelB)
  Uᵥ : ∀ {A B l l′} UA UB → ShapeView Γ l l′ A B (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  Unitᵥ : ∀ {A B l l′ s} UnitA UnitB → ShapeView Γ l l′ A B (Unitᵣ {s = s} UnitA) (Unitᵣ {s = s} UnitB)
  ne  : ∀ {A B l l′} neA neB
      → ShapeView Γ l l′ A B (ne neA) (ne neB)
  Bᵥ : ∀ {A B l l′} W BA BB
    → ShapeView Γ l l′ A B (Bᵣ W BA) (Bᵣ W BB)
  Idᵥ : ∀ ⊩A ⊩B → ShapeView Γ l l′ A B (Idᵣ ⊩A) (Idᵣ ⊩B)

-- Construct a shape view from an equality (aptly named)
goodCases : ∀ {l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
-- Diagonal cases
goodCases (Levelᵣ LevelA) (Levelᵣ LevelB) A≡B = Levelᵥ LevelA LevelB
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ UnitB@(Unitᵣ _ _ _ D _)) (Unit₌ _ D′ _)
  with whrDet* (D , Unitₙ) (D′ , Unitₙ)
... | PE.refl = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Bᵣ BΠ! ΠA) (Bᵣ′ BΠ! F G D A≡A [F] [G] G-ext _)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΠ! ΠA (Bᵣ F G D A≡A [F] [G] G-ext _)
goodCases (Bᵣ BΣ! ΣA) (Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext ok)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΣ! ΣA (Bᵣ F G D A≡A [F] [G] G-ext ok)
goodCases (Idᵣ ⊩A) (Idᵣ ⊩B) _ = Idᵥ ⊩A ⊩B

-- Refutable cases
-- Level ≡ _
goodCases (Levelᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , Levelₙ) (D' , Uₙ)
... | ()
goodCases (Levelᵣ _) (ℕᵣ D') D with whrDet* (D , Levelₙ) (D' , ℕₙ)
... | ()
goodCases (Levelᵣ _) (Emptyᵣ D') D with whrDet* (D , Levelₙ) (D' , Emptyₙ)
... | ()
goodCases (Levelᵣ _) (Unitᵣ′ _ _ _ D' _) D with whrDet* (D , Levelₙ) (D' , Unitₙ)
... | ()
goodCases (Levelᵣ _) (ne′ _ D' neK K≡K) D =
  ⊥-elim (Level≢ne neK (whrDet* ( D , Levelₙ ) ( D' , ne neK)))
goodCases (Levelᵣ _) (Bᵣ′ W _ _ D' _ _ _ _ _) D =
  ⊥-elim (Level≢B W (whrDet* ( D , Levelₙ ) (D' , ⟦ W ⟧ₙ )))
goodCases (Levelᵣ _) (Idᵣ ⊩B) D =
  case whrDet* (D , Levelₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- U ≡ _
goodCases (Uᵣ _) (Levelᵣ D') (U₌ _ D _) with whrDet* (D , Uₙ) (D' , Levelₙ)
... | ()
goodCases (Uᵣ _) (ℕᵣ D') (U₌ _ D _) with whrDet* (D , Uₙ) (D' , ℕₙ)
... | ()
goodCases (Uᵣ _) (Emptyᵣ D') (U₌ _ D _) with whrDet* (D , Uₙ) (D' , Emptyₙ)
... | ()
goodCases (Uᵣ _) (Unitᵣ′ _ _ _ D' _) (U₌ _ D _) with whrDet* (D , Uₙ) (D' , Unitₙ)
... | ()
goodCases (Uᵣ′ _ _ _ ⊢Γ) (ne′ _ D' neK K≡K) (U₌ _ D _) =
  ⊥-elim (U≢ne neK (whrDet* ( D , Uₙ ) (D' , ne neK)))
goodCases (Uᵣ′ _ _ _ _) (Bᵣ′ W _ _ D' _ _ _ _ _) (U₌ _ D _) =
  ⊥-elim (U≢B W (whrDet* ( D , Uₙ ) (D' , ⟦ W ⟧ₙ )))
goodCases (Uᵣ _) (Idᵣ ⊩B) (U₌ _ D _) =
  case whrDet* (D , Uₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- ℕ ≡ _
goodCases (ℕᵣ _) (Levelᵣ D') D with whrDet* (D , ℕₙ) (D' , Levelₙ)
... | ()
goodCases (ℕᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , ℕₙ) (D' , Uₙ)
... | ()
goodCases (ℕᵣ _) (Emptyᵣ D') D with whrDet* (D , ℕₙ) (D' , Emptyₙ)
... | ()
goodCases (ℕᵣ x) (Unitᵣ′ _ _ _ D' _) D
  with whrDet* (D , ℕₙ) (D' , Unitₙ)
... | ()
goodCases (ℕᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (D₁ , ne neK)))
goodCases (ℕᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _) A≡B =
  ⊥-elim (ℕ≢B W (whrDet* (A≡B , ℕₙ) (D , ⟦ W ⟧ₙ)))
goodCases (ℕᵣ _) (Idᵣ ⊩B) ⇒*ℕ =
  case whrDet* (⇒*ℕ , ℕₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- Empty ≢ _
goodCases (Emptyᵣ _) (Levelᵣ D') D with whrDet* (D , Emptyₙ) (D' , Levelₙ)
... | ()
goodCases (Emptyᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , Emptyₙ) (D' , Uₙ)
... | ()
goodCases (Emptyᵣ _) (Unitᵣ′ _ _ _ D' _) D
  with whrDet* (D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (D₁ , ne neK)))
goodCases (Emptyᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _) A≡B =
  ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (D , ⟦ W ⟧ₙ)))
goodCases (Emptyᵣ _) (Idᵣ ⊩B) ⇒*Empty =
  case whrDet* (⇒*Empty , Emptyₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- Unit ≡ _
goodCases (Unitᵣ _) (Levelᵣ D') (Unit₌ _ D _) with whrDet* (D , Unitₙ) (D' , Levelₙ)
... | ()
goodCases (Unitᵣ _) (Uᵣ′ _ _ _ D') (Unit₌ _ D _) with whrDet* (D , Unitₙ) (D' , Uₙ)
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') (Unit₌ _ D _) with whrDet* (D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') (Unit₌ _ D _) with whrDet* (D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ne′ _ D' neK K≡K) (Unit₌ _ D _) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (D' , ne neK)))
goodCases (Unitᵣ _) (Bᵣ′ W _ _ D' _ _ _ _ _) (Unit₌ _ D _) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (D' , ⟦ W ⟧ₙ)))
goodCases (Unitᵣ _) (Idᵣ ⊩B) (Unit₌ _ ⇒*Unit _) =
  case whrDet* (⇒*Unit , Unitₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- ne ≡ _
goodCases (ne′ _ D neK K≡K) (Levelᵣ D') (ne₌ M D′ neM K≡M) =
  ⊥-elim (Level≢ne neM (whrDet* (D' , Levelₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Uᵣ′ _ _ _ D') (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (D' , Uₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (D₁ , ℕₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (D₁ , Emptyₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Unitᵣ′ _ _ _ D₁ _) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (D₁ , Unitₙ) (D′ , ne neM)))
goodCases (ne′ _ _ _ _) (Bᵣ′ W _ _ D₁ _ _ _ _ _) (ne₌ _ D₂ neM _) =
  ⊥-elim (B≢ne W neM (whrDet* (D₁ , ⟦ W ⟧ₙ) (D₂ , ne neM)))
goodCases (ne _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neM $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (N.D′ , ne N.neM)
  where
  module N = _⊩ne_≡_/_ A≡B

-- B ≡ _
goodCases (Bᵣ W x) (Levelᵣ D') (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Level≢B W (whrDet* (D' , Levelₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Uᵣ′ _ _ _ D') (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢B W (whrDet* (D' , Uₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ℕᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢B W (whrDet* (D₁ , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Emptyᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢B W (whrDet* (D₁ , Emptyₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases
  (Bᵣ W x) (Unitᵣ′ _ _ _ D₁ _) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Unit≢B W (whrDet* (D₁ , Unitₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ne′ _ D neK K≡K) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (D , ne neK)))
goodCases (Bᵣ′ BΠ! _ _ _ _ _ _ _ _) (Bᵣ′ BΣ! _ _ D₁ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (D₂ , ΠΣₙ) (D₁ , ΠΣₙ)))
goodCases (Bᵣ′ BΣ! _ _ _ _ _ _ _ _) (Bᵣ′ BΠ! _ _ D₁ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (D₁ , ΠΣₙ) (D₂ , ΠΣₙ)))
goodCases (Bᵣ _ _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (_⊩ₗB⟨_⟩_≡_/_.D′ A≡B , ⟦ _ ⟧ₙ)

-- Id ≡ _
goodCases (Idᵣ _) (Levelᵣ D') A≡B =
  case whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (D' , Levelₙ)
  of λ ()
goodCases (Idᵣ _) (Uᵣ′ _ _ _ D') A≡B =
  case whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (D' , Uₙ)
  of λ ()
goodCases (Idᵣ _) (ℕᵣ ⇒*ℕ) A≡B =
  case whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (⇒*ℕ , ℕₙ)
  of λ ()
goodCases (Idᵣ _) (Emptyᵣ ⇒*Empty) A≡B =
  case
    whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (⇒*Empty , Emptyₙ)
  of λ ()
goodCases (Idᵣ _) (Unitᵣ ⊩B) A≡B =
  case
    whrDet*
      (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ)
      (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B , Unitₙ)
  of λ ()
goodCases (Idᵣ _) (ne ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B
goodCases (Idᵣ _) (Bᵣ _ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (_⊩ₗB⟨_⟩_.D ⊩B , ⟦ _ ⟧ₙ)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A′] : Γ ⊩⟨ l′ ⟩ A)
              → ShapeView Γ l l′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ (Γ : Con Term n) : ∀ l l′ l″ A B C
                 (p : Γ ⊩⟨ l  ⟩ A)
                 (q : Γ ⊩⟨ l′ ⟩ B)
                 (r : Γ ⊩⟨ l″ ⟩ C) → Set a where
  Levelᵥ : ∀ {A B C l l′ l″} LevelA LevelB LevelC → ShapeView₃ Γ l l′ l″ A B C (Levelᵣ LevelA) (Levelᵣ LevelB) (Levelᵣ LevelC)
  Uᵥ : ∀ {A B C l l′ l″} UA UB UC → ShapeView₃ Γ l l′ l″ A B C (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  Unitᵥ : ∀ {A B C l l′ l″ s} UnitA UnitB UnitC
    → ShapeView₃ Γ l l′ l″ A B C (Unitᵣ {s = s} UnitA)
                 (Unitᵣ {s = s} UnitB) (Unitᵣ {s = s} UnitC)
  ne  : ∀ {A B C l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C (ne neA) (ne neB) (ne neC)
  Bᵥ : ∀ {A B C l l′ l″} W W′ W″ BA BB BC
    → ShapeView₃ Γ l l′ l″ A B C (Bᵣ W BA) (Bᵣ W′ BB) (Bᵣ W″ BC)
  Idᵥ :
    ∀ ⊩A ⊩B ⊩C → ShapeView₃ Γ l l′ l″ A B C (Idᵣ ⊩A) (Idᵣ ⊩B) (Idᵣ ⊩C)

-- Combines two two-way views into a three-way view
combine : ∀ {l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
-- Diagonal cases
combine (Levelᵥ LevelA₁ LevelB₁) (Levelᵥ LevelA LevelB) = Levelᵥ LevelA₁ LevelB₁ LevelB
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁@(Unitᵣ _ _ _ D _)) (Unitᵥ (Unitᵣ _ _ _ D′ _) UnitB)
  with whrDet* (D , Unitₙ) (D′ , Unitₙ)
... | PE.refl = Unitᵥ UnitA₁ UnitB₁ UnitB
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (Bᵥ BΠ! ΠA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok))
        (Bᵥ BΠ! (Bᵣ _ _ D′ _ _ _ _ _) ΠB)
        with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl =
  Bᵥ BΠ! BΠ! BΠ! ΠA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok) ΠB
combine (Bᵥ BΣ! ΣA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok))
        (Bᵥ BΣ! (Bᵣ _ _ D′ _ _ _ _ _) ΣB)
        with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl =
  Bᵥ BΣ! BΣ! BΣ! ΣA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok) ΣB
combine (Idᵥ ⊩A ⊩B) (Idᵥ _ ⊩C) =
  Idᵥ ⊩A ⊩B ⊩C

-- Refutable cases
-- Level ≡ _
combine (Levelᵥ LevelA LevelB) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (LevelB , Levelₙ) (⇒*U , Uₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (ℕᵥ ℕA ℕB) with whrDet* (LevelB , Levelₙ) (ℕA , ℕₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (Emptyᵥ EA EB) with whrDet* (LevelB , Levelₙ) (EA , Emptyₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (Unitᵥ (Unitᵣ _ _ _ UnA _) UnB) with whrDet* (LevelB , Levelₙ) (UnA , Unitₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Level≢ne neK (whrDet* (LevelB , Levelₙ) (D , ne neK)))
combine (Levelᵥ LevelA LevelB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (Level≢B W (whrDet* (LevelB , Levelₙ) (D , ⟦ W ⟧ₙ)))
combine (Levelᵥ LevelA LevelB) (Idᵥ ⊩B′ _) =
  case whrDet* (LevelB , Levelₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- U ≡ _
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Levelᵥ LevelA LevelB) with whrDet* (⇒*U , Uₙ) (LevelA , Levelₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (ℕᵥ ℕA ℕB) with whrDet* (⇒*U , Uₙ) (ℕA , ℕₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Emptyᵥ EA EB) with whrDet* (⇒*U , Uₙ) (EA , Emptyₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Unitᵥ (Unitᵣ _ _ _ UnA _) UnB) with whrDet* (⇒*U , Uₙ) (UnA , Unitₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whrDet* (⇒*U , Uₙ) (D , ne neK)))
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (U≢B W (whrDet* (⇒*U , Uₙ) (D , ⟦ W ⟧ₙ)))
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Idᵥ ⊩B′ _) =
  case whrDet* (⇒*U , Uₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Levelᵥ LevelA LevelB) with whrDet* (ℕB , ℕₙ)  (LevelA , Levelₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (ℕB , ℕₙ)  (⇒*U , Uₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (ℕB , ℕₙ) (EmptyA , Emptyₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Unitᵥ (Unitᵣ _ _ _ UnA _) UnB)
  with whrDet* (ℕB , ℕₙ) (UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (ℕB , ℕₙ) (D , ne neK)))
combine (ℕᵥ _ ℕB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (ℕ≢B W (whrDet* (ℕB , ℕₙ) (D , ⟦ W ⟧ₙ)))
combine (ℕᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (⊩B , ℕₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Levelᵥ LevelA LevelB) with whrDet* (EmptyB , Emptyₙ)  (LevelA , Levelₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (EmptyB , Emptyₙ)  (⇒*U , Uₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (EmptyB , Emptyₙ) (ℕA , ℕₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ (Unitᵣ _ _ _ UnA _) UnB)
  with whrDet* (EmptyB , Emptyₙ) (UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (EmptyB , Emptyₙ) (D , ne neK)))
combine
  (Emptyᵥ _ EmptyB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (Empty≢B W (whrDet* (EmptyB , Emptyₙ) (D , ⟦ W ⟧ₙ)))
combine (Emptyᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (⊩B , Emptyₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- Unit ≡ _
combine (Unitᵥ UnitA (Unitᵣ _ _ _ UnitB _)) (Levelᵥ LevelA LevelB) with whrDet* (UnitB , Unitₙ)  (LevelA , Levelₙ)
... | ()
combine (Unitᵥ UnitA (Unitᵣ _ _ _ UnitB _)) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (UnitB , Unitₙ)  (⇒*U , Uₙ)
... | ()
combine (Unitᵥ UnitA (Unitᵣ _ _ _ UnitB _)) (ℕᵥ ℕA ℕB)
  with whrDet* (UnitB , Unitₙ) (ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA (Unitᵣ _ _ _ UnitB _)) (Emptyᵥ EmptyA EmptyB)
  with whrDet* (UnitB , Unitₙ) (EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA (Unitᵣ _ _ _ UnitB _)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (UnitB , Unitₙ) (D , ne neK)))
combine (Unitᵥ _ (Unitᵣ _ _ _ UnitB _)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (Unit≢B W (whrDet* (UnitB , Unitₙ) (D , ⟦ W ⟧ₙ)))
combine (Unitᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case
    whrDet* (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B , Unitₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ)
  of λ ()

-- ne ≡ _
combine (ne neA (ne _ D neK K≡K)) (Levelᵥ LevelA LevelB) =
  ⊥-elim (Level≢ne neK (whrDet* (LevelA , Levelₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) =
  ⊥-elim (U≢ne neK (whrDet* (⇒*U , Uₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (ℕA , ℕₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (EmptyA , Emptyₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Unitᵥ (Unitᵣ _ _ _ UnA _) UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (UnA , Unitₙ) (D , ne neK)))
combine (ne _ (ne _ D neK _)) (Bᵥ W (Bᵣ _ _ D′ _ _ _ _ _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (D , ne neK)))
combine (ne _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) (N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B

-- Π/Σ ≡ _
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Levelᵥ LevelA LevelB) =
  ⊥-elim (Level≢B W (whrDet* (LevelA , Levelₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) =
  ⊥-elim (U≢B W (whrDet* (⇒*U , Uₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (ℕᵥ ℕA _) =
  ⊥-elim (ℕ≢B W (whrDet* (ℕA , ℕₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Emptyᵥ EmptyA _) =
  ⊥-elim (Empty≢B W (whrDet* (EmptyA , Emptyₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Unitᵥ (Unitᵣ _ _ _ UnitA _) _) =
  ⊥-elim (Unit≢B W (whrDet* (UnitA , Unitₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D₁ _ _ _ _ _)) (ne (ne _ D neK _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (D₁ , ⟦ W ⟧ₙ) (D , ne neK)))
combine (Bᵥ BΠ! _ (Bᵣ _ _ D _ _ _ _ _)) (Bᵥ BΣ! (Bᵣ _ _ D′ _ _ _ _ _) _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
combine (Bᵥ BΣ! _ (Bᵣ _ _ D _ _ _ _ _)) (Bᵥ BΠ! (Bᵣ _ _ D′ _ _ _ _ _) _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
combine (Bᵥ _ _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) (_⊩ₗB⟨_⟩_.D ⊩B , ⟦ _ ⟧ₙ)

-- Id ≡ _
combine (Idᵥ _ ⊩B) (Levelᵥ LevelA LevelB) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (LevelA , Levelₙ) of λ ()
combine (Idᵥ _ ⊩B) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⇒*U , Uₙ) of λ ()
combine (Idᵥ _ ⊩B) (ℕᵥ ⊩B′ _) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⊩B′ , ℕₙ) of λ ()
combine (Idᵥ _ ⊩B) (Emptyᵥ ⊩B′ _) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⊩B′ , Emptyₙ) of λ ()
combine (Idᵥ _ ⊩B) (Unitᵥ ⊩B′ _) =
  case
    whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B′ , Unitₙ)
  of λ ()
combine (Idᵥ _ ⊩B) (ne ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B′
combine (Idᵥ _ ⊩B) (Bᵥ _ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (_⊩ₗB⟨_⟩_.D ⊩B′ , ⟦ _ ⟧ₙ)
