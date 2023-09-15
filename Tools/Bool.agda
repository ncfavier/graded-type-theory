------------------------------------------------------------------------
-- The booleans
------------------------------------------------------------------------

module Tools.Bool where

open import Data.Bool.Base
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
  public

open import Tools.PropositionalEquality
open import Tools.Nullary

-- The function T is pointwise propositional.

T-propositional : ∀ {b} {x y : T b} → x ≡ y
T-propositional {b = true} = refl

¬T→false : {b : Bool} → ¬ T b → b ≡ false
¬T→false {false} ¬tb = refl
¬T→false {true} ¬tb = ⊥-elim (¬tb _)

false→¬T : {b : Bool} → b ≡ false → ¬ T b
false→¬T {false} refl tb = tb

T→true : {b : Bool} → T b → b ≡ true
T→true {true} tb = refl

true→T : {b : Bool} → b ≡ true → T b
true→T {true} refl = _
