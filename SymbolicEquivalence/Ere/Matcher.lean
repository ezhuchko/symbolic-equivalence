import SymbolicEquivalence.Ere.Derivative

/-!
# Matching `Ere`

`derives` matches a word against an expression by taking derivatives. `derives_iff_matches`
proves it correct, which makes `⊫` decidable. -/

namespace Ere

open SymbolicDerivativeSystem

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

/-- The matcher, which derives along the word and then tests nullability. -/
def derives (w : List σ) (R : Ere α) : Bool := (rawSystem α σ).accepts R w

scoped infix:40 " ⊢ " => derives

/-- The matcher is correct. -/
theorem derives_iff_matches (w : List σ) (R : Ere α) : w ⊢ R ↔ w ⊫ R :=
  (rawSystem α σ).accepts_iff trivial w

instance (w : List σ) (R : Ere α) : Decidable (w ⊫ R) :=
  decidable_of_iff _ (derives_iff_matches w R)

end Ere
