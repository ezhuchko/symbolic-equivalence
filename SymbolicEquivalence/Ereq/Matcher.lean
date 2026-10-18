import SymbolicEquivalence.Ereq.Derivative

/-!
# Matching `Ereq`

`derives` matches a word against an expression by taking derivatives of its atomic form
`Ereq.nnf`. `derives_iff_matches` proves it correct, which makes `⊫` decidable. -/

namespace Ereq

open SymbolicDerivativeSystem

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ] [DecidableSat α]

/-- The matcher, which derives along the word and then tests nullability. -/
def derives (w : Word σ n) (R : Ereq α n) : Bool := (EreqAtomic.rawSystem α σ n).accepts R.nnf w

scoped infix:40 " ⊢ " => derives

/-- The matcher is correct. -/
theorem derives_iff_matches (w : Word σ n) (R : Ereq α n) : w ⊢ R ↔ w ⊫ R :=
  ((EreqAtomic.rawSystem α σ n).accepts_iff trivial w).trans (Ereq.matches_nnf R)

instance (w : Word σ n) (R : Ereq α n) : Decidable (w ⊫ R) :=
  decidable_of_iff _ (derives_iff_matches w R)

end Ereq
