import SymbolicEquivalence.Ere.NormalForm.SmartOps
import SymbolicEquivalence.Ere.Similarity

/-!
# Normalisation

`normalise r` builds the normal form of `r` with the smart constructors. Similar expressions
get the same normal form (`normalise_correctness`), but not the other way round, because the
smart constructors simplify more than `≅` allows.
-/
open scoped Ere

variable {α : Type*} [Bot α] [DecidableEq α]
open EreNorm

namespace EreNorm

def normalise (r : Ere α) : EreNorm α :=
  match r with
  | .ε      => ε
  | .pred p => pred p
  | l ⋓ r   => (normalise l) ⋓' (normalise r)
  | l ⋒ r   => mkInter (normalise l) (normalise r)
  | l ⬝ r   => mkCat (normalise l) (normalise r)
  | r★     => (normalise r)★ₙ
  | ~ r     => ~ₙ (normalise r)
  | .xor l r => .xor (normalise l) (normalise r)

theorem wellFormed_of_normalise (r : Ere α) : WellFormed (normalise r) :=
  match r with
  | .ε => .ε
  | .pred p => .pred p
  | l ⋓ r => wellFormed_mkUnion (wellFormed_of_normalise l) (wellFormed_of_normalise r)
  | l ⋒ r =>
    wellFormed_mkInter (wellFormed_of_normalise l) (wellFormed_of_normalise r)
  | l ⬝ r =>
    wellFormed_mkCat (wellFormed_of_normalise l) (wellFormed_of_normalise r)
  | r★ => .star (wellFormed_of_normalise r)
  | ~ r => .negation (wellFormed_of_normalise r)
  | .xor l r => .xor (wellFormed_of_normalise l) (wellFormed_of_normalise r)

/-- `normalise` maps similar expressions to the same normal form. -/
theorem normalise_correctness {a b : Ere α} (h : a ≅ b) :
    normalise a = normalise b := by
  induction h with
  | assoc =>
    simp only [normalise]
    rw [mkUnion_assoc (wellFormed_of_normalise _) (wellFormed_of_normalise _)]
  | dedup =>
    simp only [normalise]
    conv => rhs; rw [← mkUnion_dedup (wellFormed_of_normalise _) (wellFormed_of_normalise _)]
    rw [mkUnion_assoc (wellFormed_of_normalise _) (wellFormed_of_normalise _)]
  | idem => simp only [normalise]; exact mkUnion_idem (wellFormed_of_normalise _)
  | _ => simp_all [normalise]

/-! ### The image of `normalise`

`IsNormal s` says that `s` is an output of `normalise`, which is what the states of the ERE
checker are. Every output of `normalise` is well-formed (`IsNormal.wellFormed`), but not the
other way round. For example, `ε ⬝ₙ pred p` is well-formed, but `normalise` never produces it
because `mkCat` drops the `ε`. -/

/-- `s` is an output of `normalise`. -/
def IsNormal (s : EreNorm α) : Prop := ∃ e : Ere α, normalise e = s

@[simp] theorem isNormal_normalise (e : Ere α) : IsNormal (normalise e) := ⟨e, rfl⟩

/-- An output of `normalise` is well-formed. -/
theorem IsNormal.wellFormed {s : EreNorm α} (h : IsNormal s) : WellFormed s := by
  obtain ⟨e, rfl⟩ := h
  exact wellFormed_of_normalise e

end EreNorm
