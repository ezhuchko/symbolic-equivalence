import SymbolicEquivalence.Ereq.NormalForm.SmartOps
import SymbolicEquivalence.Ereq.Similarity

/-!
# Normalisation

`normalise r` builds the normal form of `r` with the smart constructors. Similar expressions
get the same normal form (`normalise_correctness`), but not the other way round, since
normalising simplifies more than `≅` allows. The checker applies `Ereq.nnf` before `normalise`.
-/

open scoped EreqAtomic

variable {α : Type*} [Bot α] [DecidableEq α]

namespace EreqNorm

def normalise (r : EreqAtomic α n) : EreqNorm α n :=
  match r with
  | .ε       => ε
  | .pred p  => pred p
  | l ⋓ₐ r   => normalise l ⋓' normalise r
  | l ⋒ₐ r   => mkInter (normalise l) (normalise r)
  | l ⬝ₐ r   => mkCat (normalise l) (normalise r)
  | r★ₐ      => star (normalise r)
  | ~ₐ r     => negation (normalise r)
  | ∃ₐ r     => existential (normalise r)

theorem wellFormed_of_normalise (r : EreqAtomic α n) : WellFormed (normalise r) :=
  match r with
  | .ε => .ε
  | .pred p => .pred p
  | l ⋓ₐ r => wellFormed_mkUnion (wellFormed_of_normalise l) (wellFormed_of_normalise r)
  | l ⋒ₐ r => wellFormed_mkInter (wellFormed_of_normalise l) (wellFormed_of_normalise r)
  | l ⬝ₐ r => wellFormed_mkCat (wellFormed_of_normalise l) (wellFormed_of_normalise r)
  | r★ₐ => .star (wellFormed_of_normalise r)
  | ~ₐ r => .negation (wellFormed_of_normalise r)
  | ∃ₐ r => .existential (wellFormed_of_normalise r)

/-- `normalise` maps similar expressions to the same normal form. -/
theorem normalise_correctness {a b : EreqAtomic α n} (h : a ≅ b) :
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

The states of the checker are the outputs of `normalise`. They are all well-formed, but not
every well-formed expression is normalised. For example, `normalise` never produces `ε ⬝ₙ pred p`,
because `mkCat` drops the `ε`. -/

/-- `s` is an output of `normalise`. -/
def IsNormal (s : EreqNorm α n) : Prop := ∃ e : EreqAtomic α n, normalise e = s

@[simp] theorem isNormal_normalise (e : EreqAtomic α n) : IsNormal (normalise e) := ⟨e, rfl⟩

/-- An output of `normalise` is well-formed. -/
theorem IsNormal.wellFormed {s : EreqNorm α n} (h : IsNormal s) : WellFormed s := by
  obtain ⟨e, rfl⟩ := h
  exact wellFormed_of_normalise e

end EreqNorm
