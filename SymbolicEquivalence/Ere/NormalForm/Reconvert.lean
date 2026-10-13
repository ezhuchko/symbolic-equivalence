import SymbolicEquivalence.Ere.NormalForm.SmartUnion
import SymbolicEquivalence.Ere.UnionOf

/-!
# Converting normal forms back to `Ere`

`reconvert` turns a normal form back into an `Ere`, with each union becoming a `unionOf`.
`reconvert (normalise r)` has the same language as `r` (`EreNorm.lang_normalise`) but is not
always similar (`≅`) to it, because the smart constructors simplify more than `≅` allows.
-/
open Ere (Sim unionOf unionOf_map_append unionOf_map_smartDedup)

open scoped Ere

variable {α : Type*} [Bot α]
open EreNorm

namespace EreNorm

def reconvert : EreNorm α → Ere α
  | ε => .ε
  | pred p => .pred p
  | ⋃ₙ[x, y | zs] => unionOf (reconvert x :: reconvert y :: zs.map reconvert)
  | l ⋒ₙ r => reconvert l ⋒ reconvert r
  | l ⬝ₙ r => reconvert l ⬝ reconvert r
  | r★ₙ    => (reconvert r)★
  | ~ₙ r   => ~ (reconvert r)
  | .xor l r => .xor (reconvert l) (reconvert r)

@[simp] theorem reconvert_ε : reconvert (ε : EreNorm α) = .ε := by rw [reconvert]
@[simp] theorem reconvert_pred (p : α) : reconvert (.pred p) = .pred p := by rw [reconvert]
@[simp] theorem reconvert_union (x y : EreNorm α) (zs) :
  reconvert ⋃ₙ[x, y | zs] = unionOf ((x :: y :: zs).map reconvert) := by
  rw [reconvert]; simp
@[simp] theorem reconvert_inter (l r : EreNorm α) :
  reconvert (l ⋒ₙ r) = (reconvert l ⋒ reconvert r) := by rw [reconvert]
@[simp] theorem reconvert_cat (l r : EreNorm α) :
  reconvert (l ⬝ₙ r) = (reconvert l ⬝ reconvert r) := by rw [reconvert]
@[simp] theorem reconvert_star (r : EreNorm α) :
  reconvert r★ₙ = (reconvert r)★ := by rw [reconvert]
@[simp] theorem reconvert_neg (r : EreNorm α) : reconvert ~ₙr = ~ (reconvert r) := by rw [reconvert]
@[simp] theorem reconvert_xor (l r : EreNorm α) :
  reconvert (.xor l r) = .xor (reconvert l) (reconvert r) := by rw [reconvert]

/-- `reconvert` maps `fromList` to `unionOf`. -/
@[simp] theorem reconvert_fromList (x : EreNorm α) (xs : List (EreNorm α)) :
    reconvert (fromList x xs) = unionOf ((x :: xs).map reconvert) := by
  cases xs <;> simp

/-- Folding the reconverted operands of `r` with `unionOf` gives back `reconvert r`. -/
@[simp] theorem reconvert_toList (r : EreNorm α) :
    unionOf ((toList r).map reconvert) = reconvert r := by
  rw [toList, ← reconvert_fromList, fromList_toList]

variable [DecidableEq α]

/-- If neither operand is `⊥`, `mkUnion` only reassociates and deletes repeated operands, so
    the result is `≅` to the plain union. -/
theorem reconvert_mkUnion_of_ne_bot {a b : EreNorm α}
    (hna : a ≠ pred ⊥) (hnb : b ≠ pred ⊥) :
    reconvert (a ⋓' b) ≅ (reconvert a ⋓ reconvert b) := by
  have h1 : reconvert (a ⋓' b) = unionOf ((smartDedup (toList a ++ toList b)).map reconvert) := by
    simp only [mkUnion_of_ne_bot hna hnb, mkUnionOf, reconvert_fromList,
      ← smartDedup_cons, toList_append_eq]
  rw [h1]
  refine .trans (unionOf_map_smartDedup reconvert _) ?_
  refine .trans
    (unionOf_map_append reconvert (toList_ne_nil a) (toList_ne_nil b)) ?_
  rw [reconvert_toList, reconvert_toList]
  exact .refl

end EreNorm
