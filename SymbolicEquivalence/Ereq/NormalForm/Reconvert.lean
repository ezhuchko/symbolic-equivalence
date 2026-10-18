import SymbolicEquivalence.Ereq.NormalForm.SmartUnion
import SymbolicEquivalence.Ereq.UnionOf

/-!
# Converting normal forms back to `EreqAtomic`

`reconvert` turns a normal form back into an `EreqAtomic`. The result of `reconvert (normalise r)`
has the same language as `r`, but may not be similar (`≅`) to it, since normalising simplifies
more than `≅` allows.
-/

open scoped EreqAtomic
open EreqAtomic (Sim unionOf unionOf_map_append unionOf_map_smartDedup)

variable {α : Type*} [Bot α]

namespace EreqNorm

mutual
  def reconvert : EreqNorm α n → EreqAtomic α n
    | .ε => .ε
    | .pred p => .pred p
    | ⋃ₙ[x, y | zs] => unionOf (reconvert x :: reconvert y :: reconvertList zs)
    | l ⋒ₙ r => reconvert l ⋒ₐ reconvert r
    | l ⬝ₙ r => reconvert l ⬝ₐ reconvert r
    | r★ₙ => (reconvert r)★ₐ
    | ~ₙ r => ~ₐ (reconvert r)
    | ∃ₙ r => ∃ₐ (reconvert r)
  termination_by r => sizeOf r

  def reconvertList : EreqNormList α n → List (EreqAtomic α n)
    | .nil => []
    | .cons x xs => reconvert x :: reconvertList xs
  termination_by xs => sizeOf xs
end

@[simp] theorem reconvert_ε : reconvert (ε : EreqNorm α n) = .ε := by rw [reconvert]
@[simp] theorem reconvert_pred (p : FundamentalPredicate α n) :
    reconvert (.pred p) = .pred p := by rw [reconvert]
@[simp] theorem reconvert_bot :
    reconvert (bot : EreqNorm α n) = (EreqAtomic.bot : EreqAtomic α n) := by
  rw [bot, reconvert_pred]
@[simp] theorem reconvert_inter (l r : EreqNorm α n) :
    reconvert (l ⋒ₙ r) = (reconvert l ⋒ₐ reconvert r) := by rw [reconvert]
@[simp] theorem reconvert_cat (l r : EreqNorm α n) :
    reconvert (l ⬝ₙ r) = (reconvert l ⬝ₐ reconvert r) := by rw [reconvert]
@[simp] theorem reconvert_star (r : EreqNorm α n) :
    reconvert r★ₙ = (reconvert r)★ₐ := by rw [reconvert]
@[simp] theorem reconvert_neg (r : EreqNorm α n) : reconvert ~ₙr = ~ₐ (reconvert r) := by
  rw [reconvert]
@[simp] theorem reconvert_ex (r : EreqNorm α (n + 1)) : reconvert (∃ₙ r) = ∃ₐ (reconvert r) := by
  rw [reconvert]

@[simp]
theorem reconvertList_eq_toList_map (xs : EreqNormList α n) :
    reconvertList xs = xs.toList.map reconvert := by
  match xs with
  | .nil => simp [reconvertList]
  | .cons x xs => simp [reconvertList, reconvertList_eq_toList_map xs]

@[simp] theorem reconvert_union (x y : EreqNorm α n) (zs : EreqNormList α n) :
    reconvert ⋃ₙ[x, y | zs] = unionOf ((x :: y :: zs.toList).map reconvert) := by
  rw [reconvert]; simp

/-- `reconvert` maps `fromList` to `unionOf`. -/
@[simp] theorem reconvert_fromList (x : EreqNorm α n) (xs : List (EreqNorm α n)) :
    reconvert (fromList x xs) = unionOf ((x :: xs).map reconvert) := by
  cases xs <;> simp

/-- Folding the reconverted operands of `r` with `unionOf` gives back `reconvert r`. -/
@[simp] theorem reconvert_toList (r : EreqNorm α n) :
    unionOf ((toList r).map reconvert) = reconvert r := by
  rw [toList, ← reconvert_fromList, fromList_toList]

variable [DecidableEq α]

/-- If neither operand is `bot`, `mkUnion` only reassociates and deletes repeated operands, so
    the result is `≅` to the plain union. -/
theorem reconvert_mkUnion_of_ne_bot {a b : EreqNorm α n}
    (hna : a ≠ bot) (hnb : b ≠ bot) :
    reconvert (a ⋓' b) ≅ (reconvert a ⋓ₐ reconvert b) := by
  have h1 : reconvert (a ⋓' b) = unionOf ((smartDedup (toList a ++ toList b)).map reconvert) := by
    simp only [mkUnion_of_ne_bot hna hnb, mkUnionOf, reconvert_fromList,
      ← smartDedup_cons, toList_append_eq]
  rw [h1]
  refine Sim.trans (unionOf_map_smartDedup reconvert _) ?_
  refine Sim.trans (unionOf_map_append reconvert (toList_ne_nil a) (toList_ne_nil b)) ?_
  rw [reconvert_toList, reconvert_toList]
  exact Sim.refl

end EreqNorm
