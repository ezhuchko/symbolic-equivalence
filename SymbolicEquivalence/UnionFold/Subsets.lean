import SymbolicEquivalence.UnionFold.Fold
import SymbolicEquivalence.NeSubsets
import SymbolicEquivalence.UpTo

/-!
# Folds of all non-empty sub-multisets

`(neSubsets xs).map (fold union bot)` folds every non-empty sub-multiset of `xs`, in every
order. This finite list contains, up to `Sim`, every fold of operands similar to elements of
`xs` (`fold_mem_map_neSubsets`). Every order is needed because `Sim` cannot reorder operands.
-/

open List
open scoped UpTo

namespace UnionFold

variable {E : Type _} {union : E → E → E} {Sim : E → E → Prop} [i : UnionSim union Sim]

/-- Replacing each operand by a similar element of `ys` keeps a fold similar. -/
private theorem exists_fold_sim_subset (bot : E) {xs ys : List E} (ne : xs ≠ [])
    (h : xs ⊆[ Sim ] ys) :
    ∃ us : List E, us ⊆ ys ∧ us ≠ [] ∧ Sim (fold union bot xs) (fold union bot us) := by
  match xs with
  | [x] =>
    obtain ⟨y, hy, hxy⟩ := h x (by simp)
    exact ⟨[y], by simpa using hy, cons_ne_nil y [], hxy⟩
  | x :: x' :: xs =>
    obtain ⟨y, hy, hxy⟩ := h x (by simp)
    obtain ⟨us, sb, hus, eq⟩ :=
      exists_fold_sim_subset bot (cons_ne_nil x' xs) fun z hz => h z (mem_cons_of_mem x hz)
    exact ⟨y :: us, cons_subset.mpr ⟨hy, sb⟩, cons_ne_nil y us,
      fold_cons_cong bot (cons_ne_nil x' xs) hus hxy eq⟩

/-- Removing duplicate operands keeps a fold similar. -/
private theorem nodup_equiv (bot : E) (xs : List E) (ne : xs ≠ []) :
    ∃ zs : List E, Nodup zs ∧ zs ≠ [] ∧ zs ⊆ xs ∧ Sim (fold union bot xs) (fold union bot zs) := by
  -- `smartDedup` needs `BEq E`, we use classical instead of adding `[DecidableEq E]`
  classical
  refine ⟨smartDedup xs, smartDedup_nodup, smartDedup_ne_nil ne,
    fun x hx => (mem_smartDedup_iff x xs).mp hx, i.symm ?_⟩
  simpa using fold_map_smartDedup (Sim := Sim) bot id xs

/-- Replacing each operand by a similar element of `ys` and then removing duplicates keeps a
fold similar. -/
theorem exists_fold_sim_nodup (bot : E) {xs ys : List E} (ne : xs ≠ []) (h : xs ⊆[ Sim ] ys) :
    ∃ us : List E, Nodup us ∧ us ≠ [] ∧ us ⊆ ys ∧ Sim (fold union bot xs) (fold union bot us) :=
  have ⟨xs', xs'_ys, xs'_ne, xs_xs'⟩ := exists_fold_sim_subset bot ne h
  have ⟨us, nd, us_xs', p, xs'_us⟩ := nodup_equiv bot xs' xs'_ne
  ⟨us, nd, us_xs', List.Subset.trans p xs'_ys, i.trans xs_xs' xs'_us⟩

/-- `(neSubsets ys).map (fold union bot)` contains, up to `Sim`, every fold of operands
similar to elements of `ys`. -/
theorem fold_mem_map_neSubsets (bot : E) {xs ys : List E} (ne : xs ≠ []) (h : xs ⊆[ Sim ] ys) :
    fold union bot xs ∈[ Sim ] (neSubsets ys).map (fold union bot) :=
  have ⟨us, ndup, ne, us_ys, hfold⟩ := exists_fold_sim_nodup bot ne h
  ⟨fold union bot us, mem_map_of_mem (mem_neSubsets_of_nodup ne us_ys ndup), hfold⟩

/-- Every element of `(neSubsets xs).map (fold union bot)` is the fold of a non-empty list
whose elements are all in `xs`. -/
theorem exists_of_mem_map_neSubsets (bot : E) {x : E} {xs : List E}
    (h : x ∈ (neSubsets xs).map (fold union bot)) :
    ∃ zs, zs ≠ [] ∧ x = fold union bot zs ∧ zs ⊆ xs :=
  have ⟨zs, zs_mem, zs_eq⟩ := mem_map.mp h
  ⟨zs, ne_nil_of_mem_neSubsets zs_mem, zs_eq.symm, subset_of_mem_neSubsets zs_mem⟩

/-- Folding all non-empty sub-multisets is monotone with respect to `⊆[ Sim ]`. -/
theorem map_neSubsets_mono (bot : E) {xs ys : List E} (h : xs ⊆[ Sim ] ys) :
    (neSubsets xs).map (fold union bot) ⊆[ Sim ] (neSubsets ys).map (fold union bot) :=
  fun x x_mem => by
  obtain ⟨zs, p1, rfl, p3⟩ := exists_of_mem_map_neSubsets bot x_mem
  have zsxs : zs ⊆[ Sim ] xs := subset_to_subsetUpTo ⟨fun _ => i.refl⟩ p3
  exact fold_mem_map_neSubsets bot p1 (subsetUpTo_trans ⟨i.trans⟩ zsxs h)

end UnionFold
