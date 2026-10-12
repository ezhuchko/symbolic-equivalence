import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm

/-!
# Non-empty sub-multisets

`neSubsets ys` lists every non-empty sub-multiset of `ys`, in every order. -/

open List

variable {α : Type _}

/-- Every non-empty list obtained from `ys` by dropping and reordering elements. -/
def neSubsets (ys : List α) : List (List α) :=
  (ys.sublists.flatMap permutations').filter fun xs => !xs.isEmpty

/-- `xs` is in `neSubsets ys` exactly when `xs` is non-empty and a subperm of `ys`. -/
@[simp]
theorem mem_neSubsets {xs ys : List α} : xs ∈ neSubsets ys ↔ xs ≠ [] ∧ xs <+~ ys := by
  simp only [neSubsets, mem_filter, mem_flatMap, mem_sublists, mem_permutations']
  constructor
  · rintro ⟨⟨zs, hzs, hp⟩, hne⟩
    exact ⟨by simpa using hne, zs, hp.symm, hzs⟩
  · rintro ⟨hne, zs, hp, hzs⟩
    exact ⟨⟨zs, hzs, hp.symm⟩, by simpa using hne⟩

theorem ne_nil_of_mem_neSubsets {xs ys : List α} (h : xs ∈ neSubsets ys) : xs ≠ [] :=
  (mem_neSubsets.mp h).1

private theorem subperm_of_mem_neSubsets {xs ys : List α} (h : xs ∈ neSubsets ys) : xs <+~ ys :=
  (mem_neSubsets.mp h).2

theorem neSubsets_refl {xs : List α} (ne : xs ≠ []) : xs ∈ neSubsets xs :=
  mem_neSubsets.mpr ⟨ne, Subperm.refl xs⟩

theorem neSubsets_append {x y xs ys : List α} (hl : x ∈ neSubsets xs) (hr : y ∈ neSubsets ys) :
    x ++ y ∈ neSubsets (xs ++ ys) :=
  mem_neSubsets.mpr ⟨append_ne_nil_of_left_ne_nil (ne_nil_of_mem_neSubsets hl) _,
    (subperm_of_mem_neSubsets hl).append (subperm_of_mem_neSubsets hr)⟩

theorem neSubsets_singleton {x : α} {xs : List α} (h : x ∈ xs) : [x] ∈ neSubsets xs :=
  mem_neSubsets.mpr ⟨cons_ne_nil x [], (singleton_sublist.mpr h).subperm⟩

/-- A non-empty, duplicate-free list whose elements are all in `ys` is in `neSubsets ys`. -/
theorem mem_neSubsets_of_nodup {xs ys : List α}
    (h : xs ≠ []) (sb : xs ⊆ ys) (nd : Nodup xs) : xs ∈ neSubsets ys :=
  mem_neSubsets.mpr ⟨h, nd.subperm sb⟩

theorem subset_of_mem_neSubsets {xs ys : List α} (h : xs ∈ neSubsets ys) : xs ⊆ ys :=
  (subperm_of_mem_neSubsets h).subset
