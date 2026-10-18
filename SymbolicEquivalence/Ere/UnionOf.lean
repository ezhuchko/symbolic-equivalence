import SymbolicEquivalence.UnionFold.Subsets
import SymbolicEquivalence.Ere.Similarity

open scoped UpTo

variable {α β : Type*} [Bot α]

namespace Ere

/-- Fold a list of expressions into a union. -/
def unionOf : List (Ere α) → Ere α := UnionFold.fold Ere.union (pred ⊥)

@[simp] theorem unionOf_nil : unionOf ([] : List (Ere α)) = pred ⊥ := rfl

@[simp] theorem unionOf_singleton (a : Ere α) : unionOf [a] = a := rfl

/-- `unionOf` of a cons is just a `⋓` when the tail is nonempty. -/
theorem unionOf_cons {as : List (Ere α)} (a : Ere α) (h : as ≠ []) :
    unionOf (a :: as) = (a ⋓ unionOf as) :=
  UnionFold.fold_cons _ _ a h

instance : UnionFold.UnionSim (Ere.union (α := α)) Ere.Sim where
  refl := Sim.refl
  symm := Sim.symm
  trans := Sim.trans
  union_cong := Sim.union_cong
  assoc := Sim.assoc
  idem := Sim.idem
  dedup := Sim.dedup

/-! ### Similarity of folds -/

/-- Splitting a fold at an append, up to `≅`. -/
theorem unionOf_append {xs ys : List (Ere α)} (hx : xs ≠ []) (hy : ys ≠ []) :
    unionOf (xs ++ ys) ≅ (unionOf xs ⋓ unionOf ys) :=
  UnionFold.fold_append _ hx hy

theorem unionOf_map_append (g : β → Ere α) {xs ys : List β} (hx : xs ≠ []) (hy : ys ≠ []) :
    unionOf ((xs ++ ys).map g) ≅ (unionOf (xs.map g) ⋓ unionOf (ys.map g)) := by
  rw [List.map_append]
  exact unionOf_append (by simpa using hx) (by simpa using hy)

/-- Deduplicating the operands does not change a fold up to `≅`. -/
theorem unionOf_map_smartDedup [BEq β] [LawfulBEq β] (g : β → Ere α) (xs : List β) :
    unionOf ((smartDedup xs).map g) ≅ unionOf (xs.map g) :=
  UnionFold.fold_map_smartDedup _ g xs

/-! ### Unions over non-empty sub-lists -/

def subsetUnions (xs : List (Ere α)) : List (Ere α) := xs |> neSubsets |> List.map unionOf
scoped prefix:max "⊕" => subsetUnions

theorem subset_sim_perm {xs ys : List (Ere α)} (hne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
    unionOf xs ∈[ (· ≅ ·) ] ⊕ ys :=
  UnionFold.fold_mem_map_neSubsets _ hne h

theorem subsetUnions_to_neSubset {x : Ere α} {xs : List (Ere α)} (h : x ∈ ⊕xs) :
    ∃ zs, zs ≠ [] ∧ x = unionOf zs ∧ zs ⊆ xs :=
  UnionFold.exists_of_mem_map_neSubsets _ h

theorem subsetUnions_monotone {xs ys : List (Ere α)} (h : xs ⊆[ (· ≅ ·) ] ys) :
    ⊕xs ⊆[ (· ≅ ·) ] ⊕ys :=
  UnionFold.map_neSubsets_mono _ h

/-- A union over a non-empty sub-multiset of `ps` is in `⊕ps`, which is the converse of
    `subsetUnions_to_neSubset`. -/
theorem mem_subsetUnions {xs ps : List (Ere α)} (h : xs ∈ neSubsets ps) :
    unionOf xs ∈ ⊕ps :=
  List.mem_map_of_mem h

/-- The image under any `g` of a union over a non-empty sub-multiset of `ps` is in `map g ⊕ps`. -/
theorem mem_map_subsetUnions {γ : Type*} {xs ps : List (Ere α)} {g : Ere α → γ}
    (h : xs ∈ neSubsets ps) : g (unionOf xs) ∈ List.map g ⊕ps :=
  List.mem_map_of_mem (mem_subsetUnions h)

end Ere
