import SymbolicEquivalence.UnionFold.Subsets
import SymbolicEquivalence.Ereq.Similarity

open scoped UpTo EreqAtomic

variable {α β : Type*} [Bot α] {n : Nat}

namespace EreqAtomic

/-- Fold a list of expressions into a union. -/
def unionOf : List (EreqAtomic α n) → EreqAtomic α n := UnionFold.fold EreqAtomic.union bot

@[simp] theorem unionOf_nil : unionOf ([] : List (EreqAtomic α n)) = bot := rfl

@[simp] theorem unionOf_singleton (a : EreqAtomic α n) : unionOf [a] = a := rfl

/-- `unionOf` of a cons is just a `⋓ₐ` when the tail is nonempty. -/
theorem unionOf_cons {as : List (EreqAtomic α n)} (a : EreqAtomic α n) (h : as ≠ []) :
    unionOf (a :: as) = (a ⋓ₐ unionOf as) :=
  UnionFold.fold_cons _ _ a h

instance : UnionFold.UnionSim (EreqAtomic.union (α := α) (n := n)) EreqAtomic.Sim where
  refl := Sim.refl
  symm := Sim.symm
  trans := Sim.trans
  union_cong := Sim.union_cong
  assoc := Sim.assoc
  idem := Sim.idem
  dedup := Sim.dedup

/-! ### Similarity of folds -/

/-- Splitting a fold at an append, up to `≅`. -/
theorem unionOf_append {xs ys : List (EreqAtomic α n)} (hx : xs ≠ []) (hy : ys ≠ []) :
    unionOf (xs ++ ys) ≅ (unionOf xs ⋓ₐ unionOf ys) :=
  UnionFold.fold_append _ hx hy

theorem unionOf_map_append (g : β → EreqAtomic α n) {xs ys : List β}
    (hx : xs ≠ []) (hy : ys ≠ []) :
    unionOf ((xs ++ ys).map g) ≅ (unionOf (xs.map g) ⋓ₐ unionOf (ys.map g)) := by
  rw [List.map_append]
  exact unionOf_append (by simpa using hx) (by simpa using hy)

/-- Deduplicating the operands does not change a fold up to `≅`. -/
theorem unionOf_map_smartDedup [BEq β] [LawfulBEq β] (g : β → EreqAtomic α n) (xs : List β) :
    unionOf ((smartDedup xs).map g) ≅ unionOf (xs.map g) :=
  UnionFold.fold_map_smartDedup _ g xs

/-! ### Unions over non-empty sub-lists -/

def subsetUnions (xs : List (EreqAtomic α n)) : List (EreqAtomic α n) :=
  xs |> neSubsets |> List.map unionOf
scoped prefix:max "⊕" => subsetUnions

/-- If every element of `xs` is similar to an element of `ys`, then the union of `xs` is
    similar to the union of a non-empty sublist of `ys` without duplicates. It is used in the
    `∃ₐ` case of `step_to_pieces`. -/
theorem unionOf_nodup_equiv {xs ys : List (EreqAtomic α n)}
    (hne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
    ∃ us : List (EreqAtomic α n), us.Nodup ∧ us ≠ [] ∧ us ⊆ ys ∧ unionOf xs ≅ unionOf us :=
  UnionFold.exists_fold_sim_nodup _ hne h

theorem subset_sim_perm {xs ys : List (EreqAtomic α n)} (hne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
    unionOf xs ∈[ (· ≅ ·) ] ⊕ ys :=
  UnionFold.fold_mem_map_neSubsets _ hne h

theorem subsetUnions_to_neSubset {x : EreqAtomic α n} {xs : List (EreqAtomic α n)} (h : x ∈ ⊕xs) :
    ∃ zs, zs ≠ [] ∧ x = unionOf zs ∧ zs ⊆ xs :=
  UnionFold.exists_of_mem_map_neSubsets _ h

theorem subsetUnions_monotone {xs ys : List (EreqAtomic α n)} (h : xs ⊆[ (· ≅ ·) ] ys) :
    ⊕xs ⊆[ (· ≅ ·) ] ⊕ys :=
  UnionFold.map_neSubsets_mono _ h

/-- A union over a non-empty sub-multiset of `ps` is in `⊕ps`, which is the converse of
    `subsetUnions_to_neSubset`. -/
theorem mem_subsetUnions {xs ps : List (EreqAtomic α n)} (h : xs ∈ neSubsets ps) :
    unionOf xs ∈ ⊕ps :=
  List.mem_map_of_mem h

/-- The image under any `g` of a union over a non-empty sub-multiset of `ps` is in
    `map g ⊕ps`. -/
theorem mem_map_subsetUnions {γ : Type*} {xs ps : List (EreqAtomic α n)} {g : EreqAtomic α n → γ}
    (h : xs ∈ neSubsets ps) : g (unionOf xs) ∈ List.map g ⊕ps :=
  List.mem_map_of_mem (mem_subsetUnions h)

end EreqAtomic
