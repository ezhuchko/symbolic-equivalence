import SymbolicEquivalence.Ere.Finiteness.Pieces

/-!
# Finiteness of the state space

`⊕(pieces r)` is a fixed finite list containing, up to `≅`, every state
reachable from `r` by iterated symbolic derivation (`Ere.derivWord_mem_pieces`), and every
derivative of its own members (`Ere.deriv_mem_subsetUnions_pieces`).
-/
open Ere TTerm List Sim
open scoped UpTo

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

namespace Ere

/-- The leaves (states) of the transition term of `r`. -/
def step (r : Ere α) : List (Ere α) := leaves (ρ r)

end Ere

theorem step_to_pieces {f e : Ere α} (e_in : e ∈ step f) :
    ∃ xs, unionOf xs ≅ e ∧ xs ∈ neSubsets (pieces f) := by
  induction f generalizing e with
  | ε =>
    obtain rfl : e = pred ⊥ := by simpa [step] using e_in
    exact ⟨[_], refl, neSubsets_singleton (by simp [pieces])⟩
  | pred φ =>
    simp only [step, derivative, leaves_node, leaves_leaf, cons_append, nil_append,
      mem_cons, not_mem_nil, or_false] at e_in
    rcases e_in with rfl | rfl <;> exact ⟨[_], refl, neSubsets_singleton (by simp [pieces])⟩
  | union l r ihl ihr =>
    simp only [step, derivative, leaves_binary, mem_productWith] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨xs ++ ys,
      trans (unionOf_append (ne_nil_of_mem_neSubsets xs_in) (ne_nil_of_mem_neSubsets ys_in))
        (union_cong hx hy),
      neSubsets_append xs_in ys_in⟩
  | intersection l r ihl ihr =>
    simp only [step, derivative, leaves_binary, mem_productWith] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨[_], inter_cong hx hy, neSubsets_singleton <| mem_productWith.mpr
      ⟨_, mem_subsetUnions xs_in, _, mem_subsetUnions ys_in, rfl⟩⟩
  | concatenation l r ihl ihr =>
    simp only [step, derivative] at e_in
    split at e_in
    · simp only [leaves_binary, leaves_map, mem_productWith, mem_map] at e_in
      obtain ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩ := e_in
      obtain ⟨xs, hx, xs_in⟩ := ihl ha
      obtain ⟨ys, hy, ys_in⟩ := ihr hb
      refine ⟨(unionOf xs ⬝ r) :: ys, ?_,
        neSubsets_append
          (neSubsets_singleton (mem_map_subsetUnions xs_in)) ys_in⟩
      rw [unionOf_cons _ (ne_nil_of_mem_neSubsets ys_in)]
      exact union_cong (cat_cong hx refl) hy
    · simp only [leaves_map, mem_map] at e_in
      obtain ⟨a, ha, rfl⟩ := e_in
      obtain ⟨xs, hx, xs_in⟩ := ihl ha
      exact ⟨[_], cat_cong hx refl, neSubsets_singleton <|
        mem_append_left _ (mem_map_subsetUnions xs_in)⟩
  | star r ih =>
    simp only [step, derivative, leaves_map, mem_map] at e_in
    obtain ⟨a, ha, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ih ha
    exact ⟨[_], cat_cong hx refl, neSubsets_singleton <|
      mem_cons_of_mem _ (mem_map_subsetUnions xs_in)⟩
  | negation r ih =>
    simp only [step, derivative, leaves_map, mem_map] at e_in
    obtain ⟨a, ha, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ih ha
    exact ⟨[_], neg_cong hx, neSubsets_singleton (mem_map_subsetUnions xs_in)⟩
  | xor l r ihl ihr =>
    simp only [step, derivative, leaves_binary, mem_productWith] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨[_], xor_cong hx hy, neSubsets_singleton <| mem_productWith.mpr
      ⟨_, mem_subsetUnions xs_in, _, mem_subsetUnions ys_in, rfl⟩⟩

theorem step_to_subsetUnions {r : Ere α} :
  step r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun _ in_step =>
  have ⟨xs, hx, xs_in⟩ := step_to_pieces in_step
  ⟨unionOf xs, mem_subsetUnions xs_in, symm hx⟩

/-- Every iterated derivative of `r` is similar to a member of `⊕(pieces r)`. -/
theorem Ere.derivWord_mem_pieces {r : Ere α} (v : List σ) :
  (rawSystem α σ).derivWord r v ∈[ (· ≅ ·) ] ⊕(pieces r) :=
  match v with
  | []     => subsetUnions_pieces_refl
  | c :: v =>
    subsetUnions_pieces_trans (derivWord_mem_pieces v)
      (step_to_subsetUnions _ (eval_mem_leaves (ρ r) c))

/-- A derivative of a member of `⊕(pieces root)` is again in it up to `≅`. -/
theorem Ere.deriv_mem_subsetUnions_pieces {root y : Ere α} (hy : y ∈ ⊕(pieces root)) (c : σ) :
    (ρ y)[c] ∈[ (· ≅ ·) ] ⊕(pieces root) :=
  subsetUnions_pieces_trans (step_to_subsetUnions _ (eval_mem_leaves (ρ y) c)) ⟨y, hy, Sim.refl⟩
