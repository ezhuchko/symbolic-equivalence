import SymbolicEquivalence.Checker.Product
import SymbolicEquivalence.UnionFind.MergeAll

/-!
# One step of the equivalence checker

The checker keeps a union-find of states believed equivalent and a list of pairs still to
check (`State`). The function `nextState` processes the first pending pair.
-/

namespace SymbolicDerivativeSystem

open UfManager

variable {α σ β : Type*} [EffectiveBooleanAlgebra α σ] [DecidableSat α]
  [BEq β] [LawfulBEq β] [Hashable β]

/-- The checker's state: a union-find `uf` of states assumed equivalent so far, and the
    list `todo` of pairs whose successors are still to be checked. -/
structure State (β : Type*) [BEq β] [Hashable β] where
  uf : UfManager β
  todo : List (β × β)

/-- One step of the loop, on the first pending pair:
    * nothing pending: the two starting states are equivalent (`.inr true`);
    * a successor pair disagrees on nullability: they are not (`.inr false`);
    * otherwise: merge the successors and queue the newly linked ones (`.inl`). -/
def nextState (D : SymbolicDerivativeSystem α σ β) (st : State β) : State β ⊕ Bool :=
  match st.todo with
  | [] => .inr true
  | t :: todo' =>
    -- computed once: `succs` is the expensive part, and both checks below use it
    let lvs := (prod D D).succs t
    if lvs.any (fun l => D.null l.1 != D.null l.2) then
      .inr false
    else
      -- `r.1`, `r.2` rather than a destructuring `let`, so the proofs can unfold them
      let r := mergeAll st.uf lvs
      -- new pairs go at the back (a queue, not a stack)
      .inl ⟨r.1, todo' ++ r.2⟩

variable {D : SymbolicDerivativeSystem α σ β}

/-- When the loop continues, `todo` was `t :: todo'`, all successors of `t` agree on
    nullability, and the new state merges them. -/
theorem nextState_inl {st st' : State β} (res : nextState D st = .inl st') :
    ∃ (t : β × β) (todo' : List (β × β)),
      st.todo = t :: todo' ∧
      (∀ l ∈ (prod D D).succs t, D.null l.1 = D.null l.2) ∧
      st'.uf = (mergeAll st.uf ((prod D D).succs t)).1 ∧
      st'.todo = todo' ++ (mergeAll st.uf ((prod D D).succs t)).2 := by
  obtain ⟨uf, todo⟩ := st
  unfold nextState at res
  match todo with
  | [] => simp at res
  | t :: todo' =>
    simp only at res
    split at res
    · simp at res
    · rename_i hany
      have h := Sum.inl.inj res
      refine ⟨t, todo', rfl, ?_, by rw [← h], by rw [← h]⟩
      simpa [bne_iff_ne] using hany

/-- When the loop stops, either `todo` is empty and the answer is `true`, or some successor
    pair disagrees on nullability and the answer is `false`. -/
theorem nextState_inr {st : State β} {b : Bool}
    (res : nextState D st = .inr b) :
    (b = true ∧ st.todo = []) ∨
    (b = false ∧ ∃ t ∈ st.todo, ∃ l ∈ (prod D D).succs t, D.null l.1 ≠ D.null l.2) := by
  obtain ⟨uf, todo⟩ := st
  unfold nextState at res
  match todo with
  | [] => exact Or.inl ⟨(Sum.inr.inj res).symm, rfl⟩
  | t :: todo' =>
    simp only at res
    split at res
    · rename_i hany
      simp only [List.any_eq_true, bne_iff_ne, ne_eq] at hany
      obtain ⟨l, hl, hne⟩ := hany
      exact Or.inr ⟨(Sum.inr.inj res).symm, t, List.mem_cons_self, l, hl, by simpa using hne⟩
    · simp at res

end SymbolicDerivativeSystem
