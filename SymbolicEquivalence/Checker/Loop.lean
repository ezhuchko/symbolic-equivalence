import SymbolicEquivalence.Checker.Invariants

/-!
# The loop of the equivalence checker

`loop` repeats `nextState` until `todo` is empty (`true`) or a nullability mismatch is
found (`false`), and `loop_spec` says what each answer means. It terminates because
`loopMetric` decreases at every step, and the same measure bounds the number of steps
(`loopFuel_eq_loop`).
-/

namespace SymbolicDerivativeSystem

open UfManager

variable {α σ β : Type*} [EffectiveBooleanAlgebra α σ] [DecidableSat α]
  [BEq β] [LawfulBEq β] [Hashable β]
  {D : SymbolicDerivativeSystem α σ β} [D.Bounded]

/-- The termination measure, which is the number of classes among the keys in `L` plus the
    length of `todo`. -/
noncomputable def loopMetric (L : Finset β) (st : State β) : Nat :=
  st.uf.numClasses L + st.todo.length

/-- Each step decreases the measure, because every pair added to `todo` removed at least one
    class (`mergeAll_numClasses_add_length_le`) and the head was removed from `todo`. -/
private theorem main_loop_termination {p₀ q₀ : β} {st st' : State β}
    (hp : D.WF p₀) (hq : D.WF q₀)
    (todoInv : InvariantTodoReaches D p₀ q₀ st.todo)
    (hm : nextState D st = .inl st') :
    loopMetric (D.jointClosure hp hq) st' < loopMetric (D.jointClosure hp hq) st := by
  obtain ⟨t, todo', htodo, -, huf, htodo'⟩ := nextState_inl hm
  -- the head is reachable, so both components of each successor are in `jointClosure`
  have hin : ∀ l ∈ (prod D D).succs t,
      l.1 ∈ D.jointClosure hp hq ∧ l.2 ∈ D.jointClosure hp hq :=
    fun l hl => mem_jointClosure_of_reaches hp hq
      ((todoInv t (htodo ▸ List.mem_cons_self)).succ hl)
  have hbudget := mergeAll_numClasses_add_length_le hin st.uf
  unfold loopMetric
  rw [huf, htodo', htodo]
  simp only [List.length_append, List.length_cons]
  omega

/-- Repeat `nextState` until it returns an answer. The invariant `inv` is carried along
    because the termination proof needs it. -/
def loop (D : SymbolicDerivativeSystem α σ β) [D.Bounded]
    (p₀ q₀ : β) (hp : D.WF p₀) (hq : D.WF q₀)
    (st : State β) (inv : LoopInv D p₀ q₀ st) : Bool :=
  match h : nextState D st with
  | .inl st' => loop D p₀ q₀ hp hq st' (inv.step h)
  | .inr b => b
termination_by loopMetric (D.jointClosure hp hq) st
decreasing_by
  exact main_loop_termination hp hq inv.reaches h

/-- If `loop` returns `true`, the final union-find relates `p₀` and `q₀`, its related states
    agree on nullability, and every related pair is justified with nothing pending. If it
    returns `false`, some pair reachable from `(p₀, q₀)` disagrees on nullability. -/
theorem loop_spec {p₀ q₀ : β} {hp : D.WF p₀} {hq : D.WF q₀} {st : State β}
    (inv : LoopInv D p₀ q₀ st) :
    (loop D p₀ q₀ hp hq st inv = true →
      ∃ uf' : UfManager β,
        InvariantNullAgree D uf' ∧
        InvariantJustified D uf' [] ∧
        uf'.Equiv p₀ q₀) ∧
    (loop D p₀ q₀ hp hq st inv = false →
      ∃ s : β × β, Reaches D p₀ q₀ s ∧ D.null s.1 ≠ D.null s.2) := by
  unfold loop
  split
  · -- a step: the invariant is preserved
    rename_i st' hns
    exact loop_spec (inv.step hns)
  · rename_i b hns
    rcases nextState_inr hns with ⟨rfl, htodo⟩ | ⟨rfl, t, ht, l, hl, hbad⟩
    · -- empty `todo`
      exact ⟨fun _ => ⟨st.uf, inv.null, htodo ▸ inv.just, inv.origin⟩, by simp⟩
    · -- nullability mismatch
      exact ⟨by simp, fun _ => ⟨l, (inv.reaches t ht).succ hl, hbad⟩⟩
termination_by loopMetric (D.jointClosure hp hq) st
decreasing_by
  rename_i hns
  exact main_loop_termination hp hq inv.reaches hns

/-! ### Bounding the number of steps -/

/-- The loop with at most `n` calls to `nextState`, returning `none` if the fuel runs out. -/
def loopFuel (D : SymbolicDerivativeSystem α σ β) : Nat → State β → Option Bool
  | 0, _ => none
  | n + 1, st =>
    match nextState D st with
    | .inl st' => loopFuel D n st'
    | .inr b => some b

/-- With at least `loopMetric` fuel, `loopFuel` gives the same answer as `loop`, so the loop
    takes at most that many steps. -/
theorem loopFuel_eq_loop {p₀ q₀ : β} {hp : D.WF p₀} {hq : D.WF q₀}
    {n : Nat} {st : State β} (inv : LoopInv D p₀ q₀ st)
    (hn : loopMetric (D.jointClosure hp hq) st ≤ n) :
    loopFuel D n st = some (loop D p₀ q₀ hp hq st inv) := by
  induction n generalizing st with
  | zero =>
    -- impossible, because the origin is in `jointClosure`, so there is a class to count
    have hpos : 0 < st.uf.numClasses (D.jointClosure hp hq) :=
      numClasses_pos (mem_jointClosure_of_reaches hp hq (Reach.refl _)).1
    unfold loopMetric at hn
    simp only [loopFuel]
    omega
  | succ n ih =>
    unfold loop
    split
    · -- a step lowers the measure, so `n` fuel is enough for the rest of the loop
      rename_i st' hns
      simp only [loopFuel, hns]
      have hlt := main_loop_termination hp hq inv.reaches hns
      exact ih (inv.step hns) (by omega)
    · rename_i b hns
      simp [loopFuel, hns]

end SymbolicDerivativeSystem
