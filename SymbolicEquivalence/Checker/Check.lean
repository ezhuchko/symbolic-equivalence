import SymbolicEquivalence.Checker.Loop

/-!
# Deciding equivalence

`D.decideEquiv p₀ q₀` returns `true` exactly when `p₀` and `q₀` have the same language
(`decideEquiv_eq_true_iff`).
-/

namespace SymbolicDerivativeSystem

variable {α σ β : Type*} [EffectiveBooleanAlgebra α σ]
  {D : SymbolicDerivativeSystem α σ β}

section answers

/-- If a pair reachable from `(p₀, q₀)` disagrees on nullability, `p₀` and `q₀` are not
    equivalent. -/
private theorem mismatch_separates {p₀ q₀ : β} {s : β × β}
    (hp : D.WF p₀) (hq : D.WF q₀)
    (hreach : Reaches D p₀ q₀ s)
    (hbad : D.null s.1 ≠ D.null s.2) :
    ¬ D.SemEquiv p₀ q₀ := fun hsem =>
    hbad (beq_iff_eq.mp (hreach.null_of_forall_lang ⟨hp, hq⟩ hsem))

variable [BEq β] [Hashable β]

/-- With nothing pending (`todo = []`), `uf` is a bisimulation, so the related states `p`
    and `q` are equivalent. -/
private theorem empty_worklist_sound {p q : β} {uf : UfManager β}
    (hp : D.WF p) (hq : D.WF q)
    (invNull : InvariantNullAgree D uf)
    (invJust : InvariantJustified D uf [])
    (invOrigin : uf.Equiv p q) :
    D.SemEquiv p q :=
  bisim_sound ⟨invNull, progress_of_empty_todo _ invJust⟩ invOrigin hp hq

end answers

section initial_state

/-- Initially the only pending pair is `(p₀, q₀)`, which is reachable from itself. -/
private theorem invariants_beginning_reaches {p₀ q₀ : β} :
    InvariantTodoReaches D p₀ q₀ [(p₀, q₀)] := fun _ hs =>
  List.mem_singleton.mp hs ▸ Reach.refl _

variable [BEq β] [LawfulBEq β] [Hashable β]

/-- The union-find `decideEquiv` starts from, which is the empty one with `p₀` and `q₀` merged. -/
def initUf (p₀ q₀ : β) : UfManager β :=
  (UfManager.merge (UfManager.empty : UfManager β) p₀ q₀).1

/-- The state `decideEquiv` starts from, with `(p₀, q₀)` pending. -/
def initState (p₀ q₀ : β) : State β :=
  ⟨initUf p₀ q₀, [(p₀, q₀)]⟩

/-- Initially only `p₀` and `q₀` are related to each other, and they agree on nullability
    by `h`. -/
private theorem invariants_beginning_null_agree {p₀ q₀ : β}
    (h : D.null p₀ = D.null q₀) :
    InvariantNullAgree D (initUf p₀ q₀) := fun x y g => by
  rw [initUf, UfManager.merge_empty_equiv_iff] at g
  match g with
  | Or.inl e => subst e; rfl
  | Or.inr (Or.inl ⟨e1, e2⟩) => subst e1 e2; exact h
  | Or.inr (Or.inr ⟨e1, e2⟩) => subst e1 e2; exact h.symm

/-- Initially `p₀` and `q₀` are the only distinct related states, and the pending pair
    `(p₀, q₀)` justifies them. -/
private theorem invariants_beginning_justified {p₀ q₀ : β} :
    InvariantJustified D (initUf p₀ q₀) [(p₀, q₀)] := fun x y g => by
  rw [initUf, UfManager.merge_empty_equiv_iff] at g
  match g with
  | Or.inl e => subst e; exact Relation.EqvGen.refl _
  | Or.inr (Or.inl ⟨e1, e2⟩) =>
    subst e1 e2
    exact Relation.EqvGen.rel _ _ (Or.inl (List.mem_singleton.mpr rfl))
  | Or.inr (Or.inr ⟨e1, e2⟩) =>
    subst e1 e2
    exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ (Or.inl (List.mem_singleton.mpr rfl)))

/-- The initial state satisfies the loop invariant, given that `p₀` and `q₀` agree on
    nullability. -/
theorem initState_inv {p₀ q₀ : β} (g : D.null p₀ = D.null q₀) :
    LoopInv D p₀ q₀ (initState p₀ q₀) where
  null := invariants_beginning_null_agree g
  just := invariants_beginning_justified
  origin := UfManager.merge_equiv_self
  reaches := invariants_beginning_reaches

end initial_state

section decideEquiv

variable [DecidableSat α] [BEq β] [LawfulBEq β] [Hashable β] [D.Bounded]

/-- Decide whether `p₀` and `q₀` have the same language. -/
def decideEquiv (D : SymbolicDerivativeSystem α σ β) [D.Bounded] (p₀ q₀ : β)
    (hp : D.WF p₀) (hq : D.WF q₀) : Bool :=
  if hn : D.null p₀ = D.null q₀ then
    loop D p₀ q₀ hp hq (initState p₀ q₀) (initState_inv hn)
  else false

/-- `decideEquiv` returns `true` exactly when `p₀` and `q₀` are equivalent. -/
theorem decideEquiv_eq_true_iff {p₀ q₀ : β} (hp : D.WF p₀) (hq : D.WF q₀) :
    D.decideEquiv p₀ q₀ hp hq = true ↔ D.SemEquiv p₀ q₀ := by
  unfold decideEquiv
  by_cases g : D.null p₀ = D.null q₀
  · -- `p₀` and `q₀` agree on nullability, so the loop runs from `initState`
    rw [dite_eq_left g]
    constructor
    · intro hloop
      obtain ⟨uf', hNull, hJust, hOrigin⟩ := (loop_spec (initState_inv g)).1 hloop
      exact empty_worklist_sound hp hq hNull hJust hOrigin
    · intro hsem
      by_contra hloop
      simp only [Bool.not_eq_true] at hloop
      obtain ⟨s, hreach, hbad⟩ := (loop_spec (initState_inv g)).2 hloop
      exact mismatch_separates hp hq hreach hbad hsem
  · -- `p₀` and `q₀` disagree on nullability, so the empty word tells them apart
    rw [dite_eq_right g]
    simp only [Bool.false_eq_true, false_iff]
    intro contra
    exact g (contra.null_eq hp hq)

/-- If the checker proves the derivative of `s` along `v` equivalent to `t`, then `t` accepts
    `w` exactly when `s` accepts `v ++ w`. -/
theorem lang_append_iff {s t : β} (hs : D.WF s) (ht : D.WF t) (v : List σ)
    (h : D.decideEquiv (D.derivWord s v) t (D.wf_derivWord v hs) ht = true) (w : List σ) :
    D.Lang s (v ++ w) ↔ D.Lang t w :=
  (D.lang_derivWord v hs w).symm.trans ((decideEquiv_eq_true_iff _ _).mp h w)

/-- The loop takes at most `|jointClosure| + 1` steps. -/
theorem loopFuel_initState {p₀ q₀ : β} (hp : D.WF p₀) (hq : D.WF q₀)
    (hn : D.null p₀ = D.null q₀) :
    loopFuel D ((D.jointClosure hp hq).card + 1) (initState p₀ q₀) =
      some (loop D p₀ q₀ hp hq (initState p₀ q₀) (initState_inv hn)) :=
  loopFuel_eq_loop (initState_inv hn) (Nat.add_le_add_right UfManager.numClasses_le_card _)

end decideEquiv

end SymbolicDerivativeSystem
