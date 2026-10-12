import SymbolicEquivalence.Checker.Worklist
import Mathlib.Logic.Relation

/-!
# The loop invariant of the equivalence checker

`LoopInv` says that related states agree on nullability (`InvariantNullAgree`), that every
related pair is justified by the pending pairs and the pairs already checked
(`InvariantJustified`), and that every pending pair is reachable from `(p₀, q₀)`
(`InvariantTodoReaches`). `LoopInv.step` shows that `nextState` preserves it.
-/

namespace SymbolicDerivativeSystem

open UfManager

/- `BEq`/`Hashable` are needed for `UfManager β`. -/
variable {α σ β : Type*} [EffectiveBooleanAlgebra α σ] [BEq β] [Hashable β]

section definitions

variable (D : SymbolicDerivativeSystem α σ β)

/-- For every character `c`, the derivatives of `p` and `q` by `c` are related in `uf`.
    The checker establishes this from the finite list of successors
    (`mergeAll_establishes_progresses`), even though `σ` may be infinite. -/
def Progresses (uf : UfManager β) (p q : β) : Prop :=
  ∀ c : σ, uf.Equiv (D.deriv p c) (D.deriv q c)

/-- The pair `(p, q)` is still in `todo`, or it already `Progresses`. -/
def SingleStepRelated (uf : UfManager β) (todo : List (β × β)) (p q : β) : Prop :=
  (p, q) ∈ todo ∨ Progresses D uf p q

/-- `p` and `q` are connected by a chain of `SingleStepRelated` steps. -/
abbrev Joined (uf : UfManager β) (todo : List (β × β)) :
    β → β → Prop :=
  Relation.EqvGen (SingleStepRelated D uf todo)

/-- Related states agree on nullability. -/
def InvariantNullAgree (uf : UfManager β) : Prop :=
  ∀ p q, uf.Equiv p q → D.null p = D.null q

/-- Every related pair is `Joined`. -/
def InvariantJustified (uf : UfManager β) (todo : List (β × β)) : Prop :=
  ∀ p q, uf.Equiv p q → Joined D uf todo p q

/-- Every related pair `Progresses`.  This holds once `todo` is empty
    (`progress_of_empty_todo`). -/
def InvariantProgress (uf : UfManager β) : Prop :=
  ∀ p q, uf.Equiv p q → Progresses D uf p q

/-- `uf` is a bisimulation, meaning that related states agree on nullability and their
    derivatives by every character are related. -/
structure IsBisimulation (uf : UfManager β) : Prop where
  /-- Related states agree on nullability. -/
  null : InvariantNullAgree D uf
  /-- Derivatives of related states are related. -/
  progress : InvariantProgress D uf

section reaches
variable [DecidableSat α]

/-- Every pending pair is reachable from `(p₀, q₀)`, so a nullability mismatch gives a word
    on which `p₀` and `q₀` differ. -/
def InvariantTodoReaches (p₀ q₀ : β) (todo : List (β × β)) : Prop :=
  ∀ s ∈ todo, Reaches D p₀ q₀ s

/-- The loop invariant. -/
structure LoopInv (p₀ q₀ : β) (st : State β) : Prop where
  /-- Related states agree on nullability. -/
  null : InvariantNullAgree D st.uf
  /-- Every related pair is justified. -/
  just : InvariantJustified D st.uf st.todo
  /-- `p₀` and `q₀` are related. -/
  origin : st.uf.Equiv p₀ q₀
  /-- Every pending pair is reachable from `(p₀, q₀)`. -/
  reaches : InvariantTodoReaches D p₀ q₀ st.todo

end reaches

end definitions

variable {D : SymbolicDerivativeSystem α σ β}

theorem Progresses.refl {uf : UfManager β} {p : β} :
    Progresses D uf p p := fun _ => UfManager.Equiv.refl

theorem Progresses.symm {uf : UfManager β} {p q : β}
    (h : Progresses D uf p q) : Progresses D uf q p :=
  fun c => UfManager.Equiv.symm (h c)

theorem Progresses.trans {uf : UfManager β} {x y z : β}
    (hxy : Progresses D uf x y) (hyz : Progresses D uf y z) :
    Progresses D uf x z := fun c => UfManager.Equiv.trans (hxy c) (hyz c)

/-- `Progresses` is an equivalence relation. -/
theorem Progresses.isEquivalence (uf : UfManager β) :
    Equivalence (Progresses D uf) :=
  ⟨fun _ => Progresses.refl, Progresses.symm, Progresses.trans⟩

/-! ## Bisimulations -/

/-- With nothing pending, a chain of `Progresses` steps is a single step, because
    `Progresses` is an equivalence relation. -/
theorem progress_of_empty_todo (uf : UfManager β)
    (invJust : InvariantJustified D uf []) :
    InvariantProgress D uf := fun p q hpq =>
  (Progresses.isEquivalence uf).eqvGen_iff.mp
    (Relation.EqvGen.mono
      (fun _ _ h => Or.resolve_left h (by simp)) _ _ (invJust p q hpq))

/-- Well-formed states related by a bisimulation are language equivalent. -/
theorem bisim_sound {uf : UfManager β} {p q : β}
    (hbis : IsBisimulation D uf)
    (he : uf.Equiv p q) (hp : D.WF p) (hq : D.WF q) :
    D.SemEquiv p q := by
  intro w
  induction w generalizing p q with
  | nil => rw [D.null_iff hp, D.null_iff hq, hbis.null p q he]
  | cons c w ih =>
    rw [D.deriv_iff hp, D.deriv_iff hq]
    exact ih (hbis.progress p q he c) (D.wf_deriv hp c) (D.wf_deriv hq c)

/-! ## Justification chains -/

/-- A bigger union-find and a longer `todo` preserve every single step. -/
private theorem SingleStepRelated.mono {uf uf' : UfManager β}
    {todo todo' : List (β × β)}
    (hequiv : ∀ a b, uf.Equiv a b → uf'.Equiv a b)
    (htodo : ∀ l ∈ todo, l ∈ todo') :
    ∀ p q, SingleStepRelated D uf todo p q → SingleStepRelated D uf' todo' p q :=
  fun _ _ h => h.imp (fun hp => htodo _ hp) (fun h c => hequiv _ _ (h c))

/-- A bigger union-find and a longer `todo` preserve every chain. -/
private theorem Joined.extends {uf uf' : UfManager β}
    {todo todo' : List (β × β)} {p q : β}
    (chain : Joined D uf todo p q)
    (hequiv : ∀ a b, uf.Equiv a b → uf'.Equiv a b)
    (htodo : ∀ l ∈ todo, l ∈ todo') :
    Joined D uf' todo' p q :=
  Relation.EqvGen.mono (SingleStepRelated.mono hequiv htodo) _ _ chain

/-- Removing a pending pair that already `Progresses` preserves every chain. -/
private theorem discharge_worklist_head_transitive
    {uf : UfManager β} {t : β × β} {todo : List (β × β)} {p q : β}
    (chain : Joined D uf (t :: todo) p q)
    (derivs : Progresses D uf t.1 t.2) :
    Joined D uf todo p q := by
  refine Relation.EqvGen.mono ?_ _ _ chain
  rintro a b ((_ | ⟨_, hmem⟩) | h)
  · exact Or.inr derivs
  · exact Or.inl hmem
  · exact Or.inr h

/-- If the head `t` of `todo` already `Progresses`, removing it preserves `InvariantJustified`. -/
private theorem discharge_worklist_head
    {uf : UfManager β} {t : β × β} {todo : List (β × β)}
    (i : InvariantJustified D uf (t :: todo))
    (derivs_verified : Progresses D uf t.1 t.2) :
    InvariantJustified D uf todo := fun p q hpq =>
  discharge_worklist_head_transitive (i p q hpq) derivs_verified

/-! ## Union-find reasoning -/

section lawful_beq

variable [LawfulBEq β]

/-- Merging pairs that agree on nullability preserves `InvariantNullAgree`. -/
private theorem mergeAll_maintains_null_agree
    {lvs : List (β × β)} {uf : UfManager β}
    (all_null_eq : ∀ l ∈ lvs, D.null l.1 = D.null l.2)
    (inv_before : InvariantNullAgree D uf) :
    InvariantNullAgree D (mergeAll uf lvs).1 := by
  have : IsEquiv β (fun p q => D.null p = D.null q) :=
    (equivalence_iff_isEquiv _).mp ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  intro p q hpq
  refine Relation.EqvGen.eqvGen_le (r' := fun p q => D.null p = D.null q) ?_ p q
    ((mergeAll_equiv_iff uf lvs p q).mp hpq)
  rintro a b (hab | hab)
  · exact inv_before a b hab
  · exact all_null_eq (a, b) hab

/-- Merging preserves `InvariantJustified` if the linked pairs are added to `todo`, because
    each of them then justifies itself (`mergeAll_equiv_iff_linked`). -/
private theorem mergeAll_maintains_justified_aux
    {lvs : List (β × β)} {uf : UfManager β} {rest : List (β × β)}
    (inv_before : InvariantJustified D uf rest) :
    InvariantJustified D (mergeAll uf lvs).1 (rest ++ (mergeAll uf lvs).2) := by
  intro p q hpq
  refine Relation.EqvGen.eqvGen_le ?_ p q ((mergeAll_equiv_iff_linked uf lvs p q).mp hpq)
  rintro a b (hab | hab)
  · -- an old related pair: its chain still works in the bigger union-find
    exact (inv_before a b hab).extends
      (fun _ _ h => mergeAll_preserves_equiv _ h)
      (fun _ hs => List.mem_append_left _ hs)
  · -- a linked pair: it is pending, hence justified by itself
    exact Relation.EqvGen.rel _ _ (Or.inl (List.mem_append_right _ hab))

/-! ## The worklist step -/

section decidable_sat

variable [DecidableSat α]

/-- Merging the successors of `t` makes `t` `Progresses`, because the pair of derivatives by
    any character is one of the successors. -/
private theorem mergeAll_establishes_progresses
    {t : β × β} {uf : UfManager β} :
    Progresses D (mergeAll uf ((prod D D).succs t)).1 t.1 t.2 := fun c => by
  have hmem : (D.deriv t.1 c, D.deriv t.2 c) ∈ (prod D D).succs t := by
    rw [← prod_deriv]; exact (prod D D).deriv_mem_succs t c
  exact mergeAll_establishes_all_pairs uf _ hmem

/-- Removing the head `t` from `todo` and adding the newly linked successors of `t` preserves
    `InvariantJustified`. -/
private theorem mergeAll_maintains_justified
    {t : β × β} {uf : UfManager β} {todo : List (β × β)}
    (invJust : InvariantJustified D uf (t :: todo)) :
    InvariantJustified D (mergeAll uf ((prod D D).succs t)).1
      (todo ++ (mergeAll uf ((prod D D).succs t)).2) :=
  discharge_worklist_head
    (mergeAll_maintains_justified_aux invJust)
    mergeAll_establishes_progresses

private theorem nextState_invariantNullAgree {st st' : State β}
    (invNull : InvariantNullAgree D st.uf)
    (res : nextState D st = .inl st') :
    InvariantNullAgree D st'.uf := by
  obtain ⟨t, todo', -, hnull, huf, -⟩ := nextState_inl res
  rw [huf]
  exact mergeAll_maintains_null_agree hnull invNull

private theorem nextState_invariantJustified {st st' : State β}
    (invJust : InvariantJustified D st.uf st.todo)
    (res : nextState D st = .inl st') :
    InvariantJustified D st'.uf st'.todo := by
  obtain ⟨t, todo', htodo, -, huf, htodo'⟩ := nextState_inl res
  rw [huf, htodo']
  exact mergeAll_maintains_justified (htodo ▸ invJust)

private theorem nextState_todo_closed {P : β × β → Prop} {st st' : State β}
    (hstep : ∀ t l : β × β, P t → l ∈ (prod D D).succs t → P l)
    (h : ∀ x ∈ st.todo, P x)
    (res : nextState D st = .inl st') :
    ∀ x ∈ st'.todo, P x := by
  obtain ⟨t, todo', htodo, -, -, htodo'⟩ := nextState_inl res
  intro x hx
  rw [htodo'] at hx
  rcases List.mem_append.mp hx with hm | hm
  · exact h x (htodo ▸ List.mem_cons_of_mem _ hm)
  · exact hstep t x (h t (htodo ▸ List.mem_cons_self)) ((mergeAll_linked_sublist _ _).mem hm)

private theorem nextState_invariantTodoReaches {p₀ q₀ : β} {st st' : State β}
    (iR : InvariantTodoReaches D p₀ q₀ st.todo)
    (res : nextState D st = .inl st') :
    InvariantTodoReaches D p₀ q₀ st'.todo :=
  nextState_todo_closed (fun _ _ hx hy => hx.succ hy) iR res

/-- States related before a step are still related after it. -/
private theorem nextState_preserves_equiv {st st' : State β} {p q : β}
    (invOrigin : st.uf.Equiv p q)
    (res : nextState D st = .inl st') :
    st'.uf.Equiv p q := by
  obtain ⟨t, todo', -, -, huf, -⟩ := nextState_inl res
  rw [huf]
  exact mergeAll_preserves_equiv _ invOrigin

/-- One step preserves the loop invariant. -/
theorem LoopInv.step {p₀ q₀ : β} {st st' : State β}
    (inv : LoopInv D p₀ q₀ st) (res : nextState D st = .inl st') :
    LoopInv D p₀ q₀ st' where
  null := nextState_invariantNullAgree inv.null res
  just := nextState_invariantJustified inv.just res
  origin := nextState_preserves_equiv inv.origin res
  reaches := nextState_invariantTodoReaches inv.reaches res

end decidable_sat

end lawful_beq

end SymbolicDerivativeSystem
