import SymbolicEquivalence.SymbolicDerivativeSystem
import Mathlib.Data.Set.Finite.Basic

/-!
# Products of symbolic derivative systems

`prod D₁ D₂` is the product system, whose states are pairs. Both components read the same
word, and the language of `(p, q)` is the set of words on which `p` and `q` agree.

`jointClosure` is the finite set of states reachable from `p₀` or `q₀`, which contains both
components of every pair the equivalence checker visits.
-/

open TTerm

namespace SymbolicDerivativeSystem

/-! ### The product system -/

universe u

section Prod
variable {α σ : Type*} {β₁ β₂ : Type u} [EffectiveBooleanAlgebra α σ]

/-- The product of two symbolic derivative systems. -/
def prod (D₁ : SymbolicDerivativeSystem α σ β₁) (D₂ : SymbolicDerivativeSystem α σ β₂) :
    SymbolicDerivativeSystem α σ (β₁ × β₂) where
  WF s := D₁.WF s.1 ∧ D₂.WF s.2
  Lang s w := D₁.Lang s.1 w ↔ D₂.Lang s.2 w
  null s := D₁.null s.1 == D₂.null s.2
  symDer s := liftBinary Prod.mk (D₁.symDer s.1) (D₂.symDer s.2)
  null_iff {s} hs := by
    rw [beq_iff_eq, ← Bool.coe_iff_coe]
    exact iff_congr (D₁.null_iff hs.1) (D₂.null_iff hs.2)
  wf_deriv hs c := by
    rw [eval_liftBinary]
    exact ⟨D₁.wf_deriv hs.1 c, D₂.wf_deriv hs.2 c⟩
  deriv_iff {s} hs c w := by
    rw [eval_liftBinary]
    exact iff_congr (D₁.deriv_iff hs.1 c w) (D₂.deriv_iff hs.2 c w)

variable {D₁ : SymbolicDerivativeSystem α σ β₁} {D₂ : SymbolicDerivativeSystem α σ β₂}

@[simp] theorem prod_null (s : β₁ × β₂) :
    (prod D₁ D₂).null s = (D₁.null s.1 == D₂.null s.2) := rfl

/-! ### Derivatives and reachability -/

/-- The derivative of a product state is the pair of component derivatives. -/
theorem prod_deriv (s : β₁ × β₂) (c : σ) :
    (prod D₁ D₂).deriv s c = (D₁.deriv s.1 c, D₂.deriv s.2 c) :=
  eval_liftBinary _ _ _ _

/-- A word is read by the two components in parallel. -/
theorem prod_derivWord (s : β₁ × β₂) (v : List σ) :
    (prod D₁ D₂).derivWord s v = (D₁.derivWord s.1 v, D₂.derivWord s.2 v) := by
  induction v generalizing s with
  | nil => rfl
  | cons c v ih => simp only [derivWord_cons, ih, prod_deriv]

/-- Reachability in the product is reachability of both components along the same word. -/
theorem prod_reach {s t : β₁ × β₂} :
    (prod D₁ D₂).Reach s t ↔ ∃ v, D₁.derivWord s.1 v = t.1 ∧ D₂.derivWord s.2 v = t.2 := by
  simp only [Reach, prod_derivWord, Prod.ext_iff]

theorem Reach.fst {s t : β₁ × β₂} (h : (prod D₁ D₂).Reach s t) : D₁.Reach s.1 t.1 :=
  let ⟨v, h1, _⟩ := prod_reach.mp h; ⟨v, h1⟩

theorem Reach.snd {s t : β₁ × β₂} (h : (prod D₁ D₂).Reach s t) : D₂.Reach s.2 t.2 :=
  let ⟨v, _, h2⟩ := prod_reach.mp h; ⟨v, h2⟩

end Prod

/-! ### Pairs reachable from `(p₀, q₀)` -/

section Self
variable {α σ β : Type*} [EffectiveBooleanAlgebra α σ]

/-- `s` is reached from the origin pair `(p₀, q₀)` along a common word. -/
abbrev Reaches (D : SymbolicDerivativeSystem α σ β) (p₀ q₀ : β) (s : β × β) : Prop :=
  (prod D D).Reach (p₀, q₀) s

open scoped Classical in
/-- The states reachable from `p₀` or from `q₀`, a finite set by `Bounded`.  This is only
    used in the termination measure and never computed. -/
noncomputable def jointClosure (D : SymbolicDerivativeSystem α σ β) [F : D.Bounded]
    {p₀ q₀ : β} (hp : D.WF p₀) (hq : D.WF q₀) : Finset β :=
  (F.finite_reach hp).toFinset ∪ (F.finite_reach hq).toFinset

open scoped Classical in
/-- Both components of a reachable pair are in `jointClosure`. -/
theorem mem_jointClosure_of_reaches {D : SymbolicDerivativeSystem α σ β} [D.Bounded]
    {p₀ q₀ : β} {s : β × β} (hp : D.WF p₀) (hq : D.WF q₀)
    (h : Reaches D p₀ q₀ s) :
    s.1 ∈ D.jointClosure hp hq ∧ s.2 ∈ D.jointClosure hp hq :=
  ⟨Finset.mem_union_left _ (Set.Finite.mem_toFinset _ |>.mpr h.fst),
   Finset.mem_union_right _ (Set.Finite.mem_toFinset _ |>.mpr h.snd)⟩

end Self

end SymbolicDerivativeSystem
