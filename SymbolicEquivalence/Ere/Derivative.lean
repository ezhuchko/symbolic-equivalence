import SymbolicEquivalence.TransitionTerm
import SymbolicEquivalence.Ere.Semantics
import SymbolicEquivalence.SymbolicDerivativeSystem

open scoped Ere Models

section Derivative
variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

open List TTerm Ere

/-- `nullable r` is `true` exactly when the language of `r` contains the empty word. -/
@[simp]
def Ere.nullable : Ere α → Bool
  | ε          => true
  | Ere.pred _ => false
  | l ⋓ r      => nullable l || nullable r
  | l ⋒ r      => nullable l && nullable r
  | l ⬝ r      => nullable l && nullable r
  | _★         => true
  | ~ r        => !nullable r

/-- The symbolic derivative of `r`, a transition term that evaluates at any character `c` to
    the derivative of `r` by `c`. -/
@[simp]
def Ere.derivative : Ere α → TTerm α (Ere α)
  | ε          => leaf (pred ⊥)
  | Ere.pred b => node b (leaf ε) (leaf (pred ⊥))
  | l ⋓ r      => liftBinary (· ⋓ ·) (derivative l) (derivative r)
  | l ⋒ r      => liftBinary (· ⋒ ·) (derivative l) (derivative r)
  | l ⬝ r      =>
    if nullable l then
      liftBinary (· ⋓ ·) (liftUnary (· ⬝ r) (derivative l)) (derivative r)
    else
      liftUnary (· ⬝ r) (derivative l)
  | r★  => liftUnary (· ⬝ r★) (derivative r)
  | ~ r => liftUnary (~ ·) (derivative r)
namespace Ere
scoped prefix:max " ρ " => Ere.derivative
end Ere

/-! ### The classical derivative -/

/-- The classical Brzozowski derivative of `r` with respect to a character `x`. -/
def Ere.der (r : Ere α) (x : σ) : Ere α :=
  match r with
  | ε => pred ⊥
  | pred φ => if x ⊨ φ then ε else pred ⊥
  | l ⋓ r  => der l x ⋓ der r x
  | l ⋒ r  => der l x ⋒ der r x
  | r★     => der r x ⬝ r★
  | ~ r    => ~(der r x)
  | l ⬝ r  =>
    if nullable l then
      (der l x ⬝ r) ⋓ der r x
    else
      der l x ⬝ r

/-- The classical derivative and symbolic derivative of `r` coincide. -/
theorem Ere.der_eq_eval_derivative (r : Ere α) (x : σ) :
  der r x = (ρ r)[x] :=
  match r with
  | ε => by simp only [der, derivative, eval_leaf]
  | pred φ => by simp only [der, derivative, eval_node, eval_leaf]
  | l ⋓ r => by
    simp only [der]
    simp only [der_eq_eval_derivative l x, der_eq_eval_derivative r x, derivative]
    exact Eq.symm (eval_liftBinary union (derivative l) (derivative r) x)
  | l ⋒ r => by
    simp only [der]
    simp only [der_eq_eval_derivative l x, der_eq_eval_derivative r x, derivative]
    exact Eq.symm (eval_liftBinary intersection (derivative l) (derivative r) x)
  | r★   => by
    simp only [der, derivative]
    rw[der_eq_eval_derivative r x]
    exact Eq.symm (eval_liftUnary (· ⬝ r★) (derivative r) x)
  | ~ r  => by
    simp only [der, derivative]
    rw[der_eq_eval_derivative r x]
    exact Eq.symm (eval_liftUnary negation (derivative r) x)
  | l ⬝ r => by
    unfold der
    by_cases h : nullable l
    · simp [derivative, h]
      simp [der_eq_eval_derivative l x, der_eq_eval_derivative r x]
    · simp only [derivative, h]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw[der_eq_eval_derivative l x]
      exact (eval_liftUnary (· ⬝ r) (derivative l) x).symm

end Derivative

/-! ### Correctness of the symbolic derivative -/

open List TTerm

namespace Ere

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

theorem nil_matches_iff_nullable {r : Ere α} : ([] : List σ) ⊫ r ↔ nullable r :=
  match r with
  | ε => by simp
  | pred p => by simp
  | l ⋓ r => by simp [nil_matches_iff_nullable (r := l), nil_matches_iff_nullable (r := r)]
  | l ⋒ r => by simp [nil_matches_iff_nullable (r := l), nil_matches_iff_nullable (r := r)]
  | l ⬝ r => by simp [nil_matches_iff_nullable (r := l), nil_matches_iff_nullable (r := r)]
  | r★ => by simpa using ⟨0, rfl⟩
  | ~ r => by simp [nil_matches_iff_nullable (r := r)]

/-- A nonempty word matches `l ⬝ r` iff its head is consumed by `l`, or `l` is skipped. -/
theorem cons_matches_cat {a : σ} {xs : List σ} {l r : Ere α} :
    a :: xs ⊫ (l ⬝ r) ↔
      (∃ u, a :: u ⊫ l ∧ ∃ v, v ⊫ r ∧ u ++ v = xs) ∨ ([] ⊫ l ∧ a :: xs ⊫ r) := by
  simp only [matches_cat, append_eq_cons_iff]
  constructor
  · rintro ⟨u, v, hu, hv, ⟨rfl, rfl⟩ | ⟨u', rfl, rfl⟩⟩
    · exact .inr ⟨hu, hv⟩
    · exact .inl ⟨u', hu, v, hv, rfl⟩
  · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨hl, hr⟩)
    · exact ⟨a :: u, v, hu, hv, .inr ⟨u, rfl, rfl⟩⟩
    · exact ⟨[], a :: xs, hl, hr, .inl ⟨rfl, rfl⟩⟩

/-- A nonempty word matches `r★` iff a nonempty prefix matches `r` and the rest matches `r★`. -/
theorem cons_matches_star {a : σ} {xs : List σ} {r : Ere α} :
    a :: xs ⊫ (r★) ↔ ∃ u, a :: u ⊫ r ∧ ∃ v, v ⊫ r★ ∧ u ++ v = xs := by
  rw [matches_star]
  constructor
  · rintro ⟨n, h⟩
    induction n with
    | zero => simp [repeatCat] at h
    | succ n ih =>
      obtain ⟨u, hu, v, hv, rfl⟩ | ⟨-, h⟩ := cons_matches_cat.mp h
      · exact ⟨u, hu, v, matches_star.mpr ⟨n, hv⟩, rfl⟩
      · exact ih h
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨n, hv⟩ := matches_star.mp hv
    exact ⟨n + 1, cons_matches_cat.mpr (.inl ⟨u, hu, v, hv, rfl⟩)⟩

/-- `a :: xs` matches `r` exactly when `xs` matches the derivative of `r` at `a`. -/
theorem cons_matches_iff {r : Ere α} {a : σ} {xs : List σ} : a :: xs ⊫ r ↔ xs ⊫ (ρ r)[a] :=
  match r with
  | ε => by simp
  | pred p => by by_cases h : a ⊨ p <;> simp [h]
  | l ⋓ r => by simp [cons_matches_iff (r := l), cons_matches_iff (r := r)]
  | l ⋒ r => by simp [cons_matches_iff (r := l), cons_matches_iff (r := r)]
  | ~ r => by simp [cons_matches_iff (r := r)]
  | r★ => by rw [cons_matches_star]; simp [cons_matches_iff (r := r)]
  | l ⬝ r => by
    rw [cons_matches_cat]
    by_cases g : nullable l <;>
      simp [g, nil_matches_iff_nullable, cons_matches_iff (r := l), cons_matches_iff (r := r)]

/-- `Ere` without normalisation as a `SymbolicDerivativeSystem`. It is not `Bounded`, because
    its reachable states are finite only up to `≅`. -/
def rawSystem (α σ : Type*) [EffectiveBooleanAlgebra α σ] :
    SymbolicDerivativeSystem α σ (Ere α) where
  WF _ := True
  Lang r w := w ⊫ r
  null := nullable
  symDer := derivative
  null_iff _ := nil_matches_iff_nullable
  wf_deriv _ _ := trivial
  deriv_iff _ _ _ := cons_matches_iff

end Ere
