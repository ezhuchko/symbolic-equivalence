import SymbolicEquivalence.Ere.Finiteness.Closure
import SymbolicEquivalence.Ere.NormalForm.Derivative
import SymbolicEquivalence.Ere.NormalForm.Language
import SymbolicEquivalence.Checker.Check

/-!
# The ERE checker

`Ere.decideEquiv p q` checks whether the expressions `p` and `q` match the same words, and
`Ere.decideEquiv_eq_true_iff` proves that its answer is correct. It works by putting both
expressions in normal form and running the generic checker on `Ere.system`, whose states are
normal forms.
-/
open scoped EreNorm

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]
open Ere TTerm SymbolicDerivativeSystem
open EreNorm (normalise reconvert IsNormal isNormal_normalise)

/-- A normal form accepts `c :: w` exactly when its derivative by `c` accepts `w`. -/
theorem deriv_iff_normalise [DecidableEq α] (e : Ere α) (c : σ) (w : List σ) :
    c :: w ∈ (normalise e).lang ↔ w ∈ ((ρₙ (normalise e))[c]).lang := by
  rw [EreNorm.derivative_normalise]
  exact (EreNorm.matches_normalise e (c :: w)).trans
    (Ere.cons_matches_iff.trans (EreNorm.matches_normalise _ w).symm)

/-- Normal forms of `Ere` as a `SymbolicDerivativeSystem`, which the generic checker can run on. -/
def Ere.system (α σ : Type*) [EffectiveBooleanAlgebra α σ] [DecidableEq α] :
    SymbolicDerivativeSystem α σ (EreNorm α) where
  WF := IsNormal
  Lang s w := w ∈ s.lang
  null := EreNorm.nullable
  symDer := EreNorm.derivative
  null_iff := fun {s} _ => by
    rw [EreNorm.nullable_reconvert]
    change ([] ⊫ reconvert s) ↔ _
    exact nil_matches_iff_nullable
  wf_deriv h c := h.derivative c
  deriv_iff := by
    rintro s ⟨e, rfl⟩ c w
    exact deriv_iff_normalise e c w

/-- The normal form of an expression is a well-formed state of `Ere.system`. -/
theorem Ere.system_wf [DecidableEq α] (e : Ere α) : (Ere.system α σ).WF (normalise e) :=
  isNormal_normalise e

variable [DecidableSat α] [DecidableEq α]

/-! ### The reachable states are bounded -/

/-- Every state reachable from `normalise e` is the normal form of a member of the finite list
    `⊕(pieces e)`. -/
instance : (Ere.system α σ).Bounded :=
  .of_closed <| by
    -- A well-formed state is the normal form of some expression `e`
    rintro _ ⟨e, rfl⟩
    refine ⟨(⊕(pieces e)).map normalise, ?_, ?_⟩
    · -- `e` is similar to a member of `⊕(pieces e)`, so it has the same normal form
      obtain ⟨y, hy, hey⟩ := subsetUnions_pieces_refl (r := e)
      exact List.mem_map.mpr ⟨y, hy, (EreNorm.normalise_correctness hey).symm⟩
    · -- The derivative of the normal form of `y` is the normal form of the derivative of `y`,
      -- which is similar to some `z` in `⊕(pieces e)`
      rintro _ hx c
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨z, hz, hyz⟩ := deriv_mem_subsetUnions_pieces hy c
      change (ρₙ (normalise y))[c] ∈ _
      rw [EreNorm.derivative_normalise]
      exact List.mem_map.mpr ⟨z, hz, (EreNorm.normalise_correctness hyz).symm⟩

/-- Decides whether `p` and `q` have the same language by running the generic checker on their
    normal forms. -/
def Ere.decideEquiv [Hashable α] (p q : Ere α) : Bool :=
  (Ere.system α σ).decideEquiv (normalise p) (normalise q)
    (Ere.system_wf p) (Ere.system_wf q)

/-! ### Correctness -/

/-- The checker decides language equality. -/
theorem Ere.decideEquiv_eq_true_iff [Hashable α] (p q : Ere α) :
    Ere.decideEquiv p q = true ↔ (p.lang : Language σ) = q.lang := by
  unfold Ere.decideEquiv
  rw [SymbolicDerivativeSystem.decideEquiv_eq_true_iff
    (Ere.system_wf p) (Ere.system_wf q), Language.ext_iff]
  exact forall_congr' fun w =>
    iff_congr (EreNorm.matches_normalise p w) (EreNorm.matches_normalise q w)

/-- The checker returns `true` exactly when `p` and `q` match the same words. -/
theorem Ere.decideEquiv_eq_true_iff_matches [Hashable α] (p q : Ere α) :
    Ere.decideEquiv p q = true ↔ ∀ xs : List σ, (xs ⊫ p) ↔ (xs ⊫ q) := by
  rw [Ere.decideEquiv_eq_true_iff, Language.ext_iff]
  exact Iff.rfl

/-! ### Left quotients -/

/-- If the checker proves the state reached from `R` along `v` equivalent to `normalise R'`,
then `R'` matches `w` exactly when `R` matches `v ++ w`. -/
theorem Ere.matches_append_iff [Hashable α] {R R' : Ere α} (v : List σ)
    (h : (Ere.system α σ).decideEquiv
      ((Ere.system α σ).derivWord (normalise R) v) (normalise R')
      ((Ere.system α σ).wf_derivWord v (Ere.system_wf R)) (Ere.system_wf R') = true)
    (w : List σ) :
    (v ++ w) ⊫ R ↔ w ⊫ R' :=
  (EreNorm.matches_normalise R _).symm.trans
    ((lang_append_iff (Ere.system_wf R) (Ere.system_wf R') v h w).trans
      (EreNorm.matches_normalise R' _))

/-- The one-letter case of `matches_append_iff`. -/
theorem Ere.matches_cons_iff [Hashable α] {R R' : Ere α} {c : σ}
    (h : (Ere.system α σ).decideEquiv
      ((Ere.system α σ).deriv (normalise R) c) (normalise R')
      ((Ere.system α σ).wf_deriv (Ere.system_wf R) c) (Ere.system_wf R') = true)
    (w : List σ) :
    (c :: w) ⊫ R ↔ w ⊫ R' :=
  matches_append_iff [c] h w
