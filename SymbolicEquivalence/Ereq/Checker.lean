import SymbolicEquivalence.Ereq.Finiteness.Closure
import SymbolicEquivalence.Ereq.NormalForm.Derivative
import SymbolicEquivalence.Ereq.NormalForm.Language
import SymbolicEquivalence.Checker.Check

/-!
# The EREQ checker

`Ereq.decideEquiv p q` checks whether the expressions `p` and `q` match the same words, and
`Ereq.decideEquiv_eq_true_iff` proves that its answer is correct. It works by making the
predicates of both expressions atomic (`Ereq.nnf`), translating them to a normal form and
running the generic checker on `Ereq.system`, whose states are normal forms.

`Ereq.system` follows `Ere.system`, except that its derivative is a two-level tree that
`flatten₂` turns into a single transition term over `PExtension α n`.
-/

open scoped Ereq EreqAtomic EreqNorm

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]
open TTerm BitTree SymbolicDerivativeSystem
open EreqNorm (normalise reconvert IsNormal isNormal_normalise)

/-- Normal forms of `Ereq` as a `SymbolicDerivativeSystem`, which the generic checker can run
    on. -/
def Ereq.system (α σ : Type*) (n : Nat) [EffectiveBooleanAlgebra α σ] [DecidableSat α]
    [DecidableEq α] :
    SymbolicDerivativeSystem (PExtension α n) (Elem σ n) (EreqNorm α n) where
  WF := IsNormal
  Lang s w := w ∈ s.lang
  null := EreqNorm.nullable
  symDer s := flatten₂ (ρₙ s)
  null_iff _ := by
    rw [EreqNorm.nullable_reconvert]
    exact EreqAtomic.nil_matches_iff_nullable
  wf_deriv h c := by
    rw [flatten₂_eval]
    exact h.derivative c
  deriv_iff := by
    rintro s ⟨e, rfl⟩ c w
    rw [flatten₂_eval]
    exact EreqNorm.deriv_iff_normalise e c w

variable [DecidableSat α] [DecidableEq α]

/-- The normal form of an expression is a well-formed state of `Ereq.system`. -/
theorem Ereq.system_wf (p : Ereq α n) : (Ereq.system α σ n).WF (normalise p.nnf) :=
  isNormal_normalise p.nnf

/-! ### The reachable states are bounded -/

/-- Every state reachable from `normalise e` is the normal form of a member of the finite list
    `⊕(pieces e)`. -/
instance : (Ereq.system α σ n).Bounded :=
  .of_closed <| by
    -- A well-formed state is the normal form of some expression `e`
    rintro _ ⟨e, rfl⟩
    refine ⟨(⊕(EreqAtomic.pieces e)).map normalise, ?_, ?_⟩
    · -- `e` is similar to a member of `⊕(pieces e)`, so it has the same normal form
      obtain ⟨y, hy, hey⟩ := EreqAtomic.subsetUnions_pieces_refl (r := e)
      exact List.mem_map.mpr ⟨y, hy, (EreqNorm.normalise_correctness hey).symm⟩
    · -- The derivative of the normal form of `y` is the normal form of the derivative of `y`,
      -- which is similar to some `z` in `⊕(pieces e)`
      rintro _ hx c
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨z, hz, hyz⟩ := EreqAtomic.deriv_mem_subsetUnions_pieces hy c
      change (flatten₂ (ρₙ (normalise y)))[c] ∈ _
      rw [flatten₂_eval, EreqNorm.derivative_normalise]
      exact List.mem_map.mpr ⟨z, hz, (EreqNorm.normalise_correctness hyz).symm⟩

/-- Decides whether `p` and `q` have the same language by running the generic checker on their
    normal forms. -/
def Ereq.decideEquiv [Hashable α] (p q : Ereq α n) : Bool :=
  (Ereq.system α σ n).decideEquiv (normalise p.nnf) (normalise q.nnf)
    (Ereq.system_wf p) (Ereq.system_wf q)

/-! ### Correctness -/

omit [DecidableSat α] in
/-- The normal form of `p.nnf` has the same language as `p`. -/
theorem Ereq.lang_normalise_nnf (p : Ereq α n) :
    ((normalise p.nnf).lang : Language (Elem σ n)) = p.lang := by
  rw [EreqNorm.lang_normalise, Ereq.lang_nnf]

omit [DecidableSat α] in
/-- The pointwise form of `Ereq.lang_normalise_nnf`. -/
theorem Ereq.matches_normalise_nnf (p : Ereq α n) (w : Word σ n) :
    w ∈ (normalise p.nnf).lang ↔ w ⊫ p :=
  Language.ext_iff.mp (Ereq.lang_normalise_nnf p) w

/-- The checker decides language equality. -/
theorem Ereq.decideEquiv_eq_true_iff [Hashable α] (p q : Ereq α n) :
    Ereq.decideEquiv p q = true ↔ (p.lang : Language (Elem σ n)) = q.lang := by
  unfold Ereq.decideEquiv
  rw [SymbolicDerivativeSystem.decideEquiv_eq_true_iff
    (Ereq.system_wf p) (Ereq.system_wf q), Language.ext_iff]
  exact forall_congr' fun w =>
    iff_congr (Ereq.matches_normalise_nnf p w) (Ereq.matches_normalise_nnf q w)

/-- The checker returns `true` exactly when `p` and `q` match the same words. -/
theorem Ereq.decideEquiv_eq_true_iff_matches [Hashable α] (p q : Ereq α n) :
    Ereq.decideEquiv p q = true ↔ ∀ w : Word σ n, (w ⊫ p) ↔ (w ⊫ q) := by
  rw [Ereq.decideEquiv_eq_true_iff, Language.ext_iff]
  exact Iff.rfl

/-! ### Left quotients -/

/-- If the checker proves the state reached from `R` along `v` equivalent to the normal form of
    `R'`, then `R'` matches `w` exactly when `R` matches `v ++ w`. -/
theorem Ereq.matches_append_iff [Hashable α] {R R' : Ereq α n} (v : Word σ n)
    (h : (Ereq.system α σ n).decideEquiv
      ((Ereq.system α σ n).derivWord (normalise R.nnf) v) (normalise R'.nnf)
      ((Ereq.system α σ n).wf_derivWord v (Ereq.system_wf R)) (Ereq.system_wf R') = true)
    (w : Word σ n) :
    (v ++ w) ⊫ R ↔ w ⊫ R' :=
  (Ereq.matches_normalise_nnf R _).symm.trans
    ((lang_append_iff (Ereq.system_wf R) (Ereq.system_wf R') v h w).trans
      (Ereq.matches_normalise_nnf R' _))

/-- The one-letter case of `matches_append_iff`. -/
theorem Ereq.matches_cons_iff [Hashable α] {R R' : Ereq α n} {c : Elem σ n}
    (h : (Ereq.system α σ n).decideEquiv
      ((Ereq.system α σ n).deriv (normalise R.nnf) c) (normalise R'.nnf)
      ((Ereq.system α σ n).wf_deriv (Ereq.system_wf R) c) (Ereq.system_wf R') = true)
    (w : Word σ n) :
    (c :: w) ⊫ R ↔ w ⊫ R' :=
  matches_append_iff [c] h w
