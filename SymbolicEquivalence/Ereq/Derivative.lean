import SymbolicEquivalence.Ereq.BitTree
import SymbolicEquivalence.Ereq.AtomicSemantics
import SymbolicEquivalence.SymbolicDerivativeSystem

/-!
# Derivatives of expressions with atomic predicates

Defines nullability and the derivative of an `EreqAtomic`, proves them correct, and
carries the results over to `Ereq` through `Ereq.nnf`.

Combining two derivatives drops branches that can never be taken, which needs
`[DecidableSat α]`. Without this the trees grow exponentially in the number of predicates.
-/

open scoped Ereq EreqAtomic
open TTerm BitTree

universe u

/-- Derivative trees: stratified transition terms (`BitTree`) with `EreqAtomic` leaves. -/
abbrev DerTree (α : Type u) (n : Nat) := BitTree α n (EreqAtomic α n)

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

namespace EreqAtomic

/-- Existential projection, the tree-level counterpart of `∃ₐ`. -/
abbrev liftUExists [DecidableSat α] : DerTree α (n + 1) → DerTree α n :=
  liftUProj (· ⋓ₐ ·) (∃ₐ ·)

@[simp]
def nullable : EreqAtomic α n → Bool
  | .ε      => true
  | .pred _ => false
  | L ⋓ₐ R  => nullable L || nullable R
  | L ⋒ₐ R  => nullable L && nullable R
  | L ⬝ₐ R  => nullable L && nullable R
  | _★ₐ     => true
  | ~ₐR     => !(nullable R)
  | ∃ₐ R    => nullable R

@[simp]
def derivative [DecidableSat α] : EreqAtomic α n → DerTree α n
  | .ε               => leaf (leaf bot)
  | .pred (.p q)     => .node q (leaf (leaf ε)) (leaf (leaf bot))
  | .pred (.notP q)  => .node q (leaf (leaf bot)) (leaf (leaf ε))
  | .pred (.pred φ)  => leaf (.node φ (leaf .ε) (leaf bot))
  | L ⋓ₐ R => liftBinaryNorm (· ⋓ₐ ·) (derivative L) (derivative R)
  | L ⋒ₐ R => liftBinaryNorm (· ⋒ₐ ·) (derivative L) (derivative R)
  | L ⬝ₐ R =>
    if nullable L then
      let left := liftUnaryNorm (· ⬝ₐ R) (derivative L)
      liftBinaryNorm (· ⋓ₐ ·) left (derivative R)
    else
      liftUnaryNorm (· ⬝ₐ R) (derivative L)
  | R★ₐ  => liftUnaryNorm (· ⬝ₐ R★ₐ) (derivative R)
  | ~ₐR  => liftUnaryNorm (~ₐ·) (derivative R)
  | ∃ₐ R => liftUExists (derivative R)

end EreqAtomic

-- Opened selectively, because `EreqNorm` has its own `nullable` and `derivative`.
open EreqAtomic (nullable derivative)

namespace EreqAtomic
scoped prefix:max "ρ " => EreqAtomic.derivative

theorem ordered_derivative [DecidableSat α] {r : EreqAtomic α n} : TTerm.Ordered (ρ r) := by
  match r with
  | .ε | .pred (.pred _) => exact .base
  | .pred (.p _) | .pred (.notP _) => exact .ind .base .base .base .base
  | l ⋓ₐ r => exact ordered_liftBinaryNorm ordered_derivative ordered_derivative _
  | l ⋒ₐ r => exact ordered_liftBinaryNorm ordered_derivative ordered_derivative _
  | l ⬝ₐ r =>
    unfold derivative; split
    · exact ordered_liftBinaryNorm (ordered_liftUnaryNorm ordered_derivative _) ordered_derivative _
    · exact ordered_liftUnaryNorm ordered_derivative _
  | r★ₐ => exact ordered_liftUnaryNorm ordered_derivative _
  | ~ₐr => exact ordered_liftUnaryNorm ordered_derivative _
  | ∃ₐ r => exact ordered_liftUProj _ _ ordered_derivative

/-- On an ordered tree, `liftUExists` is, up to `≅`, the union of the two bit
    instantiations. -/
theorem liftUProj_eval_sim [DecidableSat α] {f : DerTree α (n + 1)}
    (h : TTerm.Ordered f) (x : Elem σ n) :
    (liftUExists f)[x]ₙ ≅
    (∃ₐ (f[(⟨x.1, x.2.snoc true⟩ : Elem σ (n + 1))]ₙ) ⋓ₐ
     ∃ₐ (f[(⟨x.1, x.2.snoc false⟩ : Elem σ (n + 1))]ₙ)) := by
  match f, h with
  | leaf t, _ =>
    simp only [liftUProj_leaf, eval₂_leaf, eval_liftUnary]
    exact Sim.symm Sim.idem
  | .node ⟨c, pc⟩ f1 f0, .ind h1 h0 l1 l0 =>
    by_cases hc : c = n
    · subst hc
      simp only [liftUProj_node, ↓reduceDIte]
      rw [eval_liftBinaryNorm]
      rw [eval_liftUProj_of_below _ _ l1 x true, eval_liftUProj_of_below _ _ l0 x false]
      have ht : (x.2.snoc true)[c] = true := List.Vector.getElem_snoc_last
      have hf : (x.2.snoc false)[c] = false := List.Vector.getElem_snoc_last
      simp only [eval₂_node, models_fin, Fin.getElem_fin, ht, hf]
      exact Sim.refl
    · have hlt : c < n := by omega
      simp only [liftUProj_node, hc, ↓reduceDIte]
      have hsnoc_t : (x.2.snoc true)[c] = x.2[c] := List.Vector.getElem_snoc_lt hlt
      have hsnoc_f : (x.2.snoc false)[c] = x.2[c] := List.Vector.getElem_snoc_lt hlt
      by_cases hxc : x.2[c] = true
      · simp only [eval₂_node, models_fin, Fin.getElem_fin, Fin.coe_castPred, hxc, hsnoc_t, hsnoc_f]
        exact liftUProj_eval_sim h1 x
      · simp only [eval₂_node, models_fin, Fin.getElem_fin, Fin.coe_castPred, hxc, hsnoc_t, hsnoc_f]
        exact liftUProj_eval_sim h0 x

/-! ### Correctness of `nullable` and `derivative` -/

theorem nil_matches_iff_nullable {R : EreqAtomic α n} : ([] : Word σ n) ⊫ₐ R ↔ nullable R := by
  induction R with
  | ε | pred _ => simp [matches_simps]
  | union _ _ ihL ihR | intersection _ _ ihL ihR | concatenation _ _ ihL ihR =>
    simp [ihL, ihR]
  | star R _ => simpa using ⟨0, rfl⟩
  | negation R ih => simp [ih]
  | existential R ih => simp [ih, Word.extend]

/-- A nonempty word matches `L ⬝ R` iff its head is consumed by `L`, or `L` is skipped. -/
theorem cons_matches_cat {x : Elem σ n} {xs : Word σ n} {L R : EreqAtomic α n} :
    x :: xs ⊫ₐ (L ⬝ₐ R) ↔
      (∃ ys, x :: ys ⊫ₐ L ∧ ∃ zs, zs ⊫ₐ R ∧ xs = ys ++ zs) ∨ ([] ⊫ₐ L ∧ x :: xs ⊫ₐ R) := by
  simp only [matches_cat, List.cons_eq_append_iff]
  constructor
  · rintro ⟨ys, zs, hy, hz, ⟨rfl, rfl⟩ | ⟨ys', rfl, rfl⟩⟩
    · exact .inr ⟨hy, hz⟩
    · exact .inl ⟨ys', hy, zs, hz, rfl⟩
  · rintro (⟨ys, hy, zs, hz, rfl⟩ | ⟨hl, hr⟩)
    · exact ⟨x :: ys, zs, hy, hz, .inr ⟨ys, rfl, rfl⟩⟩
    · exact ⟨[], x :: xs, hl, hr, .inl ⟨rfl, rfl⟩⟩

/-- A nonempty word matches `R★` iff a nonempty prefix matches `R` and the rest matches `R★`. -/
theorem cons_matches_star {x : Elem σ n} {xs : Word σ n} {R : EreqAtomic α n} :
    x :: xs ⊫ₐ (R★ₐ) ↔ ∃ ys, x :: ys ⊫ₐ R ∧ ∃ zs, zs ⊫ₐ R★ₐ ∧ xs = ys ++ zs := by
  rw [matches_star]
  constructor
  · rintro ⟨k, h⟩
    induction k with
    | zero => simp [repeatCat] at h
    | succ k ih =>
      obtain ⟨ys, hy, zs, hz, rfl⟩ | ⟨-, h⟩ := cons_matches_cat.mp h
      · exact ⟨ys, hy, zs, matches_star.mpr ⟨k, hz⟩, rfl⟩
      · exact ih h
  · rintro ⟨ys, hy, zs, hz, rfl⟩
    obtain ⟨k, hz⟩ := matches_star.mp hz
    exact ⟨k + 1, cons_matches_cat.mpr (.inl ⟨ys, hy, zs, hz, rfl⟩)⟩

theorem cons_matches_iff [DecidableSat α] {R : EreqAtomic α n} {x : Elem σ n} {xs : Word σ n} :
    x :: xs ⊫ₐ R ↔ xs ⊫ₐ (ρ R)[x]ₙ := by
  match R with
  | .pred φ => cases φ <;> simp [matches_simps] <;> split <;> simp_all
  | .ε =>
    simp only [matches_eps, reduceCtorEq, derivative, eval₂_leaf, eval_leaf, matches_pred,
      false_iff]
    rintro ⟨_, -, h⟩
    simp [FundamentalPredicate.models] at h
  | l ⋓ₐ r => simp [eval_liftBinaryNorm, cons_matches_iff (R := l), cons_matches_iff (R := r)]
  | l ⋒ₐ r => simp [eval_liftBinaryNorm, cons_matches_iff (R := l), cons_matches_iff (R := r)]
  | l ⬝ₐ r =>
    rw [cons_matches_cat]
    by_cases g : nullable l <;>
      simp [g, eval_liftBinaryNorm, eval_liftUnaryNorm, nil_matches_iff_nullable,
        cons_matches_iff (R := l), cons_matches_iff (R := r)]
  | r★ₐ =>
    rw [cons_matches_star]
    simp [eval_liftUnaryNorm, cons_matches_iff (R := r)]
  | ~ₐr => simp [eval_liftUnaryNorm, cons_matches_iff (R := r)]
  | ∃ₐ r =>
    simp only [derivative]
    rw [Matches, Matches, sim_lang_eq (liftUProj_eval_sim ordered_derivative x),
      ← Matches, ← Matches]
    simp only [matches_simps, ← exists_or]
    obtain ⟨a, v⟩ := x
    constructor
    · rintro ⟨⟨_ | ⟨b, bs⟩, p⟩, h⟩
      · exact absurd p (by simp)
      · cases b <;> simp only [Word.extend_cons] at h
        · exact ⟨⟨bs, Nat.succ_inj.mp p⟩, .inr (cons_matches_iff.mp h)⟩
        · exact ⟨⟨bs, Nat.succ_inj.mp p⟩, .inl (cons_matches_iff.mp h)⟩
    · rintro ⟨s, h | h⟩
      · exact ⟨⟨true :: s.toList, by simp⟩, cons_matches_iff.mpr h⟩
      · exact ⟨⟨false :: s.toList, by simp⟩, cons_matches_iff.mpr h⟩

end EreqAtomic

theorem Ereq.nil_matches_iff_nullable {R : Ereq α n} :
    ([] : Word σ n) ⊫ R ↔ nullable (Ereq.nnf R) :=
  (Ereq.matches_nnf R).symm.trans EreqAtomic.nil_matches_iff_nullable

theorem Ereq.cons_matches_iff [DecidableSat α] {R : Ereq α n} {x : Elem σ n} {xs : Word σ n} :
    x :: xs ⊫ R ↔ xs ⊫ₐ (ρ (Ereq.nnf R))[x]ₙ :=
  (Ereq.matches_nnf R).symm.trans EreqAtomic.cons_matches_iff

/-- `EreqAtomic` without normalisation as a `SymbolicDerivativeSystem`, with the derivative
    tree flattened by `flatten₂`. It is not `Bounded`, because its reachable states are finite
    only up to `≅`. -/
def EreqAtomic.rawSystem (α σ : Type*) (n : Nat) [EffectiveBooleanAlgebra α σ] [DecidableSat α] :
    SymbolicDerivativeSystem (PExtension α n) (Elem σ n) (EreqAtomic α n) where
  WF _ := True
  Lang r w := w ⊫ₐ r
  null := EreqAtomic.nullable
  symDer r := flatten₂ (ρ r)
  null_iff _ := EreqAtomic.nil_matches_iff_nullable
  wf_deriv _ _ := trivial
  deriv_iff _ _ w := by rw [flatten₂_eval]; exact EreqAtomic.cons_matches_iff
