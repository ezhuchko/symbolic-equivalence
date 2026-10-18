import SymbolicEquivalence.Ereq.wMSO.Translation
import SymbolicEquivalence.Ereq.Checker

/-!
# Deciding wMSO over an EBA

`Ereq.decideEquiv ⌜φ⌝ ⌜ψ⌝` checks whether the formulas `φ` and `ψ` are satisfied by the same
words and assignments, and `Formula.decideEquiv_eq_true_iff` proves that the answer is correct.
It works by translating both formulas to `Ereq` and running the `Ereq` checker.
-/

open scoped Formula Ereq

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]
  [DecidableSat α] [DecidableEq α] [Hashable α]

/-- The checker returns `true` exactly when `φ` and `ψ` are satisfied by the same words and
    assignments. -/
theorem Formula.decideEquiv_eq_true_iff (φ ψ : Formula α n) :
    Ereq.decideEquiv ⌜φ⌝ ⌜ψ⌝ = true ↔
      ∀ (xs : List σ) (θ : Assignment xs.length n),
        Formula.Satisfies xs θ φ ↔ Formula.Satisfies xs θ ψ := by
  rw [Ereq.decideEquiv_eq_true_iff_matches]
  constructor
  · -- an encoded word is a word
    intro h xs θ
    rw [toEreq_correctness φ xs θ, toEreq_correctness ψ xs θ]
    exact h _
  · -- every word is the encoding of its letters and its bits
    intro h w
    simpa only [toEreq_correctness, List.toWord_transpose] using
      h (w.map Prod.fst) (Word.transpose w)
