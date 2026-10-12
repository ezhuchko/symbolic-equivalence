import Mathlib.Order.Notation
import Mathlib.Data.Fintype.Defs

/-!
# Effective Boolean Algebras for Symbolic Alphabets

This module introduces the `EffectiveBooleanAlgebra` typeclass for symbolic alphabets.
-/

/-- A denotation of predicates `α` as Boolean-valued functions on characters `σ`. -/
class Models (α : Type u) (σ : outParam (Type v)) where
  models : α → σ → Bool
export Models (models)

namespace Models
scoped notation:51 c:52 " ⊨ " p:52 => Models.models p c
end Models

open scoped Models

/-- A type of predicates `α` with Boolean operations and a computable denotation
`models : α → σ → Bool`.

The five `models_*` fields say exactly that `models` is a homomorphism of the Boolean
signature into `σ → Bool`. Note that they are not the Boolean algebra laws and `α` itself
need not satisfy e.g., `a ⊓ a = a`. The laws hold up to denotation, e.g.,
`∀ c, (c ⊨ a ⊓ a) = (c ⊨ a)`. -/
class EffectiveBooleanAlgebra (α : Type u) (σ : outParam (Type v))
    extends Models α σ, Bot α, Top α, Min α, Max α, Compl α where
  models_bot : models ⊥ c = false
  models_top : models ⊤ c = true
  models_compl : models aᶜ c = !models a c
  models_min : models (a ⊓ b) c = (models a c && models b c)
  models_max : models (a ⊔ b) c = (models a c || models b c)

open EffectiveBooleanAlgebra in
attribute [simp] models_bot models_top models_min models_max models_compl

namespace Models

/-- `p` is satisfiable if some character models it. -/
def Satisfiable [Models α σ] (p : α) : Prop :=
  ∃ c, c ⊨ p

theorem satisfiable_def [Models α σ] (p : α) : Satisfiable p ↔ ∃ c, c ⊨ p := Iff.rfl

theorem not_satisfiable_iff [Models α σ] {p : α} : ¬ Satisfiable p ↔ ∀ c, c ⊨ p = false := by
  simp [Satisfiable]

theorem models_eq_false_of_not_satisfiable [Models α σ] {p : α} (h : ¬ Satisfiable p) (c : σ) :
    c ⊨ p = false :=
  not_satisfiable_iff.mp h c

section EffectiveBooleanAlgebra
variable [EffectiveBooleanAlgebra α σ]
open EffectiveBooleanAlgebra

@[simp] theorem not_satisfiable_bot : ¬ Satisfiable (⊥ : α) := by simp [Satisfiable]

@[simp] theorem satisfiable_top [Nonempty σ] : Satisfiable (⊤ : α) :=
  (‹Nonempty σ›).elim fun c => ⟨c, models_top⟩

@[simp] theorem satisfiable_max {a b : α} :
    Satisfiable (a ⊔ b) ↔ Satisfiable a ∨ Satisfiable b := by
  simp [Satisfiable, exists_or]

/-- Satisfiability transfers along semantic implication of predicates. -/
theorem Satisfiable.mono {a b : α} (h : ∀ c, c ⊨ a → c ⊨ b) : Satisfiable a → Satisfiable b
  | ⟨c, hc⟩ => ⟨c, h c hc⟩

theorem Satisfiable.of_min_left {a b : α} (h : Satisfiable (a ⊓ b)) : Satisfiable a := by
  obtain ⟨c, hc⟩ := h
  rw [models_min, Bool.and_eq_true] at hc
  exact ⟨c, hc.1⟩

theorem Satisfiable.of_min_right {a b : α} (h : Satisfiable (a ⊓ b)) : Satisfiable b := by
  obtain ⟨c, hc⟩ := h
  rw [models_min, Bool.and_eq_true] at hc
  exact ⟨c, hc.2⟩
end EffectiveBooleanAlgebra
end Models

/-- Decidable satisfiability, in the style of `DecidableEq`, which gives a `Decidable` instance
for `Models.Satisfiable p` for every `p`. -/
abbrev DecidableSat (α : Type u) {σ : Type v} [Models α σ] : Type u :=
  ∀ p : α, Decidable (Models.Satisfiable p)

/-- Over a finite alphabet, satisfiability is decidable by exhaustive search. Low priority so
that a hand-written solver for a specific alphabet is always preferred. -/
instance (priority := low) Models.decidableSatOfFintype [Models α σ] [Fintype σ] :
    DecidableSat α :=
  fun p => decidable_of_iff (∃ c, c ⊨ p) (Models.satisfiable_def p).symm

/-- Syntax for Boolean predicates equipped with Boolean semantics. -/
inductive BA (α : Type u)
  | atom (a : α)
  | top | bot
  | and (a b : BA α)
  | or (a b : BA α)
  | not (a : BA α)
  deriving Repr, DecidableEq, Hashable
open BA

/-- The Boolean structure lives on the syntax, independent of any denotation for
the atoms. This is what lets `(⊥ : BA α)` elaborate with no `Models α σ` instance in scope. -/
instance : Bot (BA α) := ⟨bot⟩
instance : Top (BA α) := ⟨top⟩
instance : Min (BA α) := ⟨and⟩
instance : Max (BA α) := ⟨or⟩
instance : Compl (BA α) := ⟨not⟩

/-- Models function induced on the term algebra. -/
protected def BA.models [Models α σ] (c : σ) : BA α → Bool
  | atom a => models a c
  | not a  => !(a.models c)
  | and a b => a.models c && b.models c
  | or a b  => a.models c || b.models c
  | bot => false
  | top => true

/-- The term algebra is an effective Boolean algebra. -/
instance [Models α σ] : EffectiveBooleanAlgebra (BA α) σ where
  models a c := a.models c
  models_bot := rfl
  models_top := rfl
  models_min := rfl
  models_max := rfl
  models_compl := rfl
