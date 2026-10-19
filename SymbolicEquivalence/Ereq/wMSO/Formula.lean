import Mathlib.Computability.Language
import SymbolicEquivalence.Ereq.ExtendedEBA

/-!
# wMSO Logic over Finite Words

This file defines the syntax and semantics of weak monadic second-order (wMSO)
logic over finite words, parameterised by an effective Boolean algebra.
-/

universe u

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

/-- wMSO formulas with `i` set variables. -/
inductive Formula (α : Type u) : Nat → Type u where
  | or : Formula α i → Formula α i → Formula α i
  | and : Formula α i → Formula α i → Formula α i
  | not : Formula α i → Formula α i
  -- `∃Xᵢ. φ`, which adds a new last variable
  | exists₂ : Formula α (i + 1) → Formula α i
  -- `Xᵢ < Xⱼ`
  | lt : Fin i → Fin i → Formula α i
  -- `Xᵢ ⊆ Xⱼ`
  | sub : Fin i → Fin i → Formula α i
  -- `φ(Xᵢ)`, some position in `Xᵢ` has a letter satisfying `φ`
  | pred (φ : α) (n : Fin i) : Formula α i
  -- `|Xᵢ| = 1`
  | singleton : Fin i → Formula α i

namespace Formula

scoped infixr:35 " ∨ᶠ " => Formula.or
scoped infixr:40 " ∧ᶠ " => Formula.and
scoped prefix:max " ¬ᶠ " => Formula.not
scoped prefix:max " ∃ᶠ " => Formula.exists₂
scoped notation:52 n " <ᶠ " m => Formula.lt n m
scoped notation:52 n " ⊆ᶠ " m => Formula.sub n m
scoped notation "[| " n " |]" => Formula.singleton n

end Formula

open scoped Formula

/-- Gives each of `n` set variables a set of positions in a word of length `len`, as a bit
    vector. For example `[true,false,true,false]` is the set `{0,2}`. -/
abbrev Assignment (len : Nat) : Nat → Type := fun (n : Nat) => Fin n → List.Vector Bool len

/-- Add one more variable to an assignment, as the last one. -/
abbrev extAssignment {len i : Nat} (θ : Assignment len i) (v : List.Vector Bool len) :
    Assignment len (i + 1) :=
  Fin.snoc θ v

def Formula.Satisfies : (xs : List σ) → Assignment xs.length i → Formula α i → Prop
  | xs, θ, φ ∨ᶠ ψ => Satisfies xs θ φ ∨ Satisfies xs θ ψ
  | xs, θ, φ ∧ᶠ ψ => Satisfies xs θ φ ∧ Satisfies xs θ ψ
  | xs, θ, ¬ᶠ φ   => ¬ Satisfies xs θ φ
  | xs, θ, ∃ᶠ φ   => ∃ (v : List.Vector Bool xs.length), Satisfies xs (extAssignment θ v) φ
  | xs, θ, m <ᶠ n => ∃ (pos pos' : Fin xs.length), (θ m).get pos ∧ (θ n).get pos' ∧ pos < pos'
  | xs, θ, m ⊆ᶠ n => ∀ (i : Fin xs.length), (θ m).get i → (θ n).get i
  | xs, θ, [| n |] => ∃! (i : Fin xs.length), (θ n)[i]
  | xs, θ, .pred (p : α) n =>
    ∃ (pos : Fin xs.length), (θ n).get pos ∧ xs[pos]?.any (Models.models p)

/-- Collect the bits of a word into one bit vector per variable. `List.toWord` undoes this. -/
def Word.transpose : (w : Word σ n) → Assignment (w.map Prod.fst).length n
  | [] => fun _ => List.Vector.nil
  | (_, v) :: w' => fun i => v.get i ::ᵥ transpose w' i

/-- The words whose letters and bits satisfy the formula. -/
def Formula.lang (φ : Formula α n) : Language (Elem σ n) :=
  { w | Formula.Satisfies (w.map Prod.fst) (Word.transpose w) φ }
