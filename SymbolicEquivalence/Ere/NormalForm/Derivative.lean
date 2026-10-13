import SymbolicEquivalence.Ere.NormalForm.Normalise
import SymbolicEquivalence.Ere.NormalForm.Reconvert
import SymbolicEquivalence.Ere.Derivative

/-!
# Derivatives directly on normal forms

This file defines `nullable` and the symbolic derivative `ρₙ` directly on normal forms, so the
checker never has to convert back to `Ere`. They agree with the `Ere` versions on normalised
expressions (`nullable_normalise`, `derivative_normalise`). -/

open scoped Ere EreNorm
open Ere (unionOf unionOf_cons)

open TTerm

namespace EreNorm

variable {α : Type*}

mutual

/-- Nullability of a normal form (agrees with `nullable ∘ reconvert`). -/
def nullable : EreNorm α → Bool
  | .ε => true
  | .pred _ => false
  | ⋃ₙ[x, y | zs] => nullable x || nullableUnion y zs
  | l ⋒ₙ r => nullable l && nullable r
  | l ⬝ₙ r => nullable l && nullable r
  | _★ₙ => true
  | ~ₙ r => !nullable r
  | .xor l r => nullable l != nullable r
termination_by r => sizeOf r

/-- Nullability of an operand list given as its first element and the rest. -/
def nullableUnion : EreNorm α → List (EreNorm α) → Bool
  | x, [] => nullable x
  | x, y :: ys => nullable x || nullableUnion y ys
termination_by x xs => sizeOf x + sizeOf xs

end

/-- Nullability of an operand list is `any nullable` over it. -/
theorem nullableUnion_any (x : EreNorm α) (xs : List (EreNorm α)) :
    nullableUnion x xs = (x :: xs).any nullable := by
  induction xs generalizing x with
  | nil => simp [nullableUnion]
  | cons y ys ih => rw [nullableUnion, ih]; simp

/-- Nullability of any node is `any nullable` over its operands. -/
theorem nullable_toList (r : EreNorm α) : nullable r = (toList r).any nullable := by
  cases r with
  | union x y zs => rw [nullable, nullableUnion_any]; simp
  | _ => simp [toList]

section Bridge

variable [Bot α]

mutual

theorem nullable_reconvert (r : EreNorm α) :
  nullable r = (reconvert r).nullable := by
  match r with
  | .ε | .pred _ => simp [nullable, Ere.nullable]
  | ⋃ₙ[x, y | zs] =>
    rw [nullable, reconvert_union, List.map_cons,
      unionOf_cons _ (by simp), nullable_reconvert x, nullableUnion_reconvert y zs]
    simp [Ere.nullable]
  | l ⋒ₙ r | l ⬝ₙ r | .xor l r =>
    simp [nullable, nullable_reconvert l, nullable_reconvert r, Ere.nullable]
  | r★ₙ => simp [nullable, Ere.nullable]
  | ~ₙ r => simp [nullable, nullable_reconvert r, Ere.nullable]
termination_by sizeOf r

theorem nullableUnion_reconvert (x : EreNorm α) (xs : List (EreNorm α)) :
  nullableUnion x xs = (unionOf ((x :: xs).map reconvert)).nullable := by
  match xs with
  | [] => simpa [nullableUnion] using nullable_reconvert x
  | y :: ys =>
    rw [nullableUnion, List.map_cons, unionOf_cons _ (by simp),
      nullable_reconvert x, nullableUnion_reconvert y ys]
    simp [Ere.nullable]
termination_by sizeOf x + sizeOf xs

end

end Bridge

section Null

variable [Bot α] [DecidableEq α]

/-- `a ⋓' b` is nullable exactly when `a` or `b` is. -/
theorem nullable_mkUnion {a b : EreNorm α} (ha : WellFormed a) :
    nullable (a ⋓' b) = (nullable a || nullable b) := by
  by_cases hna : a = pred ⊥
  · subst hna; simp [nullable]
  by_cases hnb : b = pred ⊥
  · subst hnb; simp [nullable]
  rw [nullable_toList (a ⋓' b), toList_mkUnion ha hna hnb, any_smartDedup,
    List.any_append, ← nullable_toList, ← nullable_toList]

/-- `mkCat A B` is nullable exactly when both `A` and `B` are. -/
theorem nullable_mkCat (A B : EreNorm α) :
    nullable (mkCat A B) = (nullable A && nullable B) := by
  by_cases bl : A = pred ⊥
  · simp [bl, nullable]
  by_cases br : B = pred ⊥
  · simp [br, nullable]
  by_cases el : A = ε
  · simp [el, nullable]
  by_cases er : B = ε
  · simp [er, nullable]
  rw [mkCat_eq_cat bl br el er, nullable]

/-- `mkInter A B` is nullable exactly when both `A` and `B` are. -/
theorem nullable_mkInter (A B : EreNorm α) :
    nullable (mkInter A B) = (nullable A && nullable B) := by
  by_cases bl : A = pred ⊥
  · simp [bl, nullable]
  by_cases br : B = pred ⊥
  · simp [br, nullable]
  rw [mkInter_eq_inter bl br, nullable]

/-- `normalise` preserves nullability. -/
theorem nullable_normalise (e : Ere α) : nullable (normalise e) = e.nullable := by
  induction e with
  | union l r ihl ihr =>
    simp only [normalise]
    rw [nullable_mkUnion (wellFormed_of_normalise l), ihl, ihr]
    simp
  | intersection l r ihl ihr => simp only [normalise, nullable_mkInter, ihl, ihr, Ere.nullable]
  | concatenation l r ihl ihr => simp only [normalise, nullable_mkCat, ihl, ihr, Ere.nullable]
  | _ => simp_all [normalise, nullable]

end Null

section Def

/-! ### The derivative on normal forms -/

variable {σ : Type*} [EffectiveBooleanAlgebra α σ] [DecidableEq α]

mutual

/-- The symbolic derivative on normal forms, which follows `Ere.derivative` but builds with
    the smart constructors so that every leaf is again a normal form. -/
def derivative : EreNorm α → TTerm α (EreNorm α)
  | .ε => leaf (.pred ⊥)
  | .pred b => node b (leaf .ε) (leaf (.pred ⊥))
  | ⋃ₙ[x, y | zs] => liftBinary (· ⋓' ·) (derivative x) (derivativeUnion y zs)
  | l ⋒ₙ r => liftBinary mkInter (derivative l) (derivative r)
  | l ⬝ₙ r =>
    if nullable l then
      liftBinary (· ⋓' ·) (liftUnary (mkCat · r) (derivative l)) (derivative r)
    else
      liftUnary (mkCat · r) (derivative l)
  | r★ₙ => liftUnary (mkCat · r★ₙ) (derivative r)
  | ~ₙ r => liftUnary (~ₙ ·) (derivative r)
  | .xor l r => liftBinary .xor (derivative l) (derivative r)
termination_by r => sizeOf r

/-- Derivative of an operand list, folded with `mkUnion`. -/
def derivativeUnion : EreNorm α → List (EreNorm α) → TTerm α (EreNorm α)
  | x, [] => derivative x
  | x, y :: ys => liftBinary mkUnion (derivative x) (derivativeUnion y ys)
termination_by x xs => sizeOf x + sizeOf xs

end

end Def

scoped prefix:max " ρₙ " => EreNorm.derivative

/-! ## Well-formedness is preserved -/

variable {σ : Type*} [EffectiveBooleanAlgebra α σ] [DecidableEq α]

mutual

theorem derivative_eval_wf {r : EreNorm α} (h : WellFormed r) (a : σ) :
  WellFormed ((derivative r)[a]) := by
  match r, h with
  | .ε, _ =>
    simp only [derivative, eval_leaf]
    exact .pred ⊥
  | .pred b, _ =>
    simp only [derivative, eval_node]
    split <;> constructor
  | ⋃ₙ[x, y | zs], .union hwf _ _ =>
    simp only [derivative, eval_liftBinary]
    exact wellFormed_mkUnion (derivative_eval_wf (hwf x (by simp)) a)
      (derivativeUnion_eval_wf (hwf y (by simp)) (fun z hz => hwf z (by simp [hz])) a)
  | l ⋒ₙ r, .intersection hl hr =>
    simp only [derivative, eval_liftBinary]
    exact wellFormed_mkInter (derivative_eval_wf hl a) (derivative_eval_wf hr a)
  | l ⬝ₙ r, .concatenation hl hr =>
    by_cases hn : nullable l
    · rw [derivative, ite_eq_left hn]
      simp only [eval_liftBinary, eval_liftUnary]
      exact wellFormed_mkUnion
        (wellFormed_mkCat (derivative_eval_wf hl a) hr)
        (derivative_eval_wf hr a)
    · rw [derivative, ite_eq_right hn]
      simp only [eval_liftUnary]
      exact wellFormed_mkCat (derivative_eval_wf hl a) hr
  | r★ₙ, .star hr =>
    simp only [derivative, eval_liftUnary]
    exact wellFormed_mkCat (derivative_eval_wf hr a) (.star hr)
  | ~ₙ r, .negation hr =>
    simp only [derivative, eval_liftUnary]
    exact .negation (derivative_eval_wf hr a)
  | .xor l r, .xor hl hr =>
    simp only [derivative, eval_liftBinary]
    exact .xor (derivative_eval_wf hl a) (derivative_eval_wf hr a)
termination_by sizeOf r

theorem derivativeUnion_eval_wf {x : EreNorm α} {xs : List (EreNorm α)}
    (hx : WellFormed x) (h : ∀ z ∈ xs, WellFormed z) (a : σ) :
    WellFormed ((derivativeUnion x xs)[a]) := by
  match xs with
  | [] => simpa [derivativeUnion] using derivative_eval_wf hx a
  | y :: ys =>
    simp only [derivativeUnion, eval_liftBinary]
    exact wellFormed_mkUnion (derivative_eval_wf hx a)
      (derivativeUnion_eval_wf (h y (by simp)) (fun z hz => h z (by simp [hz])) a)
termination_by sizeOf x + sizeOf xs

end

/-! ## Normalisation commutes with derivatives -/

/-- The derivative of an operand list is the `⋓'`-fold of the operands' derivatives. -/
theorem eval_derivativeUnion (x : EreNorm α) (xs : List (EreNorm α)) (c : σ) :
    (derivativeUnion x xs)[c] = unionAll ((x :: xs).map (fun w => (ρₙ w)[c])) := by
  induction xs generalizing x with
  | nil => simp [derivativeUnion]
  | cons y ys ih => simp only [derivativeUnion, eval_liftBinary, List.map_cons, unionAll_cons, ih]

/-- The derivative of any normal form is the fold over its operand list. -/
theorem eval_derivative_toList (r : EreNorm α) (c : σ) :
    (ρₙ r)[c] = unionAll ((toList r).map (fun w => (ρₙ w)[c])) := by
  cases r with
  | union x y zs =>
    simp only [derivative, eval_liftBinary, eval_derivativeUnion, toList_union,
      List.map_cons, unionAll_cons]
  | _ => simp [toList]

/-- The derivative of `a ⋓' b` is the smart union of the derivatives of `a` and `b`. -/
theorem derivative_mkUnion {a b : EreNorm α} (ha : WellFormed a) (hb : WellFormed b) (c : σ) :
    (ρₙ (a ⋓' b))[c] = (ρₙ a)[c] ⋓' (ρₙ b)[c] := by
  by_cases hna : a = pred ⊥
  · subst hna; simp [derivative]
  by_cases hnb : b = pred ⊥
  · subst hnb; simp [derivative]
  have hwf : ∀ w ∈ toList a ++ toList b, WellFormed ((ρₙ w)[c]) := fun w hw =>
    derivative_eval_wf (mem_toList_append ha hb hw).1 c
  have hwf_a : ∀ x ∈ (toList a).map (fun w => (ρₙ w)[c]), WellFormed x := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    exact hwf w (List.mem_append_left _ hw)
  -- The derivative of a union is the union of the derivatives of its operands
  rw [eval_derivative_toList (a ⋓' b), toList_mkUnion ha hna hnb]
  -- Removing duplicate operands does not change the union
  rw [unionAll_map_smartDedup _ _ hwf]
  -- Split the operands into those of `a` and those of `b`
  rw [List.map_append, unionAll_append hwf_a,
    ← eval_derivative_toList a c, ← eval_derivative_toList b c]

/-- The derivative of `mkInter A B` is the smart intersection of their derivatives. -/
theorem derivative_mkInter (A B : EreNorm α) (c : σ) :
    (ρₙ (mkInter A B))[c] = mkInter ((ρₙ A)[c]) ((ρₙ B)[c]) := by
  by_cases bl : A = pred ⊥
  · subst bl; simp [derivative]
  by_cases br : B = pred ⊥
  · subst br; simp [derivative]
  rw [mkInter_eq_inter bl br, derivative, eval_liftBinary]

/-- The derivative of `mkCat A B` follows the concatenation rule with smart constructors.
    The `A = ε` case needs `mkUnion_bot_left`. -/
theorem derivative_mkCat (A B : EreNorm α) (c : σ) :
    (ρₙ (mkCat A B))[c] =
      if nullable A then mkCat ((ρₙ A)[c]) B ⋓' (ρₙ B)[c] else mkCat ((ρₙ A)[c]) B := by
  by_cases bl : A = pred ⊥
  · subst bl; simp [derivative, nullable]
  by_cases br : B = pred ⊥
  · subst br; simp [derivative]
  by_cases el : A = ε
  · subst el; simp [derivative, nullable]
  by_cases er : B = ε
  · subst er; simp [derivative]
  rw [mkCat_eq_cat bl br el er]
  by_cases hn : nullable A
  · rw [derivative, ite_eq_left hn, ite_eq_left hn]
    simp only [eval_liftBinary, eval_liftUnary]
  · rw [derivative, ite_eq_right hn, ite_eq_right hn]
    simp only [eval_liftUnary]

/-- The derivative of `normalise y` is the normal form of the derivative of `y`. -/
theorem derivative_normalise (y : Ere α) (c : σ) :
    (ρₙ (normalise y))[c] = normalise ((ρ y)[c]) := by
  induction y with
  | ε => simp [normalise, derivative, Ere.derivative]
  | pred p =>
    simp only [normalise, derivative, Ere.derivative, eval_node, eval_leaf]
    split <;> simp [normalise]
  | union l r ihl ihr =>
    simp only [normalise, Ere.derivative, eval_liftBinary]
    rw [derivative_mkUnion (wellFormed_of_normalise l) (wellFormed_of_normalise r), ihl, ihr]
  | intersection l r ihl ihr =>
    simp only [normalise, Ere.derivative, eval_liftBinary]
    rw [derivative_mkInter, ihl, ihr]
  | concatenation l r ihl ihr =>
    simp only [normalise]
    rw [derivative_mkCat, nullable_normalise l]
    by_cases h : l.nullable
    · rw [ite_eq_left h, Ere.derivative, ite_eq_left h]
      simp only [eval_liftBinary, eval_liftUnary, normalise, ihl, ihr]
    · rw [ite_eq_right h, Ere.derivative, ite_eq_right h]
      simp only [eval_liftUnary, normalise, ihl]
  | star r ih => simp only [normalise, derivative, Ere.derivative, eval_liftUnary, ih]
  | negation r ih => simp only [normalise, derivative, Ere.derivative, eval_liftUnary, ih]
  | xor l r ihl ihr => simp only [normalise, derivative, Ere.derivative, eval_liftBinary, ihl, ihr]

/-- Derivatives of an output of `normalise` are again outputs of `normalise`. -/
theorem IsNormal.derivative {s : EreNorm α} (h : IsNormal s) (c : σ) :
    IsNormal ((ρₙ s)[c]) := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨(ρ e)[c], (derivative_normalise e c).symm⟩

end EreNorm
