import SymbolicEquivalence.Ereq.NormalForm.Normalise
import SymbolicEquivalence.Ereq.NormalForm.Reconvert
import SymbolicEquivalence.Ereq.Derivative
import SymbolicEquivalence.Ereq.NormalForm.Language

/-!
# Derivatives directly on normal forms

This file defines `nullable` and the symbolic derivative `ρₙ` directly on normal forms, so the
checker never has to convert back to `EreqAtomic`. The derivative is a `BitTree` with
`EreqNorm` leaves (`DerTreeNorm`), built with the smart constructors so that every leaf is
again well-formed (`derivative_eval_wf`). They agree with the `EreqAtomic` versions on
normalised expressions (`nullable_normalise`, `derivative_normalise`).
-/

open scoped EreqAtomic EreqNorm
open TTerm BitTree EreqNormList
open EreqAtomic (Sim unionOf unionOf_cons)

namespace EreqNorm

variable {α : Type*}

/-! ## Nullability -/

mutual

/-- Nullability of a normal form (agrees with `nullable ∘ reconvert`). -/
def nullable : EreqNorm α n → Bool
  | .ε => true
  | .pred _ => false
  | ⋃ₙ[x, y | zs] => nullable x || nullableUnion y zs
  | l ⋒ₙ r => nullable l && nullable r
  | l ⬝ₙ r => nullable l && nullable r
  | _★ₙ => true
  | ~ₙ r => !nullable r
  | ∃ₙ r => nullable r
termination_by r => sizeOf r

/-- Nullability of an operand list given as its first element and the rest. -/
def nullableUnion : EreqNorm α n → EreqNormList α n → Bool
  | x, .nil => nullable x
  | x, .cons y ys => nullable x || nullableUnion y ys
termination_by x xs => sizeOf x + sizeOf xs

end

/-- Nullability of an operand list is `any nullable` over it. -/
theorem nullableUnion_any (x : EreqNorm α n) (xs : EreqNormList α n) :
    nullableUnion x xs = (x :: xs.toList).any nullable := by
  match xs with
  | .nil => simp [nullableUnion]
  | .cons y ys => rw [nullableUnion, nullableUnion_any y ys]; simp
termination_by sizeOf xs

/-- Nullability of any node is `any nullable` over its operands. -/
theorem nullable_toList (r : EreqNorm α n) : nullable r = (toList r).any nullable := by
  cases r with
  | union x y zs => rw [nullable, nullableUnion_any]; simp [toList]
  | _ => simp [toList]

section Bridge

variable [Bot α]

mutual

theorem nullable_reconvert (r : EreqNorm α n) :
    nullable r = (reconvert r).nullable := by
  match r with
  | .ε | .pred _ => simp [nullable, EreqAtomic.nullable]
  | ⋃ₙ[x, y | zs] =>
    rw [nullable, reconvert_union, List.map_cons,
      unionOf_cons (as := (y :: zs.toList).map reconvert) _ (by simp),
      nullable_reconvert x, nullableUnion_reconvert y zs]
    simp [EreqAtomic.nullable]
  | l ⋒ₙ r | l ⬝ₙ r =>
    simp [nullable, nullable_reconvert l, nullable_reconvert r, EreqAtomic.nullable]
  | r★ₙ => simp [nullable, EreqAtomic.nullable]
  | ~ₙ r => simp [nullable, nullable_reconvert r, EreqAtomic.nullable]
  | ∃ₙ r => simp [nullable, nullable_reconvert r, EreqAtomic.nullable]
termination_by sizeOf r

theorem nullableUnion_reconvert (x : EreqNorm α n) (xs : EreqNormList α n) :
    nullableUnion x xs = (unionOf ((x :: xs.toList).map reconvert)).nullable := by
  match xs with
  | .nil => simpa [nullableUnion] using nullable_reconvert x
  | .cons y ys =>
    rw [nullableUnion, toList_cons, List.map_cons,
      unionOf_cons (as := (y :: ys.toList).map reconvert) _ (by simp),
      nullable_reconvert x, nullableUnion_reconvert y ys]
    simp [EreqAtomic.nullable]
termination_by sizeOf x + sizeOf xs

end

end Bridge

section Null

variable [Bot α] [DecidableEq α]

/-- `a ⋓' b` is nullable exactly when `a` or `b` is. -/
theorem nullable_mkUnion {a b : EreqNorm α n} (ha : WellFormed a) :
    nullable (a ⋓' b) = (nullable a || nullable b) := by
  by_cases hna : a = bot
  · subst hna; simp [nullable]
  by_cases hnb : b = bot
  · subst hnb; simp [nullable]
  rw [nullable_toList (a ⋓' b), toList_mkUnion ha hna hnb, any_smartDedup, List.any_append,
    ← nullable_toList, ← nullable_toList]

/-- `mkCat A B` is nullable exactly when both `A` and `B` are. -/
theorem nullable_mkCat (A B : EreqNorm α n) :
    nullable (mkCat A B) = (nullable A && nullable B) := by
  by_cases bl : A = bot
  · simp [bl, nullable]
  by_cases br : B = bot
  · simp [br, nullable]
  by_cases el : A = ε
  · simp [el, nullable]
  by_cases er : B = ε
  · simp [er, nullable]
  rw [mkCat_eq_cat bl br el er, nullable]

/-- `mkInter A B` is nullable exactly when both `A` and `B` are. -/
theorem nullable_mkInter (A B : EreqNorm α n) :
    nullable (mkInter A B) = (nullable A && nullable B) := by
  by_cases bl : A = bot
  · simp [bl, nullable]
  by_cases br : B = bot
  · simp [br, nullable]
  rw [mkInter_eq_inter bl br, nullable]

/-- `normalise` preserves nullability. -/
theorem nullable_normalise (e : EreqAtomic α n) :
    nullable (normalise e) = EreqAtomic.nullable e := by
  induction e with
  | union l r ihl ihr =>
    simp only [normalise]
    rw [nullable_mkUnion (wellFormed_of_normalise l), ihl, ihr]
    rfl
  | intersection l r ihl ihr =>
    simp only [normalise, nullable_mkInter, ihl, ihr, EreqAtomic.nullable]
  | concatenation l r ihl ihr =>
    simp only [normalise, nullable_mkCat, ihl, ihr, EreqAtomic.nullable]
  | _ => simp_all [normalise, nullable, EreqAtomic.nullable]

end Null

end EreqNorm

/-! ## The derivative on normal forms -/

/-- A `DerTree` with `EreqNorm` leaves. -/
abbrev DerTreeNorm (α : Type*) (n : Nat) := BitTree α n (EreqNorm α n)

namespace EreqNorm

section Def

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ] [DecidableSat α] [DecidableEq α]

/-- Existential projection that joins the two branches with the smart union `⋓'`. -/
abbrev liftUExists : DerTreeNorm α (n + 1) → DerTreeNorm α n :=
  liftUProj (· ⋓' ·) (∃ₙ ·)

mutual

/-- The symbolic derivative on normal forms, which follows `EreqAtomic.derivative` but builds
    with the smart constructors so that every leaf is again a normal form. -/
def derivative : EreqNorm α n → DerTreeNorm α n
  | .ε => leaf (leaf bot)
  | .pred (.p i) => .node i (leaf (leaf .ε)) (leaf (leaf bot))
  | .pred (.notP i) => .node i (leaf (leaf bot)) (leaf (leaf .ε))
  | .pred (.pred φ) => leaf (.node φ (leaf .ε) (leaf bot))
  | ⋃ₙ[x, y | zs] => liftBinaryNorm (· ⋓' ·) (derivative x) (derivativeUnion y zs)
  | l ⋒ₙ r => liftBinaryNorm mkInter (derivative l) (derivative r)
  | l ⬝ₙ r =>
    if nullable l then
      liftBinaryNorm (· ⋓' ·) (liftUnaryNorm (mkCat · r) (derivative l)) (derivative r)
    else
      liftUnaryNorm (mkCat · r) (derivative l)
  | r★ₙ => liftUnaryNorm (mkCat · r★ₙ) (derivative r)
  | ~ₙ r => liftUnaryNorm (~ₙ ·) (derivative r)
  | ∃ₙ r => liftUExists (derivative r)
termination_by r => sizeOf r

/-- Derivative of an operand list, folded with `mkUnion`. -/
def derivativeUnion : EreqNorm α n → EreqNormList α n → DerTreeNorm α n
  | x, .nil => derivative x
  | x, .cons y ys => liftBinaryNorm (· ⋓' ·) (derivative x) (derivativeUnion y ys)
termination_by x xs => sizeOf x + sizeOf xs

end

scoped prefix:max " ρₙ " => EreqNorm.derivative

/-! ## The derivative tree tests its bits in order -/

mutual

theorem ordered_derivative {r : EreqNorm α n} : TTerm.Ordered (ρₙ r) := by
  match r with
  | .ε | .pred (.pred _) => simp only [derivative]; exact Ordered.base
  | .pred (.p i) | .pred (.notP i) =>
    simp only [derivative]; exact .ind .base .base .base .base
  | ⋃ₙ[x, y | zs] =>
    simp only [derivative]
    exact ordered_liftBinaryNorm ordered_derivative ordered_derivativeUnion (· ⋓' ·)
  | l ⋒ₙ r =>
    simp only [derivative]
    exact ordered_liftBinaryNorm ordered_derivative ordered_derivative mkInter
  | l ⬝ₙ r =>
    by_cases g : nullable l
    · rw [derivative, ite_eq_left g]
      exact ordered_liftBinaryNorm
        (ordered_liftUnaryNorm (ordered_derivative (r := l)) (mkCat · r)) ordered_derivative
        (· ⋓' ·)
    · rw [derivative, ite_eq_right g]
      exact ordered_liftUnaryNorm ordered_derivative (mkCat · r)
  | r★ₙ =>
    simp only [derivative]; exact ordered_liftUnaryNorm ordered_derivative (mkCat · r★ₙ)
  | ~ₙ r =>
    simp only [derivative]; exact ordered_liftUnaryNorm ordered_derivative (~ₙ ·)
  | ∃ₙ r =>
    simp only [derivative]; exact ordered_liftUProj (· ⋓' ·) (∃ₙ ·) ordered_derivative
termination_by sizeOf r

theorem ordered_derivativeUnion {x : EreqNorm α n} {xs : EreqNormList α n} :
    TTerm.Ordered (derivativeUnion x xs) := by
  match xs with
  | .nil => simpa [derivativeUnion] using ordered_derivative (r := x)
  | .cons y ys =>
    simp only [derivativeUnion]
    exact ordered_liftBinaryNorm ordered_derivative ordered_derivativeUnion (· ⋓' ·)
termination_by sizeOf x + sizeOf xs

end

/-- On an ordered tree, `liftUExists` gives the smart union of the results for the last bit set
    to `true` and to `false`. Unlike `EreqAtomic.liftUProj_eval_sim`, this holds exactly and not
    only up to `≅`. -/
theorem liftUExists_eval {x : Elem σ n} {f : DerTreeNorm α (n + 1)}
    (h : TTerm.Ordered f)
    (hwf1 : WellFormed (f[⟨x.1, x.2.snoc true⟩]ₙ))
    (hwf0 : WellFormed (f[⟨x.1, x.2.snoc false⟩]ₙ)) :
    (liftUExists f)[x]ₙ
      = (∃ₙ (f[⟨x.1, x.2.snoc true⟩]ₙ)) ⋓' (∃ₙ (f[⟨x.1, x.2.snoc false⟩]ₙ)) := by
  match f, h with
  | leaf t, _ =>
    simp only [eval₂_leaf] at hwf1
    simp only [liftUProj_leaf, eval₂_leaf, eval_liftUnary]
    exact (mkUnion_idem (.existential hwf1)).symm
  | .node ⟨c, p⟩ f1 f0, h =>
    let .ind hn1 hn0 hl1 hl0 := h
    by_cases eq : c = n
    · subst eq
      simp only [liftUProj_node, ↓reduceDIte]
      rw [eval_liftBinaryNorm]
      have ht : (x.2.snoc true)[c] = true := List.Vector.getElem_snoc_last
      have hf : (x.2.snoc false)[c] = false := List.Vector.getElem_snoc_last
      simp only [eval₂_node, models_fin, Fin.getElem_fin, ht, hf, Bool.false_eq_true,
        ↓reduceIte]
      rw [eval_liftUProj_of_below _ _ hl1 x true, eval_liftUProj_of_below _ _ hl0 x false]
    · have hlt : c < n := by omega
      have hsnoc_t : (x.2.snoc true)[c] = x.2[c] := List.Vector.getElem_snoc_lt hlt
      have hsnoc_f : (x.2.snoc false)[c] = x.2[c] := List.Vector.getElem_snoc_lt hlt
      simp only [liftUProj_node, eq, ↓reduceDIte]
      by_cases eq2 : x.2[c] = true
      · simp only [eval₂_node, models_fin, Fin.coe_castPred, Fin.getElem_fin,
          hsnoc_t, hsnoc_f, eq2] at hwf1 hwf0 ⊢
        exact liftUExists_eval hn1 hwf1 hwf0
      · simp only [eval₂_node, models_fin, Fin.coe_castPred, Fin.getElem_fin,
          hsnoc_t, hsnoc_f, eq2, Bool.false_eq_true] at hwf1 hwf0 ⊢
        exact liftUExists_eval hn0 hwf1 hwf0

/-! ## Well-formedness is preserved -/

mutual

theorem derivative_eval_wf {r : EreqNorm α n} (h : WellFormed r) (c : Elem σ n) :
    WellFormed ((ρₙ r)[c]ₙ) := by
  match r, h with
  | .ε, _ => simp only [derivative]; exact .pred _
  | .pred p, _ =>
    cases p <;>
      simp only [derivative, eval₂_node, eval₂_leaf, models_fin, eval_node] <;>
      split <;> first | exact .ε | exact .pred _
  | ⋃ₙ[x, y | zs], .union hwf _ _ =>
    simp only [derivative, eval_liftBinaryNorm]
    exact wellFormed_mkUnion (derivative_eval_wf (hwf x (by simp)) c)
      (derivativeUnion_eval_wf (hwf y (by simp)) (fun z hz => hwf z (by simp [hz])) c)
  | l ⋒ₙ r, .intersection hl hr =>
    simp only [derivative, eval_liftBinaryNorm]
    exact wellFormed_mkInter (derivative_eval_wf hl c) (derivative_eval_wf hr c)
  | l ⬝ₙ r, .concatenation hl hr =>
    by_cases hn : nullable l
    · rw [derivative, ite_eq_left hn]
      simp only [eval_liftBinaryNorm, eval_liftUnaryNorm]
      exact wellFormed_mkUnion (wellFormed_mkCat (derivative_eval_wf hl c) hr)
        (derivative_eval_wf hr c)
    · rw [derivative, ite_eq_right hn]
      simp only [eval_liftUnaryNorm]
      exact wellFormed_mkCat (derivative_eval_wf hl c) hr
  | r★ₙ, .star hr =>
    simp only [derivative, eval_liftUnaryNorm]
    exact wellFormed_mkCat (derivative_eval_wf hr c) (.star hr)
  | ~ₙ r, .negation hr =>
    simp only [derivative, eval_liftUnaryNorm]
    exact .negation (derivative_eval_wf hr c)
  | ∃ₙ r, .existential hr =>
    have h₁ := derivative_eval_wf hr ⟨c.1, c.2.snoc true⟩
    have h₀ := derivative_eval_wf hr ⟨c.1, c.2.snoc false⟩
    simp only [derivative]
    rw [liftUExists_eval ordered_derivative h₁ h₀]
    exact wellFormed_mkUnion (.existential h₁) (.existential h₀)
termination_by sizeOf r

theorem derivativeUnion_eval_wf {x : EreqNorm α n} {xs : EreqNormList α n}
    (hx : WellFormed x) (h : ∀ z ∈ xs.toList, WellFormed z) (c : Elem σ n) :
    WellFormed ((derivativeUnion x xs)[c]ₙ) := by
  match xs with
  | .nil => simpa [derivativeUnion] using derivative_eval_wf hx c
  | .cons y ys =>
    simp only [derivativeUnion, eval_liftBinaryNorm]
    exact wellFormed_mkUnion (derivative_eval_wf hx c)
      (derivativeUnion_eval_wf (h y (by simp)) (fun z hz => h z (by simp [hz])) c)
termination_by sizeOf x + sizeOf xs

end

/-! ## Normalisation commutes with derivatives

The interesting case is `∃ₙ`. There the `EreqAtomic` derivative matches the
`EreqNorm` one only up to `≅`, and `normalise_correctness` turns this into an equality. -/

/-- The derivative of an operand list is the `⋓'`-fold of the operands' derivatives. -/
theorem eval_derivativeUnion (x : EreqNorm α n) (xs : EreqNormList α n) (c : Elem σ n) :
    (derivativeUnion x xs)[c]ₙ
      = unionAll ((ρₙ x)[c]ₙ) (xs.toList.map (fun w => (ρₙ w)[c]ₙ)) := by
  match xs with
  | .nil => simp [derivativeUnion]
  | .cons y ys =>
    rw [derivativeUnion, eval_liftBinaryNorm, eval_derivativeUnion y ys, toList_cons,
      List.map_cons, unionAll_cons]
termination_by sizeOf xs

/-- The derivative of any normal form is the fold over its operand list. -/
theorem eval_derivative_toList (r : EreqNorm α n) (c : Elem σ n) :
    (ρₙ r)[c]ₙ = unionAll ((ρₙ r.first)[c]ₙ) (r.rest.map (fun w => (ρₙ w)[c]ₙ)) := by
  cases r with
  | union x y zs =>
    rw [derivative, eval_liftBinaryNorm, eval_derivativeUnion]
    simp
  | _ => simp

/-- The derivative of `a ⋓' b` is the smart union of the derivatives of `a` and `b`. -/
theorem derivative_mkUnion {a b : EreqNorm α n} (ha : WellFormed a) (hb : WellFormed b)
    (c : Elem σ n) :
    (ρₙ (a ⋓' b))[c]ₙ = (ρₙ a)[c]ₙ ⋓' (ρₙ b)[c]ₙ := by
  by_cases hna : a = bot
  · subst hna; simp [derivative]
  by_cases hnb : b = bot
  · subst hnb; simp [derivative]
  have hwf : ∀ w ∈ a.first :: (a.rest ++ toList b), WellFormed ((ρₙ w)[c]ₙ) := fun w hw =>
    derivative_eval_wf (mem_toList_append ha hb hw).1 c
  -- The operands of `a ⋓' b` are those of `a` and `b`, deduplicated
  obtain ⟨hf, hr⟩ : (a ⋓' b).first = a.first ∧
      (a ⋓' b).rest = List.eraseAll a.first (smartDedup (a.rest ++ toList b)) := by
    have h := toList_mkUnion ha hna hnb
    rw [toList_append_eq, smartDedup_cons] at h
    exact List.cons_eq_cons.mp h
  -- The derivative of a union is the union of the derivatives of its operands
  rw [eval_derivative_toList (a ⋓' b) c, hf, hr]
  -- Removing the later copies of `a.first` does not change the union
  have hwf' : ∀ w ∈ a.first :: ([] ++ smartDedup (a.rest ++ toList b)),
      WellFormed ((ρₙ w)[c]ₙ) := by
    simpa [mem_smartDedup_iff] using hwf
  rw [← List.nil_append (List.eraseAll _ _)]
  rw [unionAll_map_eraseAll (fun w => (ρₙ w)[c]ₙ) hwf' (by simp)]
  rw [List.nil_append]
  -- Removing the remaining duplicates does not change the union either
  rw [unionAll_map_smartDedup (fun w => (ρₙ w)[c]ₙ) hwf]
  -- Split the operands into those of `a` and those of `b`
  have hwf_a : ∀ z ∈ a.rest.map (fun w => (ρₙ w)[c]ₙ), WellFormed z := by
    simpa using fun w hw => hwf w (by simp [hw])
  rw [toList_eq b, List.map_append, List.map_cons]
  rw [unionAll_append (hwf _ List.mem_cons_self) hwf_a]
  -- Each half is the derivative of `a` or of `b`
  rw [← eval_derivative_toList a c, ← eval_derivative_toList b c]

/-- The derivative of `mkInter A B` is the smart intersection of their derivatives. -/
theorem derivative_mkInter (A B : EreqNorm α n) (c : Elem σ n) :
    (ρₙ (mkInter A B))[c]ₙ = mkInter ((ρₙ A)[c]ₙ) ((ρₙ B)[c]ₙ) := by
  by_cases bl : A = bot
  · subst bl; simp [derivative]
  by_cases br : B = bot
  · subst br; simp [derivative]
  rw [mkInter_eq_inter bl br, derivative, eval_liftBinaryNorm]

/-- The derivative of `mkCat A B` follows the concatenation rule with smart constructors.
    The `A = ε` case needs `mkUnion_bot_left`. -/
theorem derivative_mkCat (A B : EreqNorm α n) (c : Elem σ n) :
    (ρₙ (mkCat A B))[c]ₙ =
      if nullable A then mkCat ((ρₙ A)[c]ₙ) B ⋓' (ρₙ B)[c]ₙ
      else mkCat ((ρₙ A)[c]ₙ) B := by
  by_cases bl : A = bot
  · subst bl; simp [derivative, nullable]
  by_cases br : B = bot
  · subst br; simp [derivative]
  by_cases el : A = ε
  · subst el; simp [derivative, nullable]
  by_cases er : B = ε
  · subst er; simp [derivative]
  rw [mkCat_eq_cat bl br el er]
  by_cases hn : nullable A
  · rw [derivative, ite_eq_left hn, ite_eq_left hn]
    simp only [eval_liftBinaryNorm, eval_liftUnaryNorm]
  · rw [derivative, ite_eq_right hn, ite_eq_right hn]
    simp only [eval_liftUnaryNorm]

/-- The derivative of `normalise y` is the normal form of the derivative of `y`. -/
theorem derivative_normalise (y : EreqAtomic α n) (c : Elem σ n) :
    (ρₙ (normalise y))[c]ₙ = normalise ((ρ y)[c]ₙ) := by
  match y with
  | .ε => simp [normalise, derivative, EreqAtomic.derivative, EreqAtomic.bot]
  | .pred (.p i) | .pred (.notP i) =>
    simp only [normalise, derivative, EreqAtomic.derivative, eval₂_node, models_fin,
      eval₂_leaf, eval_leaf]
    split_ifs <;> simp [normalise]
  | .pred (.pred φ) =>
    simp only [normalise, derivative, EreqAtomic.derivative, eval₂_leaf, eval_node]
    split_ifs <;> simp [normalise, EreqAtomic.bot]
  | l ⋓ₐ r =>
    simp only [normalise, EreqAtomic.derivative, eval_liftBinaryNorm]
    rw [derivative_mkUnion (wellFormed_of_normalise l) (wellFormed_of_normalise r),
      derivative_normalise l c, derivative_normalise r c]
  | l ⋒ₐ r =>
    simp only [normalise, EreqAtomic.derivative, eval_liftBinaryNorm]
    rw [derivative_mkInter, derivative_normalise l c, derivative_normalise r c]
  | l ⬝ₐ r =>
    simp only [normalise]
    rw [derivative_mkCat, nullable_normalise l]
    by_cases h : EreqAtomic.nullable l
    · rw [ite_eq_left h, EreqAtomic.derivative, ite_eq_left h]
      simp only [eval_liftBinaryNorm, eval_liftUnaryNorm, normalise,
        derivative_normalise l c, derivative_normalise r c]
    · rw [ite_eq_right h, EreqAtomic.derivative, ite_eq_right h]
      simp only [eval_liftUnaryNorm, normalise, derivative_normalise l c]
  | r★ₐ =>
    simp only [normalise, derivative, EreqAtomic.derivative, eval_liftUnaryNorm,
      derivative_normalise r c, normalise]
  | ~ₐ r =>
    simp only [normalise, derivative, EreqAtomic.derivative, eval_liftUnaryNorm,
      derivative_normalise r c]
  | ∃ₐ r =>
    simp only [normalise, derivative, EreqAtomic.derivative]
    rw [liftUExists_eval ordered_derivative
      (derivative_eval_wf (wellFormed_of_normalise r) ⟨c.1, c.2.snoc true⟩)
      (derivative_eval_wf (wellFormed_of_normalise r) ⟨c.1, c.2.snoc false⟩)]
    rw [normalise_correctness
      (EreqAtomic.liftUProj_eval_sim (EreqAtomic.ordered_derivative (r := r)) c)]
    simp only [normalise]
    rw [derivative_normalise r ⟨c.1, c.2.snoc true⟩,
      derivative_normalise r ⟨c.1, c.2.snoc false⟩]
termination_by sizeOf y

/-- Derivatives of an output of `normalise` are again outputs of `normalise`. -/
theorem IsNormal.derivative {s : EreqNorm α n} (h : IsNormal s) (c : Elem σ n) :
    IsNormal ((ρₙ s)[c]ₙ) := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨(ρ e)[c]ₙ, (derivative_normalise e c).symm⟩

/-- A normal form accepts `c :: w` exactly when its derivative by `c` accepts `w`. -/
theorem deriv_iff_normalise (e : EreqAtomic α n) (c : Elem σ n) (w : Word σ n) :
    c :: w ∈ (normalise e).lang ↔ w ∈ ((ρₙ (normalise e))[c]ₙ).lang := by
  rw [derivative_normalise]
  exact (matches_normalise e (c :: w)).trans
    (EreqAtomic.cons_matches_iff.trans (matches_normalise _ w).symm)

end Def

end EreqNorm
