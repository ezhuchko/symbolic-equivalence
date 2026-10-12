import SymbolicEquivalence.EffectiveBooleanAlgebra
import SymbolicEquivalence.Ere.Syntax
import SymbolicEquivalence.Ere.Similarity
import Mathlib.Computability.Language

/-!
# Semantics of extended regular expressions

`Ere.lang r` is the language `r` denotes, as a Mathlib `Language σ`, and `xs ⊫ r` is
membership in it. -/

open scoped Computability Models

namespace Ere

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

def lang : Ere α → Language σ
  | ε => 1
  | pred p => {xs | ∃ c, xs = [c] ∧ c ⊨ p}
  | l ⋓ r => lang l + lang r
  | l ⋒ r => lang l ⊓ lang r
  | l ⬝ r => lang l * lang r
  | r★ => (lang r)∗
  | ~ r => (lang r)ᶜ

/-- `xs ⊫ r` holds exactly when `xs` is in the language of `r`. -/
def Matches (xs : List σ) (r : Ere α) : Prop := xs ∈ r.lang

scoped notation:52 lhs:53 " ⊫ " rhs:53 => Ere.Matches lhs rhs

@[simp] theorem matches_eps {xs : List σ} : (xs ⊫ (ε : Ere α)) ↔ xs = [] :=
  Language.mem_one xs

@[simp] theorem matches_pred {xs : List σ} {p : α} :
    (xs ⊫ pred p) ↔ ∃ c, xs = [c] ∧ c ⊨ p := Iff.rfl

@[simp] theorem matches_union {xs : List σ} {l r : Ere α} :
    (xs ⊫ (l ⋓ r)) ↔ (xs ⊫ l) ∨ (xs ⊫ r) :=
  Language.mem_add _ _ _

@[simp] theorem matches_inter {xs : List σ} {l r : Ere α} :
    (xs ⊫ (l ⋒ r)) ↔ (xs ⊫ l) ∧ (xs ⊫ r) := Iff.rfl

@[simp] theorem matches_cat {xs : List σ} {l r : Ere α} :
    (xs ⊫ (l ⬝ r)) ↔ ∃ u₁ u₂, (u₁ ⊫ l) ∧ (u₂ ⊫ r) ∧ u₁ ++ u₂ = xs := by
  simp only [Matches, lang, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

@[simp] theorem matches_neg {xs : List σ} {r : Ere α} : (xs ⊫ ~r) ↔ ¬ (xs ⊫ r) := Iff.rfl

/-- The language of a bounded repetition is the corresponding power. -/
theorem lang_repeatCat (r : Ere α) (n : ℕ) : (r⁽n⁾).lang = (r.lang : Language σ) ^ n := by
  induction n with
  | zero => exact (pow_zero _).symm
  | succ n ih =>
    change r.lang * (r⁽n⁾).lang = _
    rw [ih, pow_succ']

@[simp] theorem matches_star {xs : List σ} {r : Ere α} : (xs ⊫ r★) ↔ ∃ m, xs ⊫ r⁽m⁾ := by
  simp only [Matches, lang]
  rw [Language.kstar_eq_iSup_pow, Language.mem_iSup]
  exact exists_congr fun m => by rw [lang_repeatCat]

/-- No word matches `pred ⊥`. -/
theorem not_mem_lang_pred_bot {x : List σ} : x ∉ (Ere.lang (pred (⊥ : α)) : Language σ) := by
  rintro ⟨c, rfl, hc⟩; simp at hc

theorem lang_pred_bot : (Ere.lang (Ere.pred (⊥ : α)) : Language σ) = 0 :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ => not_mem_lang_pred_bot

theorem lang_eps : (Ere.lang (Ere.ε : Ere α) : Language σ) = 1 := rfl

/-- Similar expressions denote the same language. -/
theorem sim_lang_eq {p q : Ere α} (h : p ≅ q) : (p.lang : Language σ) = q.lang := by
  induction h with
  | refl => rfl
  | idem | assoc | dedup => ext x; simp only [Ere.lang, Language.mem_add]; tauto
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | union_cong _ _ ih1 ih2 | inter_cong _ _ ih1 ih2 | cat_cong _ _ ih1 ih2 =>
    simp only [Ere.lang, ih1, ih2]
  | star_cong _ ih | neg_cong _ ih => simp only [Ere.lang, ih]

end Ere
