import SymbolicEquivalence.Ere.Semantics
import SymbolicEquivalence.Ere.NormalForm.Normalise
import SymbolicEquivalence.Ere.NormalForm.Reconvert

/-!
# The language of a normal form

The language of a normal form is the language of its `reconvert` (`EreNorm.lang`). Each smart
constructor computes the matching operation on `Language σ` (`lang_mkUnion`, `lang_mkCat`,
`lang_mkInter`), so `normalise` preserves the language (`lang_normalise`).

These results are language equalities rather than `≅`, because the smart constructors simplify
more than `≅` allows. The simplifications hold on languages, since `⊥` denotes `0` and `ε`
denotes `1`.
-/

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]
open scoped Ere EreNorm Computability

namespace EreNorm

/-! ## The language of a normal form -/

/-- The language of a normal form is the language of the `Ere` it stands for. -/
def lang (s : EreNorm α) : Language σ := (reconvert s).lang

theorem lang_star (s : EreNorm α) : (s★ₙ).lang = ((s.lang : Language σ))∗ := by
  simp only [EreNorm.lang, reconvert_star, Ere.lang]

theorem lang_neg (s : EreNorm α) : (~ₙ s).lang = ((s.lang : Language σ))ᶜ := by
  simp only [EreNorm.lang, reconvert_neg, Ere.lang]

theorem lang_xor (s t : EreNorm α) :
    (EreNorm.xor s t).lang = symmDiff (s.lang : Language σ) t.lang := by
  simp only [EreNorm.lang, reconvert_xor, Ere.lang]

/-! ## Languages of the smart constructors -/

section SmartConstructors

variable [DecidableEq α]

/-- The language of `a ⋓' b` is the union of the languages of `a` and `b`. -/
theorem lang_mkUnion (a b : EreNorm α) :
    (a ⋓' b).lang = (a.lang + b.lang : Language σ) := by
  unfold EreNorm.lang
  by_cases hna : a = EreNorm.pred ⊥
  · subst hna; rw [mkUnion_bot_left, reconvert_pred, Ere.lang_pred_bot, zero_add]
  by_cases hnb : b = EreNorm.pred ⊥
  · subst hnb; rw [mkUnion_bot_right, reconvert_pred, Ere.lang_pred_bot, add_zero]
  rw [Ere.sim_lang_eq (reconvert_mkUnion_of_ne_bot hna hnb)]
  rfl

/-- The language of `mkCat a b` is the concatenation of their languages. Its simplifications
    correspond to `zero_mul`, `mul_zero`, `one_mul` and `mul_one`. -/
theorem lang_mkCat (a b : EreNorm α) :
    (mkCat a b).lang = (a.lang * b.lang : Language σ) := by
  unfold EreNorm.lang
  by_cases bl : a = EreNorm.pred ⊥
  · subst bl; rw [mkCat_bot_left, reconvert_pred, Ere.lang_pred_bot, zero_mul]
  by_cases br : b = EreNorm.pred ⊥
  · subst br; rw [mkCat_bot_right, reconvert_pred, Ere.lang_pred_bot, mul_zero]
  by_cases el : a = EreNorm.ε
  · subst el; rw [mkCat_eps_left, reconvert_ε, Ere.lang_eps, one_mul]
  by_cases er : b = EreNorm.ε
  · subst er; rw [mkCat_eps_right, reconvert_ε, Ere.lang_eps, mul_one]
  rw [mkCat_eq_cat bl br el er, reconvert_cat]
  rfl

/-- The language of `mkInter a b` is the intersection of their languages. The language `0`
    is the empty set, hence the `Set` lemmas. -/
theorem lang_mkInter (a b : EreNorm α) :
    (mkInter a b).lang = (a.lang ⊓ b.lang : Language σ) := by
  unfold EreNorm.lang
  by_cases bl : a = EreNorm.pred ⊥
  · subst bl
    rw [mkInter_bot_left, reconvert_pred, Ere.lang_pred_bot]
    exact (Set.empty_inter _).symm
  by_cases br : b = EreNorm.pred ⊥
  · subst br
    rw [mkInter_bot_right, reconvert_pred, Ere.lang_pred_bot]
    exact (Set.inter_empty _).symm
  rw [mkInter_eq_inter bl br, reconvert_inter]
  rfl

/-- `normalise` does not change the language. -/
theorem lang_normalise (r : Ere α) : (normalise r).lang = (r.lang : Language σ) := by
  induction r with
  | ε => simp only [normalise, EreNorm.lang, reconvert_ε]
  | pred p => simp only [normalise, EreNorm.lang, reconvert_pred]
  | union l r ihl ihr =>
    simp only [normalise]
    rw [lang_mkUnion, ihl, ihr]; rfl
  | intersection l r ihl ihr =>
    simp only [normalise]
    rw [lang_mkInter, ihl, ihr]; rfl
  | concatenation l r ihl ihr =>
    simp only [normalise]
    rw [lang_mkCat, ihl, ihr]; rfl
  | star r ih => simp only [normalise, lang_star, ih, Ere.lang]
  | negation r ih => simp only [normalise, lang_neg, ih, Ere.lang]
  | xor l r ihl ihr => simp only [normalise, lang_xor, ihl, ihr, Ere.lang]

/-- The pointwise form of `lang_normalise`. -/
theorem matches_normalise (r : Ere α) (xs : List σ) :
    xs ∈ (normalise r).lang ↔ (xs ⊫ r) :=
  Language.ext_iff.mp (lang_normalise r) xs

/-- Expressions with the same normal form have the same language. -/
theorem lang_eq_of_normalise_eq {r₁ r₂ : Ere α} (h : normalise r₁ = normalise r₂) :
    (r₁.lang : Language σ) = r₂.lang := by
  rw [← lang_normalise r₁, ← lang_normalise r₂, h]

end SmartConstructors

end EreNorm
