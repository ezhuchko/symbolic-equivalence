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

/-- A word is in the language of `unionOf es` exactly when it is in the language of some
    member of `es`. -/
theorem Ere.mem_lang_unionOf {w : List σ} :
    ∀ es : List (Ere α), w ∈ (Ere.unionOf es).lang ↔ ∃ e ∈ es, w ∈ e.lang
  | [] => by simp [Ere.lang_pred_bot]
  | [a] => by simp
  | a :: b :: bs => by
    rw [Ere.unionOf_cons _ (List.cons_ne_nil b bs)]
    simp only [Ere.lang, Language.mem_add, Ere.mem_lang_unionOf (b :: bs), List.mem_cons]
    constructor
    · rintro (h | ⟨e, he, hw⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨e, Or.inr he, hw⟩
    · rintro ⟨e, (rfl | he), hw⟩
      · exact Or.inl hw
      · exact Or.inr ⟨e, he, hw⟩

namespace EreNorm

/-! ## The language of a normal form -/

/-- The language of a normal form is the language of the `Ere` it stands for. -/
def lang (s : EreNorm α) : Language σ := (reconvert s).lang

theorem lang_ε : ((ε : EreNorm α).lang : Language σ) = 1 := by
  simp only [EreNorm.lang, reconvert_ε, Ere.lang]

theorem lang_cat (l r : EreNorm α) : ((l ⬝ₙ r).lang : Language σ) = l.lang * r.lang := by
  simp only [EreNorm.lang, reconvert_cat, Ere.lang]

/-- A word is in the language of a union exactly when it is in the language of one of its
    operands. -/
theorem mem_lang_union {w : List σ} (x y : EreNorm α) (zs : List (EreNorm α)) :
    w ∈ (⋃ₙ[x, y | zs].lang : Language σ) ↔ ∃ e ∈ x :: y :: zs, w ∈ (e.lang : Language σ) := by
  simp only [EreNorm.lang, reconvert_union, Ere.mem_lang_unionOf, List.mem_map]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hw⟩; exact ⟨e, he, hw⟩
  · rintro ⟨e, he, hw⟩; exact ⟨_, ⟨e, he, rfl⟩, hw⟩

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
  by_cases hta : a = (pred ⊤)★ₙ
  · subst hta
    rw [mkUnion_topStar_left, reconvert_star, reconvert_pred, Ere.lang_pred_top_star]
    exact (top_sup_eq _).symm
  by_cases htb : b = (pred ⊤)★ₙ
  · subst htb
    rw [mkUnion_topStar_right, reconvert_star, reconvert_pred, Ere.lang_pred_top_star]
    exact (sup_top_eq _).symm
  rw [Ere.sim_lang_eq (reconvert_mkUnion_of_ne_bot hna hnb hta htb)]
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
  by_cases tl : a = (pred ⊤)★ₙ
  · subst tl
    rw [mkInter_topStar_left, reconvert_star, reconvert_pred, Ere.lang_pred_top_star]
    exact (top_inf_eq _).symm
  by_cases tr : b = (pred ⊤)★ₙ
  · subst tr
    rw [mkInter_topStar_right, reconvert_star, reconvert_pred, Ere.lang_pred_top_star]
    exact (inf_top_eq _).symm
  by_cases nl : b = ~ₙa
  · subst nl
    rw [mkInter_neg_right tl, reconvert_pred, Ere.lang_pred_bot, reconvert_neg]
    exact (Set.inter_compl_self _).symm
  by_cases nr : a = ~ₙb
  · subst nr
    rw [mkInter_neg_left tr, reconvert_pred, Ere.lang_pred_bot, reconvert_neg]
    exact (Set.compl_inter_self _).symm
  rw [mkInter_eq_inter bl br tl tr nl nr, reconvert_inter]
  rfl

/-- The language of `mkNeg a` is the complement of the language of `a`. -/
theorem lang_mkNeg (a : EreNorm α) : (mkNeg a).lang = ((a.lang : Language σ))ᶜ := by
  unfold EreNorm.lang
  by_cases hb : a = EreNorm.pred ⊥
  · subst hb
    simp only [mkNeg_bot, reconvert_star, reconvert_pred]
    rw [Ere.lang_pred_top_star, Ere.lang_pred_bot]
    exact compl_bot.symm
  · by_cases ht : a = (pred ⊤)★ₙ
    · subst ht
      simp only [mkNeg_topStar, reconvert_pred, reconvert_star]
      rw [Ere.lang_pred_top_star, Ere.lang_pred_bot]
      exact compl_top.symm
    · rw [mkNeg_eq_neg hb ht, reconvert_neg]
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
  | negation r ih =>
    simp only [normalise]
    rw[lang_mkNeg, ih, Ere.lang]
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
