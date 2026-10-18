import SymbolicEquivalence.Ereq.AtomicSemantics
import SymbolicEquivalence.Ereq.NormalForm.Normalise
import SymbolicEquivalence.Ereq.NormalForm.Reconvert

/-!
# The language of a normal form

The language of a normal form is the language of its `reconvert` (`EreqNorm.lang`). Each smart
constructor computes the matching operation on `Language (Elem σ n)` (`lang_mkUnion`,
`lang_mkCat`, `lang_mkInter`), so `normalise` preserves the language (`lang_normalise`).

These results are language equalities rather than `≅`, because the smart constructors simplify
more than `≅` allows. The simplifications hold on languages, since `bot` denotes `0` and `ε`
denotes `1`.
-/

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]
open scoped EreqAtomic EreqNorm Computability

namespace EreqNorm

/-! ## The language of a normal form -/

/-- The language of a normal form is the language of the `EreqAtomic` it stands for. -/
def lang (s : EreqNorm α n) : Language (Elem σ n) := (reconvert s).lang

theorem lang_star (s : EreqNorm α n) :
    (s★ₙ).lang = ((s.lang : Language (Elem σ n)))∗ := by
  simp only [EreqNorm.lang, reconvert_star, EreqAtomic.lang]

theorem lang_neg (s : EreqNorm α n) :
    (~ₙ s).lang = ((s.lang : Language (Elem σ n)))ᶜ := by
  simp only [EreqNorm.lang, reconvert_neg, EreqAtomic.lang]

theorem lang_ex (s : EreqNorm α (n + 1)) :
    ((∃ₙ s).lang : Language (Elem σ n))
      = {xs | ∃ (b : List.Vector Bool xs.length),
          Word.extend xs b ∈ (s.lang : Language (Elem σ (n + 1)))} := by
  simp only [EreqNorm.lang, reconvert_ex]; rfl

/-! ## Languages of the smart constructors -/

section SmartConstructors

variable [DecidableEq α]

/-- The language of `a ⋓' b` is the union of the languages of `a` and `b`. -/
theorem lang_mkUnion (a b : EreqNorm α n) :
    (a ⋓' b).lang = (a.lang + b.lang : Language (Elem σ n)) := by
  unfold EreqNorm.lang
  by_cases hna : a = bot
  · subst hna; rw [mkUnion_bot_left, reconvert_bot, EreqAtomic.lang_bot, zero_add]
  by_cases hnb : b = bot
  · subst hnb; rw [mkUnion_bot_right, reconvert_bot, EreqAtomic.lang_bot, add_zero]
  rw [EreqAtomic.sim_lang_eq (reconvert_mkUnion_of_ne_bot hna hnb)]
  rfl

/-- The language of `mkCat a b` is the concatenation of their languages. Its simplifications
    correspond to `zero_mul`, `mul_zero`, `one_mul` and `mul_one`. -/
theorem lang_mkCat (a b : EreqNorm α n) :
    (mkCat a b).lang = (a.lang * b.lang : Language (Elem σ n)) := by
  unfold EreqNorm.lang
  by_cases bl : a = bot
  · subst bl; rw [mkCat_bot_left, reconvert_bot, EreqAtomic.lang_bot, zero_mul]
  by_cases br : b = bot
  · subst br; rw [mkCat_bot_right, reconvert_bot, EreqAtomic.lang_bot, mul_zero]
  by_cases el : a = ε
  · subst el; rw [mkCat_eps_left, reconvert_ε, EreqAtomic.lang_eps, one_mul]
  by_cases er : b = ε
  · subst er; rw [mkCat_eps_right, reconvert_ε, EreqAtomic.lang_eps, mul_one]
  rw [mkCat_eq_cat bl br el er, reconvert_cat]
  rfl

/-- The language of `mkInter a b` is the intersection of their languages. The language `0`
    is the empty set, hence the `Set` lemmas. -/
theorem lang_mkInter (a b : EreqNorm α n) :
    (mkInter a b).lang = (a.lang ⊓ b.lang : Language (Elem σ n)) := by
  unfold EreqNorm.lang
  by_cases bl : a = bot
  · subst bl
    rw [mkInter_bot_left, reconvert_bot, EreqAtomic.lang_bot]
    exact (Set.empty_inter _).symm
  by_cases br : b = bot
  · subst br
    rw [mkInter_bot_right, reconvert_bot, EreqAtomic.lang_bot]
    exact (Set.inter_empty _).symm
  rw [mkInter_eq_inter bl br, reconvert_inter]
  rfl

/-- `normalise` does not change the language. -/
theorem lang_normalise (r : EreqAtomic α n) :
    (normalise r).lang = (r.lang : Language (Elem σ n)) := by
  induction r with
  | ε => simp only [normalise, EreqNorm.lang, reconvert_ε]
  | pred p => simp only [normalise, EreqNorm.lang, reconvert_pred]
  | union l r ihl ihr =>
    simp only [normalise]
    rw [lang_mkUnion, ihl, ihr]; rfl
  | intersection l r ihl ihr =>
    simp only [normalise]
    rw [lang_mkInter, ihl, ihr]; rfl
  | concatenation l r ihl ihr =>
    simp only [normalise]
    rw [lang_mkCat, ihl, ihr]; rfl
  | star r ih => simp only [normalise, lang_star, ih, EreqAtomic.lang]
  | negation r ih => simp only [normalise, lang_neg, ih, EreqAtomic.lang]
  | existential r ih =>
    simp only [normalise, lang_ex, EreqAtomic.lang]
    rw [ih]

/-- The pointwise form of `lang_normalise`. -/
theorem matches_normalise (r : EreqAtomic α n) (xs : Word σ n) :
    xs ∈ (normalise r).lang ↔ (xs ⊫ₐ r) :=
  Language.ext_iff.mp (lang_normalise r) xs

end SmartConstructors

end EreqNorm
