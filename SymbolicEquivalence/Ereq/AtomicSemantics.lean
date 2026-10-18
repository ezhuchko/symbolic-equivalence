import SymbolicEquivalence.Ereq.NegationNormalForm
import SymbolicEquivalence.Ereq.Semantics
import SymbolicEquivalence.Ereq.Similarity

/-!
# Semantics of expressions with atomic predicates

`EreqAtomic.lang r` is the language of `r`, and `xs ⊫ₐ r` is membership in it. Similar
expressions denote the same language (`sim_lang_eq`), and making the predicates atomic with
`Ereq.nnf` does not change the language (`Ereq.lang_nnf`).
-/

open scoped Ereq EreqAtomic Computability
open EreqAtomic (Sim)

variable {α σ : Type*}

def EreqAtomic.lang [EffectiveBooleanAlgebra α σ] : EreqAtomic α n → Language (Elem σ n)
  | .ε      => 1
  | .pred φ => {xs | ∃ c, xs = [c] ∧ FundamentalPredicate.models φ c}
  | L ⋓ₐ R  => lang L + lang R
  | L ⋒ₐ R  => lang L ⊓ lang R
  | L ⬝ₐ R  => HMul.hMul (lang L) (lang R)
  | R★ₐ     => (lang R)∗
  | ~ₐR     => (lang R)ᶜ
  | ∃ₐ R    => {xs | ∃ (s : List.Vector Bool xs.length), Word.extend xs s ∈ lang R}

/-- The match semantics of `EreqAtomic`: membership in the denoted language. -/
def EreqAtomic.Matches [EffectiveBooleanAlgebra α σ] (xs : Word σ n) (R : EreqAtomic α n) : Prop :=
  xs ∈ R.lang

namespace EreqAtomic
scoped notation:52 lhs:53 " ⊫ₐ " rhs:53 => EreqAtomic.Matches lhs rhs
end EreqAtomic

section MatchesClauses
variable [EffectiveBooleanAlgebra α σ]

@[simp, matches_simps] theorem EreqAtomic.matches_eps {xs : Word σ n} :
    (xs ⊫ₐ (.ε : EreqAtomic α n)) ↔ xs = [] := Language.mem_one xs

/-- Not `@[simp]`, for the reason given at `Ereq.matches_pred`. -/
@[matches_simps] theorem EreqAtomic.matches_pred {xs : Word σ n} {φ : FundamentalPredicate α n} :
    (xs ⊫ₐ .pred φ) ↔ ∃ c, xs = [c] ∧ FundamentalPredicate.models φ c := Iff.rfl

@[simp] theorem EreqAtomic.matches_pred_nil {φ : FundamentalPredicate α n} :
    ¬ (([] : Word σ n) ⊫ₐ .pred φ) := by
  simp only [EreqAtomic.matches_pred]; rintro ⟨_, ⟨⟩, _⟩

@[simp] theorem EreqAtomic.matches_pred_cons {x : Elem σ n} {xs : Word σ n}
    {φ : FundamentalPredicate α n} :
    ((x :: xs) ⊫ₐ .pred φ) ↔ xs = [] ∧ FundamentalPredicate.models φ x := by
  simp only [EreqAtomic.matches_pred, List.cons.injEq, and_assoc, exists_eq_left']

/-- No word matches `bot`. -/
@[simp] theorem EreqAtomic.not_matches_bot {xs : Word σ n} :
    ¬ (xs ⊫ₐ (EreqAtomic.bot : EreqAtomic α n)) := by
  rintro ⟨c, -, h⟩
  simp [FundamentalPredicate.models] at h

@[simp, matches_simps] theorem EreqAtomic.matches_union {xs : Word σ n} {L R : EreqAtomic α n} :
    (xs ⊫ₐ (L ⋓ₐ R)) ↔ (xs ⊫ₐ L) ∨ (xs ⊫ₐ R) := Language.mem_add _ _ _

@[simp, matches_simps] theorem EreqAtomic.matches_inter {xs : Word σ n} {L R : EreqAtomic α n} :
    (xs ⊫ₐ (L ⋒ₐ R)) ↔ (xs ⊫ₐ L) ∧ (xs ⊫ₐ R) := Iff.rfl

@[simp, matches_simps] theorem EreqAtomic.matches_cat {xs : Word σ n} {L R : EreqAtomic α n} :
    (xs ⊫ₐ (L ⬝ₐ R)) ↔ ∃ (ys zs : Word σ n), (ys ⊫ₐ L) ∧ (zs ⊫ₐ R) ∧ xs = ys ++ zs := by
  simp only [EreqAtomic.Matches, EreqAtomic.lang, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

@[simp, matches_simps] theorem EreqAtomic.matches_neg {xs : Word σ n} {R : EreqAtomic α n} :
    (xs ⊫ₐ ~ₐR) ↔ ¬ (xs ⊫ₐ R) := Iff.rfl

@[simp, matches_simps] theorem EreqAtomic.matches_ex {xs : Word σ n} {R : EreqAtomic α (n + 1)} :
    (xs ⊫ₐ ∃ₐ R) ↔ ∃ (s : List.Vector Bool xs.length), (Word.extend xs s) ⊫ₐ R := Iff.rfl

/-- The language of a bounded repetition is the corresponding language power. -/
theorem EreqAtomic.lang_repeatCat (R : EreqAtomic α n) (m : Nat) :
    (R ⁽ m ⁾ₐ).lang = (R.lang : Language (Elem σ n)) ^ m := by
  induction m with
  | zero => exact (pow_zero _).symm
  | succ m ih =>
    change HMul.hMul R.lang (R ⁽ m ⁾ₐ).lang = _
    rw [ih, pow_succ']

@[simp, matches_simps] theorem EreqAtomic.matches_star {xs : Word σ n} {R : EreqAtomic α n} :
    (xs ⊫ₐ R★ₐ) ↔ ∃ m, xs ⊫ₐ (R ⁽ m ⁾ₐ) := by
  simp only [EreqAtomic.Matches, EreqAtomic.lang]
  rw [Language.kstar_eq_iSup_pow, Language.mem_iSup]
  exact exists_congr fun m => by rw [lang_repeatCat]

end MatchesClauses

namespace EreqAtomic
variable [EffectiveBooleanAlgebra α σ]

/-- No word matches `bot`. -/
theorem lang_bot : (EreqAtomic.lang (EreqAtomic.bot : EreqAtomic α n) : Language (Elem σ n)) = 0 :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ => EreqAtomic.not_matches_bot

theorem lang_eps : (EreqAtomic.lang (.ε : EreqAtomic α n) : Language (Elem σ n)) = 1 := rfl

/-- Similar expressions denote the same language. -/
theorem sim_lang_eq {a b : EreqAtomic α n} (h : a ≅ b) :
    (a.lang : Language (Elem σ n)) = b.lang := by
  induction h with
  | refl => rfl
  | idem | assoc | dedup => ext x; simp only [EreqAtomic.lang, Language.mem_add]; tauto
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | union_cong _ _ ih1 ih2 | inter_cong _ _ ih1 ih2 | cat_cong _ _ ih1 ih2 =>
    simp only [EreqAtomic.lang, ih1, ih2]
  | neg_cong _ ih | star_cong _ ih => simp only [EreqAtomic.lang, ih]
  | exists_cong _ ih => simp only [EreqAtomic.lang]; rw [ih]

end EreqAtomic

/-! ### Normalisation preserves the semantics -/

section NnfPreservesMatches
variable [EffectiveBooleanAlgebra α σ]

/-- An externalised predicate matches exactly the one-letter words satisfying it. -/
theorem PExtensionNNF.matches_externaliseNnf {xs : Word σ n} (p : PExtensionNNF α n) :
    xs ⊫ₐ p.externaliseNnf ↔ ∃ c, xs = [c] ∧ p.models c := by
  induction p generalizing xs with
  | and p q ihp ihq =>
    simp only [PExtensionNNF.externaliseNnf, EreqAtomic.matches_inter, ihp, ihq]
    rcases xs with _ | ⟨c, _ | _⟩ <;> simp
  | or p q ihp ihq =>
    simp only [PExtensionNNF.externaliseNnf, EreqAtomic.matches_union, ihp, ihq]
    rcases xs with _ | ⟨c, _ | _⟩ <;> simp
  | _ => simp [matches_simps]

theorem PExtension.ext_pred_nnf_correct {xs : Word σ n} (e : PExtension α n) :
    xs ⊫ₐ e.nnfp.externaliseNnf ↔ xs ⊫ .pred e := by
  simp [PExtensionNNF.matches_externaliseNnf, Ereq.matches_pred, PExtension.nnfp_correct]

/-- Predicate normalisation does not change the language. -/
theorem Ereq.lang_nnf (R : Ereq α n) :
    ((Ereq.nnf R).lang : Language (Elem σ n)) = R.lang :=
  match R with
  | .pred e => Set.ext fun _ => e.ext_pred_nnf_correct
  | .ε => rfl
  | l ⋓ r | l ⋒ r | l ⬝ r => by
    simp only [Ereq.nnf, EreqAtomic.lang, Ereq.lang, lang_nnf l, lang_nnf r]
  | r★ | ~r => by simp only [Ereq.nnf, EreqAtomic.lang, Ereq.lang, lang_nnf r]
  | ∃ʳ r => by simp only [Ereq.nnf, EreqAtomic.lang, Ereq.lang, lang_nnf r]; rfl

theorem Ereq.matches_nnf (R : Ereq α n) {xs : Word σ n} : (Ereq.nnf R).Matches xs ↔ xs ⊫ R := by
  rw [EreqAtomic.Matches, Ereq.lang_nnf]; rfl

end NnfPreservesMatches
