import SymbolicEquivalence.Ereq.Word
import SymbolicEquivalence.ListIndexHelpers
import SymbolicEquivalence.Ereq.Syntax
import Mathlib.Computability.Language

/-!
# Semantics of `Ereq`

Defines the language `Ereq.lang R` of a regex and the match relation `xs ⊫ R`, and proves
some properties about them.
-/

open scoped Ereq Computability

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

namespace Ereq

/-- The language denoted by an `Ereq`. -/
def lang : Ereq α n → Language (Elem σ n)
  | ε      => 1
  | pred φ => {xs | ∃ c, xs = [c] ∧ PExtension.models φ c}
  | L ⋓ R  => lang L + lang R
  | L ⋒ R  => lang L ⊓ lang R
  | L ⬝ R  => HMul.hMul (lang L) (lang R)
  | R★     => (lang R)∗
  | ~R     => (lang R)ᶜ
  | ∃ʳ R   => {xs | ∃ (s : List.Vector Bool xs.length), Word.extend xs s ∈ lang R}

theorem lang_union (L R : Ereq α n) : ((L ⋓ R).lang : Language (Elem σ n)) = L.lang + R.lang :=
  rfl
theorem lang_cat (L R : Ereq α n) : ((L ⬝ R).lang : Language (Elem σ n)) = L.lang * R.lang :=
  rfl
theorem lang_star (R : Ereq α n) : ((R★).lang : Language (Elem σ n)) = R.lang∗ := rfl

/-- The match semantics of `Ereq`: membership in the denoted language. -/
def Matches (xs : Word σ n) (R : Ereq α n) : Prop := xs ∈ R.lang

scoped notation:52 lhs:53 " ⊫ " rhs:53 => Ereq.Matches lhs rhs

section MatchesClauses

@[simp, matches_simps] theorem matches_eps {xs : Word σ n} :
    (xs ⊫ (ε : Ereq α n)) ↔ xs = [] := by
  simp only [Ereq.Matches, Ereq.lang]; exact Language.mem_one xs

/-- Not `@[simp]`, since `simp` would get stuck on `x :: xs`; use `matches_pred_nil` and
    `matches_pred_cons` instead. -/
@[matches_simps] theorem matches_pred {xs : Word σ n} {φ : PExtension α n} :
    (xs ⊫ pred φ) ↔ ∃ c, xs = [c] ∧ PExtension.models φ c := Iff.rfl

@[simp] theorem matches_pred_nil {φ : PExtension α n} :
    ¬ (([] : Word σ n) ⊫ pred φ) := by
  simp only [Ereq.matches_pred]; rintro ⟨_, ⟨⟩, _⟩

@[simp] theorem matches_pred_cons {x : Elem σ n} {xs : Word σ n} {φ : PExtension α n} :
    ((x :: xs) ⊫ pred φ) ↔ xs = [] ∧ PExtension.models φ x := by
  simp only [Ereq.matches_pred, List.cons.injEq, and_assoc, exists_eq_left']

@[simp, matches_simps] theorem matches_union {xs : Word σ n} {L R : Ereq α n} :
    (xs ⊫ (L ⋓ R)) ↔ (xs ⊫ L) ∨ (xs ⊫ R) := by
  simp only [Ereq.Matches, Ereq.lang]; exact Language.mem_add _ _ _

@[simp, matches_simps] theorem matches_inter {xs : Word σ n} {L R : Ereq α n} :
    (xs ⊫ (L ⋒ R)) ↔ (xs ⊫ L) ∧ (xs ⊫ R) := Iff.rfl

@[simp, matches_simps] theorem matches_cat {xs : Word σ n} {L R : Ereq α n} :
    (xs ⊫ (L ⬝ R)) ↔ ∃ (ys zs : Word σ n), (ys ⊫ L) ∧ (zs ⊫ R) ∧ xs = ys ++ zs := by
  simp only [Ereq.Matches, Ereq.lang, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

@[simp, matches_simps] theorem matches_neg {xs : Word σ n} {R : Ereq α n} :
    (xs ⊫ ~R) ↔ ¬ (xs ⊫ R) := Iff.rfl

@[simp, matches_simps] theorem matches_ex {xs : Word σ n} {R : Ereq α (n + 1)} :
    (xs ⊫ ∃ʳ R) ↔ ∃ (s : List.Vector Bool xs.length), (Word.extend xs s) ⊫ R := Iff.rfl

/-- The language of a bounded repetition is the corresponding language power. -/
theorem lang_repeatCat (R : Ereq α n) (m : Nat) :
    (R ⁽ m ⁾).lang = (R.lang : Language (Elem σ n)) ^ m := by
  induction m with
  | zero => exact (pow_zero _).symm
  | succ m ih =>
    change HMul.hMul R.lang (R ⁽ m ⁾).lang = _
    rw [ih, pow_succ']

@[simp, matches_simps] theorem matches_star {xs : Word σ n} {R : Ereq α n} :
    (xs ⊫ R★) ↔ ∃ m, xs ⊫ (R ⁽ m ⁾) := by
  simp only [Ereq.Matches, Ereq.lang]
  rw [Language.kstar_eq_iSup_pow, Language.mem_iSup]
  exact exists_congr fun m => by rw [lang_repeatCat]

end MatchesClauses

/-- Predicate `and` is regex intersection. -/
theorem and_intersection {xs : Word σ n} {q r : PExtension α n} :
    (xs ⊫ (Ereq.pred (.and q r)))
    ↔ (xs ⊫ ((.pred q) ⋒ (.pred r))) := by
  simp only [Ereq.matches_pred, Ereq.matches_inter, PExtension.models, Bool.and_eq_true]
  constructor
  · rintro ⟨c, rfl, hq, hr⟩; exact ⟨⟨c, rfl, hq⟩, ⟨c, rfl, hr⟩⟩
  · rintro ⟨⟨c, rfl, hq⟩, ⟨_, ⟨⟩, hr⟩⟩; exact ⟨c, rfl, hq, hr⟩

/-- Predicate `or` is regex union. -/
theorem or_union {xs : Word σ n} {q r : PExtension α n} :
    (xs ⊫ (Ereq.pred (.or q r)))
    ↔ (xs ⊫ ((.pred q) ⋓ (.pred r))) := by
  simp only [Ereq.matches_pred, Ereq.matches_union, PExtension.models, Bool.or_eq_true, and_or_left,
    exists_or]

theorem deMorgan {xs : Word σ n} {q s : PExtension α n} :
    (xs ⊫ (Ereq.pred q.not ⋓ Ereq.pred s.not))
    ↔ xs ⊫ Ereq.pred (q.and s).not := by
  match xs with
  | [] => simp
  | x::xs => simp; grind

theorem deMorgan_rev {xs : Word σ n} {q s : PExtension α n} :
    (xs ⊫ (Ereq.pred q.not ⋒ Ereq.pred s.not))
    ↔ xs ⊫ Ereq.pred (q.or s).not := by
  match xs with
  | [] => simp
  | x::xs => simp; grind

theorem exists_iff_project {xs : Word σ n} {R : Ereq α (n + 1)} :
    xs ⊫ (∃ʳ R) ↔ ∃ w' : Word σ (n + 1), Word.project w' = xs ∧ w' ⊫ R := by
  rw [Ereq.matches_ex]
  constructor
  · rintro ⟨s, h⟩
    exact ⟨Word.extend xs s, Word.project_extend xs s, h⟩
  · rintro ⟨w', rfl, h⟩
    exact ⟨⟨Word.extract w', Word.extract_length_project w'⟩, by rwa [Word.extend_project]⟩

/-! ### `∃ʳ` distributes over the regex operations

The language of `∃ʳ R` is the language of `R` with the last bit erased from every letter.
So `∃ʳ` distributes over `⋓`, `⬝`, `⁽m⁾` and `★`. -/

/-- Erase the last bit of a letter. -/
abbrev projectElem : Elem σ (n + 1) → Elem σ n := fun ⟨a, v⟩ => (a, v.eraseIdx (Fin.last n))

theorem lang_ex (R : Ereq α (n + 1)) :
    ((∃ʳ R).lang : Language (Elem σ n)) = Language.map projectElem R.lang := by
  ext xs
  exact exists_iff_project.trans (exists_congr fun _ => and_comm)

theorem exists_distr_or (L R : Ereq α (n + 1)) (xs : Word σ n) :
    xs ⊫ ∃ʳ (L ⋓ R) ↔ xs ⊫ ((∃ʳ L) ⋓ (∃ʳ R)) := by
  simp only [Ereq.Matches, Ereq.lang_ex, Ereq.lang_union, map_add]

theorem exists_distr_cat (L R : Ereq α (n + 1)) (xs : Word σ n) :
    xs ⊫ ∃ʳ (L ⬝ R) ↔ xs ⊫ ((∃ʳ L) ⬝ (∃ʳ R)) := by
  simp only [Ereq.Matches, Ereq.lang_ex, Ereq.lang_cat, map_mul]

theorem exists_distr_repeatCat (R : Ereq α (n + 1)) (xs : Word σ n) :
    xs ⊫ ∃ʳ (R ⁽ m ⁾) ↔ xs ⊫ ((∃ʳ R) ⁽ m ⁾) := by
  simp only [Ereq.Matches, Ereq.lang_ex, Ereq.lang_repeatCat, map_pow]

theorem exists_distr_star (R : Ereq α (n + 1)) (xs : Word σ n) :
    xs ⊫ ∃ʳ (R★) ↔ xs ⊫ (∃ʳ R)★ := by
  simp only [Ereq.Matches, Ereq.lang_ex, Ereq.lang_star, Language.map_kstar]

/-- `∃ʳ` distributes over `⋒` when `L'` matches a word exactly when `L` matches its projection. -/
theorem exists_distr_inter {L' R : Ereq α (n + 1)} {L : Ereq α n}
    (hL : ∀ w : Word σ (n + 1), w ⊫ L' ↔ Word.project w ⊫ L) (xs : Word σ n) :
    xs ⊫ ∃ʳ (L' ⋒ R) ↔ xs ⊫ (L ⋒ (∃ʳ R)) := by
  simp only [matches_ex, matches_inter, hL, Word.project_extend, exists_and_left]

/-- The same with the roles of the two sides swapped. -/
theorem exists_distr_inter' {L R' : Ereq α (n + 1)} {R : Ereq α n}
    (hR : ∀ w : Word σ (n + 1), w ⊫ R' ↔ Word.project w ⊫ R) (xs : Word σ n) :
    xs ⊫ ∃ʳ (L ⋒ R') ↔ xs ⊫ ((∃ʳ L) ⋒ R) := by
  simp only [matches_ex, matches_inter, hR, Word.project_extend, exists_and_right]

/-! ### Predicate stars -/

/-- A word matches `p★` iff every letter satisfies `p`. -/
theorem matches_star_pred {w : Word σ n} {p : PExtension α n} :
    (w ⊫ (Ereq.pred p)★) ↔ ∀ a ∈ w, p.models a := by
  simp only [Ereq.Matches, Ereq.lang_star, Language.mem_kstar]
  constructor
  · rintro ⟨L, rfl, hL⟩ a ha
    obtain ⟨y, hy, hay⟩ := List.mem_flatten.mp ha
    obtain ⟨c, rfl, hc⟩ := hL y hy
    simp_all
  · intro h
    refine ⟨w.map ([·]), (List.flatMap_singleton' w).symm, ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, rfl, h a ha⟩

@[simp]
theorem any_matches (xs : Word σ n) : xs ⊫ Ereq.any (α := α) (n := n) := by
  rw [Ereq.any, Ereq.matches_star_pred]
  simp [PExtension.models]

/-! ### Matching patterns -/

/-- `pred ⊥` matches nothing. -/
theorem not_matches_bot {w : Word σ n} : ¬ w ⊫ (Ereq.pred .bot : Ereq α n) := by
  simp [Ereq.matches_pred]

/-- `L ⬝ p ⬝ R` matches exactly the words that split around a `p`-letter, with the prefix
    matching `L` and the suffix matching `R`. -/
theorem matches_cat_pred_cat {w : Word σ n} {p : PExtension α n} {L R : Ereq α n} :
    (w ⊫ (L ⬝ Ereq.pred p ⬝ R))
      ↔ ∃ xs a ys, w = xs ++ a :: ys ∧ xs ⊫ L ∧ p.models a ∧ ys ⊫ R := by
  rw [Ereq.matches_cat]
  constructor
  · rintro ⟨xs, _, hL, h, rfl⟩
    obtain ⟨_, ys, ⟨a, rfl, ha⟩, hR, rfl⟩ := Ereq.matches_cat.mp h
    exact ⟨xs, a, ys, rfl, hL, ha, hR⟩
  · rintro ⟨xs, a, ys, rfl, hL, ha, hR⟩
    exact ⟨xs, [a] ++ ys, hL,
      Ereq.matches_cat.mpr ⟨[a], ys, Ereq.matches_pred.mpr ⟨a, rfl, ha⟩, hR, rfl⟩, rfl⟩

/-- `any ⬝ p ⬝ any` matches exactly the words having some position satisfying `p`. -/
theorem matches_somewhere {w : Word σ n} {p : PExtension α n} :
    (w ⊫ (Ereq.any ⬝ Ereq.pred p ⬝ Ereq.any)) ↔ ∃ i : Fin w.length, p.models w[i] := by
  rw [Ereq.matches_cat_pred_cat,
    List.exists_getElem_iff_split (P := fun b => p.models b = true)]
  simp

/-- `any ⬝ p ⬝ any ⬝ q ⬝ any` matches exactly the words having a position satisfying `p`
    strictly before a position satisfying `q`. -/
theorem matches_before {w : Word σ n} {p q : PExtension α n} :
    (w ⊫ (Ereq.any ⬝ Ereq.pred p ⬝ Ereq.any ⬝ Ereq.pred q ⬝ Ereq.any))
      ↔ ∃ i j : Fin w.length, i < j ∧ p.models w[i] ∧ q.models w[j] := by
  rw [Ereq.matches_cat_pred_cat,
    List.exists_lt_getElem_iff (P := fun b => p.models b = true)
      (Q := fun b => q.models b = true)]
  simp only [any_matches, true_and, Ereq.matches_somewhere]

/-- Exactly one position satisfies `p`. -/
theorem matches_unique {w : Word σ n} {p : PExtension α n} :
    (w ⊫ ((Ereq.pred p.not)★ ⬝ Ereq.pred p ⬝ (Ereq.pred p.not)★))
      ↔ ∃! i : Fin w.length, p.models w[i] := by
  have no_p {ys : Word σ n} : (ys ⊫ (Ereq.pred p.not)★) ↔ ∀ b ∈ ys, ¬ p.models b := by
    rw [Ereq.matches_star_pred]; simp
  rw [Ereq.matches_cat_pred_cat,
    List.existsUnique_getElem_iff (P := fun b => p.models b = true)]
  simp only [no_p]

end Ereq
