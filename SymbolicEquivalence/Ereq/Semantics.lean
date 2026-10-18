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

/-! ### `∃ʳ` on `ε`, `⊥` and the last bit -/

/-- A word matching a predicate has length one. -/
theorem length_of_matches_pred {w : Word σ n} {φ : PExtension α n} (h : w ⊫ pred φ) :
    w.length = 1 := by
  obtain ⟨c, rfl, _⟩ := matches_pred.mp h; rfl

theorem exists_eps (xs : Word σ n) :
    xs ⊫ ∃ʳ (ε : Ereq α (n + 1)) ↔ xs ⊫ (ε : Ereq α n) := by
  simp only [matches_ex, matches_eps]
  constructor
  · rintro ⟨s, h⟩
    simpa using congrArg List.length h
  · rintro rfl; exact ⟨⟨[], rfl⟩, rfl⟩

theorem exists_bot (xs : Word σ n) :
    xs ⊫ ∃ʳ (pred .bot : Ereq α (n + 1)) ↔ xs ⊫ (pred .bot : Ereq α n) := by
  simp [not_matches_bot]

/-- Quantifying a predicate that holds whenever the last bit is `b` gives `⊤`. -/
private theorem exists_bit (b : Bool) {φ : PExtension α (n + 1)}
    (hφ : ∀ a (v : List.Vector Bool n), φ.models (a, v.snoc b)) (xs : Word σ n) :
    xs ⊫ ∃ʳ (pred φ) ↔ xs ⊫ (pred .top : Ereq α n) := by
  constructor
  · rintro ⟨s, h⟩
    have hlen := length_of_matches_pred h
    rw [Word.length_extend] at hlen
    match xs, hlen with
    | [x], _ => simp [PExtension.models]
  · intro h
    obtain ⟨⟨a, v⟩, rfl, -⟩ := matches_pred.mp h
    exact ⟨⟨[b], rfl⟩, matches_pred_cons.mpr ⟨rfl, hφ a v⟩⟩

/-- After quantifying the last bit, the atom `pₙ` holds on every letter. -/
theorem exists_last_bit (xs : Word σ n) :
    xs ⊫ ∃ʳ (pred (.p (Fin.last n)) : Ereq α (n + 1)) ↔ xs ⊫ (pred .top : Ereq α n) :=
  exists_bit true (fun _ _ => by simp [PExtension.models, List.Vector.getElem_snoc_last]) xs

/-- After quantifying the last bit, the negated atom `¬pₙ` holds on every letter. -/
theorem exists_not_last_bit (xs : Word σ n) :
    xs ⊫ ∃ʳ (pred (.not (.p (Fin.last n))) : Ereq α (n + 1))
      ↔ xs ⊫ (pred .top : Ereq α n) :=
  exists_bit false (fun _ _ => by simp [PExtension.models, List.Vector.getElem_snoc_last]) xs

/-! ### Predicate complement and regex complement -/

/-- Predicate complement is regex complement restricted to single letters. -/
theorem matches_pred_not {xs : Word σ n} {φ : PExtension α n} :
    xs ⊫ pred (.not φ) ↔ xs ⊫ (~(pred φ) ⋒ (pred .top : Ereq α n)) := by
  match xs with
  | [] => simp
  | [x] => simp [PExtension.models]
  | _ :: _ :: _ => simp

/-- Regex complement of an atom differs from its predicate complement, already on the empty
    word. -/
theorem neg_pred_ne_pred_not (i : Fin n) :
    ¬ ∀ xs : Word σ n, xs ⊫ ~(pred (.p i) : Ereq α n) ↔ xs ⊫ (pred (.not (.p i)) : Ereq α n) :=
  fun h => matches_pred_nil ((h []).mp (matches_neg.mpr matches_pred_nil))

/-- Quantifying the regex complement of the last atom gives every word. -/
theorem exists_neg_last_bit (xs : Word σ n) :
    xs ⊫ ∃ʳ (~(pred (.p (Fin.last n))) : Ereq α (n + 1)) ↔ xs ⊫ (Ereq.any : Ereq α n) := by
  refine iff_of_true ?_ (any_matches xs)
  rw [matches_ex]
  by_cases hlen : xs.length = 1
  · obtain ⟨⟨a, v⟩, rfl⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨⟨[false], rfl⟩, fun h => ?_⟩
    simpa [PExtension.models, List.Vector.getElem_snoc_last] using (matches_pred_cons.mp h).2
  · refine ⟨⟨List.replicate xs.length false, by simp⟩, fun h => hlen ?_⟩
    exact (Word.length_extend xs _).symm.trans (length_of_matches_pred h)

end Ereq
