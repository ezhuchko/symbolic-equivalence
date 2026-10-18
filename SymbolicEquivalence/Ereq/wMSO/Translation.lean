import SymbolicEquivalence.Ereq.Semantics
import SymbolicEquivalence.Ereq.wMSO.Encoding

/-!
# Translation from wMSO to EREQ

`Formula.toEreq` translates wMSO formulas into quantified regular expressions, and
`Formula.toEreq_correctness` proves `Formula.Satisfies xs θ φ ↔ 「xs, θ」 ⊫ ⌜φ⌝`.
-/

open scoped Formula Ereq
open Ereq (any)

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ]

/-- Translate a wMSO formula into a quantified regular expression. -/
def Formula.toEreq : Formula α n → Ereq α n
  | .not φ    => ~ (toEreq φ)
  | .and φ ψ  => toEreq φ ⋒ toEreq ψ
  | .or φ ψ   => toEreq φ ⋓ toEreq ψ
  | .exists₂ φ => ∃ʳ (toEreq φ)
  | .pred φ n  => any ⬝ (.pred (.and (.pred φ) (.p n))) ⬝ any
  | .singleton n => (.pred (.not (.p n)))★ ⬝ (.pred (.p n)) ⬝ (.pred (.not (.p n)))★
  | .lt n m    => any ⬝ (.pred (.p n)) ⬝ any ⬝ (.pred (.p m)) ⬝ any
  | .sub n m   => (.pred (.or (.not (.p n)) (.p m)))★

notation "⌜" f "⌝" => Formula.toEreq f

/-! ### Reading a position of the encoded word

The letter at position `i` of `「xs, θ」` is `xs[i]`, and its bit `m` is `(θ m)[i]`. -/

@[simp] theorem List.toWord_getElem_fst {xs : List σ} :
    ∀ (θ : Assignment xs.length n) (i : Nat) (h : i < (「xs, θ」).length),
      ((「xs, θ」)[i]'h).1 = xs[i]'(by simpa using h) := by
  match xs with
  | [] => intro θ i h; simp [List.toWord] at h
  | x :: xs' =>
    rintro θ (_ | k) h
    · rfl
    · exact toWord_getElem_fst (fun j => (θ j).tail) k (by simpa using h)

@[simp] theorem List.toWord_getElem_snd {xs : List σ} {θ : Assignment xs.length n} {m : Nat}
    {i : Nat} (hm : m < n) (h : i < 「xs, θ」.length) :
    ((「xs, θ」)[i]'h).2[m]'hm = (θ ⟨m, hm⟩)[i]'(by simpa using h) :=
  (toWord_getElem_bit (m := ⟨m, hm⟩) θ i (by simpa using h) h).symm

/-! ### The four atomic formulas

The translation is correct for `⊆`, `|·| = 1`, `<` and predicates. Each proof applies a
matching lemma from `Ereq.Semantics`, and uses the two lemmas above. -/

section Atoms

variable {xs : List σ} {θ : Assignment xs.length n}

/-- `Xₖ ⊆ Xₘ` — every position in `Xₖ` is a position in `Xₘ`. -/
theorem Formula.toEreq_correctness_sub {k m : Fin n} :
    Formula.Satisfies xs θ (k ⊆ᶠ m : Formula α n) ↔ 「xs, θ」 ⊫ ⌜(k ⊆ᶠ m : Formula α n)⌝ := by
  simp only [Formula.Satisfies, toEreq]
  rw [Ereq.matches_star_pred, List.forall_mem_iff_forall_getElem]
  simp [Fin.forall_iff]
  grind

/-- `|Xₘ| = 1` — exactly one position lies in `Xₘ`. -/
theorem Formula.toEreq_correctness_singleton {m : Fin n} :
    Formula.Satisfies xs θ ([| m |] : Formula α n) ↔ 「xs, θ」 ⊫ ⌜([| m |] : Formula α n)⌝ := by
  simp only [Formula.Satisfies, toEreq]
  rw [Ereq.matches_unique, Fin.existsUnique_iff, Fin.existsUnique_iff]
  simp

/-- `Xₖ <ᶠ Xₘ` — some position of `Xₖ` precedes some position of `Xₘ`. -/
theorem Formula.toEreq_correctness_lt {k m : Fin n} :
    Formula.Satisfies xs θ (k <ᶠ m : Formula α n) ↔ 「xs, θ」 ⊫ ⌜(k <ᶠ m : Formula α n)⌝ := by
  simp only [Formula.Satisfies, toEreq]
  rw [Ereq.matches_before]
  simp [Fin.exists_iff]
  grind

/-- `φ(Xₘ)` — some position of `Xₘ` carries a letter satisfying the base predicate `φ`. -/
theorem Formula.toEreq_correctness_pred {m : Fin n} {φ : α} :
    Formula.Satisfies xs θ (.pred φ m) ↔ 「xs, θ」 ⊫ ⌜.pred φ m⌝ := by
  simp only [Formula.Satisfies, toEreq]
  rw [Ereq.matches_somewhere]
  simp [Fin.exists_iff]
  grind

end Atoms

/-- Matching `∃ʳ ⌜φ⌝` against `「xs, θ」` means choosing a value `v` for the new variable. -/
theorem Formula.toEreq_ex_toWord {φ : Formula α (n + 1)} {xs : List σ}
    {θ : Assignment xs.length n} :
    (「xs, θ」 ⊫ ∃ʳ ⌜φ⌝) ↔
      ∃ v : List.Vector Bool xs.length, 「xs, extAssignment θ v」 ⊫ ⌜φ⌝ := by
  rw [Ereq.matches_ex]
  constructor
  · rintro ⟨v, h⟩
    refine ⟨v.congr (List.toWord_length θ), ?_⟩
    show 「xs, extAssignment θ (v.congr (List.toWord_length θ))」 ⊫ ⌜φ⌝
    rwa [List.extend_toWord]
  · rintro ⟨v, h⟩
    refine ⟨v.congr (Eq.symm (List.toWord_length θ)), ?_⟩
    rwa [← List.extend_toWord]

/-- Correctness of the translation: a formula holds iff the encoded word matches its
    translation. -/
theorem Formula.toEreq_correctness : ∀ {n : Nat} (φ : Formula α n) (xs : List σ)
    (θ : Assignment xs.length n), Formula.Satisfies xs θ φ ↔ 「xs, θ」 ⊫ ⌜φ⌝
  | _, φ ∨ᶠ ψ, xs, θ => by
    simp [Formula.Satisfies, toEreq, toEreq_correctness φ xs θ, toEreq_correctness ψ xs θ]
  | _, φ ∧ᶠ ψ, xs, θ => by
    simp [Formula.Satisfies, toEreq, toEreq_correctness φ xs θ, toEreq_correctness ψ xs θ]
  | _, ¬ᶠ φ, xs, θ => by simp [Formula.Satisfies, toEreq, toEreq_correctness φ xs θ]
  | _, ∃ᶠ φ, xs, θ => by
    rw [toEreq, toEreq_ex_toWord]
    exact exists_congr fun v => toEreq_correctness φ xs (extAssignment θ v)
  | _, _ <ᶠ _, _, _ => toEreq_correctness_lt
  | _, _ ⊆ᶠ _, _, _ => toEreq_correctness_sub
  | _, [| _ |], _, _ => toEreq_correctness_singleton
  | _, .pred _ _, _, _ => toEreq_correctness_pred

/-- A formula and its translation denote the same language. -/
theorem Formula.lang_eq (φ : Formula α n) : φ.lang = (⌜φ⌝).lang := by
  ext w
  change Formula.Satisfies (w.map Prod.fst) (Word.transpose w) φ ↔ _
  rw [toEreq_correctness φ (w.map Prod.fst) (Word.transpose w), List.toWord_transpose]
  rfl

/-- `Formula.Satisfies` is exactly membership of the encoded word in `Formula.lang`. -/
theorem Formula.mem_lang {φ : Formula α n} {xs : List σ} {θ : Assignment xs.length n} :
    「xs, θ」 ∈ φ.lang ↔ Formula.Satisfies xs θ φ := by
  rw [Formula.lang_eq]; exact (toEreq_correctness φ xs θ).symm

@[simp] theorem Formula.lang_or (φ ψ : Formula α n) :
    (φ ∨ᶠ ψ).lang = φ.lang + ψ.lang := by
  rw [Formula.lang_eq, Formula.lang_eq φ, Formula.lang_eq ψ]; rfl

@[simp] theorem Formula.lang_and (φ ψ : Formula α n) :
    (φ ∧ᶠ ψ).lang = φ.lang ⊓ ψ.lang := by
  rw [Formula.lang_eq, Formula.lang_eq φ, Formula.lang_eq ψ]; rfl

@[simp] theorem Formula.lang_not (φ : Formula α n) :
    (¬ᶠ φ).lang = {w | w ∉ φ.lang} := by
  rw [Formula.lang_eq, Formula.lang_eq φ]; rfl

/-- Membership in a formula's language is matching its translation. -/
theorem Formula.mem_lang_iff_matches {φ : Formula α n} {w : Word σ n} :
    w ∈ φ.lang ↔ w ⊫ ⌜φ⌝ := by rw [Formula.lang_eq φ]; rfl

/-- The existential quantifier denotes projection of the language. -/
theorem Formula.lang_exists (φ : Formula α (n + 1)) :
    (∃ᶠ φ).lang = Word.project '' φ.lang := by
  rw [Formula.lang_eq (∃ᶠ φ)]
  ext w
  change (w ⊫ ∃ʳ ⌜φ⌝) ↔ w ∈ Word.project '' φ.lang
  rw [Ereq.exists_iff_project]
  exact ⟨fun ⟨w', hp, h⟩ => ⟨w', Formula.mem_lang_iff_matches.mpr h, hp⟩,
         fun ⟨w', h, hp⟩ => ⟨w', hp, Formula.mem_lang_iff_matches.mp h⟩⟩

/-! ### The translation is linear -/

/-- The number of constructors of an `Ereq`, counting each predicate as one. -/
def Ereq.size : Ereq α n → Nat
  | .ε => 1
  | .pred _ => 1
  | .union l r | .intersection l r | .concatenation l r => l.size + r.size + 1
  | .star r | .negation r | .existential r => r.size + 1

/-- The number of constructors of a formula. -/
def Formula.size : Formula α n → Nat
  | .or φ ψ | .and φ ψ => φ.size + ψ.size + 1
  | .not φ | .exists₂ φ => φ.size + 1
  | .lt _ _ | .sub _ _ | .pred _ _ | .singleton _ => 1

/-- The translated formula has at most 12 times as many constructors as the input formula. -/
theorem Formula.size_toEreq (φ : Formula α n) : ⌜φ⌝.size ≤ 12 * φ.size := by
  induction φ with
  | or φ ψ ihφ ihψ | and φ ψ ihφ ihψ =>
    simp only [Formula.toEreq, Ereq.size, Formula.size]; omega
  | not φ ih | exists₂ φ ih => simp only [Formula.toEreq, Ereq.size, Formula.size]; omega
  | lt | sub | pred | singleton => simp [Formula.toEreq, Ereq.size, Ereq.any, Formula.size]
