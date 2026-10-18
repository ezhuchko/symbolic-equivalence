import Mathlib.Basic.ExistsUnique
import Mathlib.Data.List.Basic

/-!
# Indexing into `xs ++ a :: ys`

Statements about positions of a list, `∃ i : Fin l.length, P l[i]` and its variants, turned
into statements about splitting the list around an element. These are used by
`SymbolicEquivalence.Ereq.Semantics` and the wMSO translation.
-/

variable {α : Type _}

/-- Some position of `l` satisfies `P` iff `l` splits around a `P`-element. -/
theorem List.exists_getElem_iff_split {l : List α} {P : α → Prop} :
    (∃ i : Fin l.length, P l[i]) ↔ ∃ xs a ys, l = xs ++ a :: ys ∧ P a := by
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    exact ⟨l.take i, l[i], l.drop (i + 1), by simp, h⟩
  · rintro ⟨xs, a, ys, rfl, h⟩
    exact ⟨⟨xs.length, by simp⟩, by simpa using h⟩

/-- A `P`-position precedes a `Q`-position iff `l` splits around a `P`-element followed
    by a `Q`-position. -/
theorem List.exists_lt_getElem_iff {l : List α} {P Q : α → Prop} :
    (∃ i j : Fin l.length, i < j ∧ P l[i] ∧ Q l[j]) ↔
      ∃ xs a ys, l = xs ++ a :: ys ∧ P a ∧ ∃ j : Fin ys.length, Q ys[j] := by
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hP, hQ⟩
    simp only [Fin.mk_lt_mk] at hij
    refine ⟨l.take i, l[i], l.drop (i + 1), by simp, hP, ⟨j - (i + 1), by simp; omega⟩, ?_⟩
    grind
  · rintro ⟨xs, a, ys, rfl, hP, ⟨j, hj⟩, hQ⟩
    refine ⟨⟨xs.length, by simp⟩, ⟨xs.length + 1 + j, by simp; omega⟩, by simp; omega,
      by simpa using hP, ?_⟩
    grind

/-- Exactly one position of `l` satisfies `P` iff `l` splits around the only `P`-element. -/
theorem List.existsUnique_getElem_iff {l : List α} {P : α → Prop} :
    (∃! i : Fin l.length, P l[i]) ↔
      ∃ ys a zs, l = ys ++ a :: zs ∧ (∀ b ∈ ys, ¬ P b) ∧ P a ∧ ∀ b ∈ zs, ¬ P b := by
  simp only [List.forall_mem_iff_forall_getElem]
  constructor
  · rintro ⟨⟨i, hi⟩, hP, huniq⟩
    have only_i (j : Nat) (hj : j < l.length) (hPj : P l[j]) : j = i :=
      congrArg Fin.val (huniq ⟨j, hj⟩ hPj)
    refine ⟨l.take i, l[i], l.drop (i + 1), by simp, ?_, hP, ?_⟩ <;> grind
  · rintro ⟨ys, a, zs, rfl, hys, ha, hzs⟩
    refine ⟨⟨ys.length, by simp⟩, by simpa using ha, fun ⟨j, hj⟩ hPj => Fin.ext ?_⟩
    simp only [Fin.getElem_fin, List.getElem_append] at hPj
    grind

theorem Fin.existsUnique_iff {N : Nat} {P : Fin N → Prop} :
    (∃! i : Fin N, P i) ↔ ∃! i : Nat, ∃ h : i < N, P ⟨i, h⟩ := by
  constructor
  · rintro ⟨⟨i, hi⟩, hp, huniq⟩
    exact ⟨i, ⟨hi, hp⟩, fun j ⟨hj, hpj⟩ => congrArg Fin.val (huniq ⟨j, hj⟩ hpj)⟩
  · rintro ⟨i, ⟨hi, hp⟩, huniq⟩
    exact ⟨⟨i, hi⟩, hp, fun ⟨j, hj⟩ hpj => Fin.ext (huniq j ⟨hj, hpj⟩)⟩
