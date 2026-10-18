import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Fin.Tuple.Basic

/-!
# `List.Vector` helpers

Small facts about `snoc`, `last`, `eraseIdx` and `ofFn` on `List.Vector`, and `Fin.castPredVal`.
-/

/-- `Fin.castPred` with the side condition stated on `.val`. -/
abbrev Fin.castPredVal (i : Fin (n + 1)) (h : ¬ i.val = n) : Fin n :=
  i.castPred (Fin.ne_of_val_ne h)

/-- A list of length `n + 1` is its `eraseIdx n` with the last element appended. -/
theorem List.eq_eraseIdx_append_getElem {l : List α} (hl : l.length = n + 1) :
    l = l.eraseIdx n ++ [l[n]] := by
  have hne : l ≠ [] := by intro h; simp [h] at hl
  have hn : n = l.length - 1 := by omega
  simp only [hn, List.eraseIdx_length_sub_one]
  rw [← List.getLast_eq_getElem hne, List.dropLast_append_getLast]

namespace List.Vector

/-- `toList` of `snoc` appends the new element at the end. -/
@[simp]
theorem toList_snoc {v : List.Vector α n} {a : α} :
    (v.snoc a).toList = v.toList ++ [a] := rfl

/-- `toList` of `eraseIdx` is `List.eraseIdx` on the underlying list. -/
@[simp]
theorem toList_eraseIdx {i : Fin n} {v : List.Vector α n} :
    (v.eraseIdx i).toList = v.toList.eraseIdx i :=
  eraseIdx_val

/-- Indexing into `xs.snoc x`: the last position yields `x`, all others index into `xs`. -/
theorem getElem_snoc {n : Nat} (xs : List.Vector α n) (x : α) (i : Fin (n + 1)) :
    (xs.snoc x)[i] = if h : i.val = n then x else xs[i] := by
  simp only [Fin.getElem_fin, getElem_def, toList_snoc, List.getElem_append, toList_length]
  split <;> split <;> first | omega | simp [*]

/-- The last position of `x.snoc a` holds `a`. -/
theorem getElem_snoc_last {x : List.Vector α n} {a : α} : (x.snoc a)[n] = a := by
  simpa using getElem_snoc x a ⟨n, Nat.lt_succ_self n⟩

/-- Positions before the last are unaffected by `snoc`. -/
theorem getElem_snoc_lt {x : List.Vector α n} {a : α} {k : Nat} (h : k < n) :
    (x.snoc a)[k] = x[k] := by
  simpa [Nat.ne_of_lt h] using getElem_snoc x a ⟨k, Nat.lt_succ_of_lt h⟩

@[simp]
theorem getElem_ofFn (f : Fin n → α) (i : Fin n) : (ofFn f)[i] = f i := get_ofFn f i

/-- `ofFn` turns `Fin.snoc` into `snoc`. -/
theorem ofFn_snoc {n : Nat} (f : Fin n → α) (x : α) :
    ofFn (Fin.snoc f x : Fin (n + 1) → α) = (ofFn f).snoc x := by
  apply List.Vector.eq
  rw [toList_ofFn, List.ofFn_succ_last]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Erasing the last index undoes `snoc`. -/
theorem eraseIdx_last_snoc {v : List.Vector α n} {b : α} :
    eraseIdx (Fin.last n) (v.snoc b) = v := by
  apply List.Vector.eq
  simp [List.eraseIdx_append_of_length_le]

/-- Erasing the last index and appending the last entry recovers the vector. -/
theorem snoc_eraseIdx_last {n : Nat} {v : List.Vector α (n + 1)} :
    (eraseIdx (Fin.last n) v).snoc v.last = v := by
  apply List.Vector.eq
  simp only [toList_snoc, toList_eraseIdx, last_def, get_eq_get_toList, Fin.val_last]
  exact (List.eq_eraseIdx_append_getElem v.toList_length).symm

/-- Normalises `get` at a literal `Fin` to `getElem`. -/
@[simp] theorem get_mk_eq_getElem {v : List.Vector β N} {i : Nat} {h : i < N} :
    v.get ⟨i, h⟩ = v[i] := rfl

end List.Vector
