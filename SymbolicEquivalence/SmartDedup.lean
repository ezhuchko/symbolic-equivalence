/-!
# Order-preserving deduplication of lists

`smartDedup` removes duplicates, keeping the first occurrence of each element in order.
-/

variable {α : Type _}

section Dedup
variable [BEq α]

/-! ### Definitions -/

/-- Remove every occurrence of `x` (`List.erase` removes only the first). -/
def List.eraseAll (x : α) (xs : List α) : List α :=
  xs.filter (· != x)

/-- Push `x` onto `xs`, keeping only this occurrence of `x` in `xs`. -/
private def List.addErase (x : α) (xs : List α) : List α :=
  x :: xs.eraseAll x

/-- `smartDedup xs` followed by `ys` with every element of `xs` erased. The `smartDedup`
lemmas about `++` are proved through it. -/
private def allAddErase (xs ys : List α) : List α :=
  xs.foldr List.addErase ys

/-- Deduplication keeping the first occurrence of each element. -/
def smartDedup (xs : List α) : List α :=
  xs.foldr List.addErase []

private theorem smartDedup_eq_allAddErase (xs : List α) : smartDedup xs = allAddErase xs [] := rfl

@[simp] theorem eraseAll_nil (x : α) : List.eraseAll x [] = [] := rfl

@[simp] private theorem allAddErase_nil_left (ys : List α) : allAddErase [] ys = ys := rfl

@[simp] theorem smartDedup_nil : smartDedup ([] : List α) = [] := rfl

private theorem allAddErase_cons (x : α) (xs ys : List α) :
    allAddErase (x :: xs) ys = List.addErase x (allAddErase xs ys) := rfl

/-- Deduplicating a cons gives a cons with the same head. -/
theorem smartDedup_cons {x : α} {xs : List α} :
    smartDedup (x :: xs) = x :: List.eraseAll x (smartDedup xs) := rfl

theorem smartDedup_ne_nil {xs : List α} (h : xs ≠ []) : smartDedup xs ≠ [] := by
  match xs with
  | _ :: _ => exact List.cons_ne_nil _ _

@[simp] theorem eraseAll_eraseAll (x : α) (l : List α) :
    (l.eraseAll x).eraseAll x = l.eraseAll x := by
  simp [List.eraseAll, List.filter_filter]

private theorem eraseAll_comm (x y : α) (l : List α) :
    (l.eraseAll x).eraseAll y = (l.eraseAll y).eraseAll x := by
  simp only [List.eraseAll, List.filter_filter, Bool.and_comm]

private theorem smartDedup_append (xs ys : List α) :
    smartDedup (xs ++ ys) = allAddErase xs (smartDedup ys) :=
  List.foldr_append

section LawfulBEq
variable [LawfulBEq α]

/-! ### `eraseAll` -/

@[simp] theorem mem_eraseAll_iff (x y : α) (xs : List α) :
    x ∈ xs.eraseAll y ↔ x ∈ xs ∧ x ≠ y := by
  simp [List.eraseAll]

theorem eraseAll_cons_self {x : α} {xs : List α} :
    List.eraseAll x (x :: xs) = List.eraseAll x xs := by
  simp [List.eraseAll]

theorem eraseAll_cons_of_ne {x i : α} {xs : List α} (h : x ≠ i) :
    List.eraseAll x (i :: xs) = i :: List.eraseAll x xs := by
  simp [List.eraseAll, Ne.symm h]

private theorem eraseAll_eq_self {x : α} {l : List α} (h : x ∉ l) : List.eraseAll x l = l :=
  List.filter_eq_self.2 fun _ ha => bne_iff_ne.2 (ne_of_mem_of_not_mem ha h)

/-! ### `allAddErase` -/

private theorem mem_allAddErase_iff (x : α) (xs ys : List α) :
    x ∈ allAddErase xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [allAddErase_cons, List.addErase, List.mem_cons, mem_eraseAll_iff, ih]
    grind

/-- `allAddErase` only copies elements, so erasing before or after is the same. -/
private theorem allAddErase_eraseAll_comm (x : α) (xs ys : List α) :
    (allAddErase xs ys).eraseAll x = allAddErase (xs.eraseAll x) (ys.eraseAll x) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [allAddErase_cons, List.addErase]
    by_cases h : a = x
    · subst h
      rw [eraseAll_cons_self, eraseAll_eraseAll, ih, eraseAll_cons_self]
    · rw [eraseAll_cons_of_ne (Ne.symm h), eraseAll_cons_of_ne (Ne.symm h),
        allAddErase_cons, List.addErase, ← ih, eraseAll_comm]

/-- Erasing `x` from the left operand is invisible once `x` is erased from the result. -/
private theorem eraseAll_allAddErase_eraseAll (x : α) (xs ys : List α) :
    (allAddErase (xs.eraseAll x) ys).eraseAll x = (allAddErase xs ys).eraseAll x := by
  simp only [allAddErase_eraseAll_comm, eraseAll_eraseAll]

private theorem allAddErase_assoc (xs ys zs : List α) :
    allAddErase (allAddErase xs ys) zs = allAddErase xs (allAddErase ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [allAddErase_cons, List.addErase, eraseAll_allAddErase_eraseAll, ih]

/-- The left-biased union adds nothing when everything in `ys` is already in `xs`. -/
private theorem allAddErase_of_subset {xs ys : List α}
    (hxs : xs.Nodup) (hys : ∀ y ∈ ys, y ∈ xs) : allAddErase xs ys = xs := by
  induction xs generalizing ys with
  | nil => simpa [List.eq_nil_iff_forall_not_mem] using hys
  | cons x xs ih =>
    rw [List.nodup_cons] at hxs
    have hys' : ∀ y ∈ ys.eraseAll x, y ∈ xs := by
      intro y hy
      rw [mem_eraseAll_iff] at hy
      simpa [hy.2] using hys y hy.1
    rw [allAddErase_cons, List.addErase, allAddErase_eraseAll_comm, eraseAll_eq_self hxs.1,
      ih hxs.2 hys']

/-! ### `smartDedup` -/

@[simp] theorem mem_smartDedup_iff (x : α) (xs : List α) : x ∈ smartDedup xs ↔ x ∈ xs := by
  simp [smartDedup_eq_allAddErase, mem_allAddErase_iff]

theorem smartDedup_nodup {xs : List α} : (smartDedup xs).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [smartDedup_cons, List.nodup_cons, List.eraseAll]
    exact ⟨by simp, ih.filter _⟩

private theorem smartDedup_eq_self {xs : List α} (h : xs.Nodup) : smartDedup xs = xs :=
  allAddErase_of_subset h (by simp)

theorem smartDedup_append_subset {xs ys : List α}
    (hxs : xs.Nodup) (hys : ∀ x ∈ ys, x ∈ xs) : smartDedup (xs ++ ys) = xs := by
  rw [smartDedup_append]
  exact allAddErase_of_subset hxs (by simpa using hys)

theorem smartDedup_append_self {xs : List α} (h : xs.Nodup) : smartDedup (xs ++ xs) = xs :=
  smartDedup_append_subset h fun _ => id

/-- Deduplication changes only multiplicity, so it is invisible to `any`. -/
theorem any_smartDedup (p : α → Bool) (l : List α) : (smartDedup l).any p = l.any p := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, mem_smartDedup_iff]

/-! ### Absorption of nested deduplication

These give `smartDedup_assoc`. -/

private theorem smartDedup_append_dedup_left (xs ys : List α) :
    smartDedup (smartDedup xs ++ ys) = smartDedup (xs ++ ys) := by
  rw [smartDedup_append, smartDedup_eq_allAddErase, allAddErase_assoc, allAddErase_nil_left,
    smartDedup_append]

private theorem smartDedup_append_dedup_right (xs ys : List α) :
    smartDedup (xs ++ smartDedup ys) = smartDedup (xs ++ ys) := by
  rw [smartDedup_append, smartDedup_eq_self smartDedup_nodup, smartDedup_append]

theorem smartDedup_assoc {xs ys zs : List α} :
    smartDedup (smartDedup (xs ++ ys) ++ zs) = smartDedup (xs ++ smartDedup (ys ++ zs)) := by
  rw [smartDedup_append_dedup_left, List.append_assoc, smartDedup_append_dedup_right]

end LawfulBEq

end Dedup
