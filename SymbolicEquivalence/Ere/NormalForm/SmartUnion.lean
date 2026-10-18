import SymbolicEquivalence.Ere.NormalForm.Syntax
import Mathlib.Tactic.Tauto

/-!
# Smart union (`⋓'`)

`mkUnion` concatenates operand lists, deduplicates (keeping first occurrences) and
rebuilds. It satisfies the union laws of `≅` as equations:

  Idempotence:            `r ⋓' r = r`
  Right-deduplication:    `(r ⋓' s) ⋓' r = r ⋓' s`
  Associativity:          `(r ⋓' s) ⋓' t = r ⋓' (s ⋓' t)`

`unionAll` folds a list with `⋓'` and works on empty lists because `⊥` is a unit for `⋓'`.
-/
open scoped Ere

variable {α : Type*} [DecidableEq α]
open EreNorm
namespace EreNorm

/-- Rebuild a node from its first operand and the rest, deduplicating. -/
def mkUnionOf (x : EreNorm α) (xs : List (EreNorm α)) : EreNorm α :=
  fromList x (List.eraseAll x (smartDedup xs))

theorem wellFormed_mkUnionOf {x : EreNorm α} {xs : List (EreNorm α)}
    (hwf : ∀ w ∈ x :: xs, WellFormed w) (hflat : ∀ w ∈ x :: xs, isUnion w = false) :
    WellFormed (mkUnionOf x xs) := by
  refine fromList_wf ?_ ?_ ?_ <;> rw [← smartDedup_cons]
  · exact fun w hw => hwf w (by simpa using hw)
  · exact smartDedup_nodup
  · exact fun w hw => hflat w (by simpa using hw)

theorem toList_mkUnionOf {x : EreNorm α} (xs : List (EreNorm α)) (h : isUnion x = false) :
    toList (mkUnionOf x xs) = smartDedup (x :: xs) := by
  rw [mkUnionOf, toList_fromList h, ← smartDedup_cons]

variable [Bot α]

/-- Smart union returns the other operand if one is `⊥` and merges the operand lists otherwise.

    Dropping `⊥` simplifies more than `≅` allows. This is safe, since it preserves the language,
    nullability, derivatives and well-formedness (`lang_mkUnion`, `nullable_mkUnion`,
    `derivative_mkUnion`, `wellFormed_mkUnion`). -/
def mkUnion (A B : EreNorm α) : EreNorm α :=
  if A = pred ⊥ then B
  else if B = pred ⊥ then A
  else mkUnionOf A.first (A.rest ++ toList B)

scoped infixr:65 " ⋓' " => mkUnion

@[simp] theorem mkUnion_bot_left (B : EreNorm α) : (pred ⊥ ⋓' B) = B := by
  simp [mkUnion]

@[simp] theorem mkUnion_bot_right (A : EreNorm α) : (A ⋓' pred ⊥) = A := by
  by_cases h : A = pred ⊥ <;> simp [mkUnion, h]

/-- If neither operand is `⊥`, `A ⋓' B` merges their operand lists. -/
theorem mkUnion_of_ne_bot {A B : EreNorm α} (ha : A ≠ pred ⊥) (hb : B ≠ pred ⊥) :
    (A ⋓' B) = mkUnionOf A.first (A.rest ++ toList B) := by
  simp [mkUnion, ha, hb]

theorem wellFormed_mkUnion {A B : EreNorm α} (ha : WellFormed A) (hb : WellFormed B) :
    WellFormed (A ⋓' B) := by
  by_cases hna : A = pred ⊥
  · subst hna; simpa
  by_cases hnb : B = pred ⊥
  · subst hnb; simpa
  rw [mkUnion_of_ne_bot hna hnb]
  exact wellFormed_mkUnionOf
    (fun w hw => (mem_toList_append ha hb hw).1)
    (fun w hw => (mem_toList_append ha hb hw).2)

/-- If neither operand is `⊥`, the operands of `a ⋓' b` are those of `a` and `b` without
    duplicates. -/
theorem toList_mkUnion {a b : EreNorm α} (ha : WellFormed a)
    (hna : a ≠ pred ⊥) (hnb : b ≠ pred ⊥) :
    toList (a ⋓' b) = smartDedup (toList a ++ toList b) := by
  rw [mkUnion_of_ne_bot hna hnb,
    toList_mkUnionOf _ (toList_not_isUnion ha _ (by simp [toList])), toList_append_eq]

/-- If `a` is not `⊥`, neither is `a ⋓' b`. -/
theorem mkUnion_ne_bot {a b : EreNorm α} (ha : WellFormed a) (hna : a ≠ pred ⊥) :
    (a ⋓' b) ≠ pred ⊥ := by
  by_cases hnb : b = pred ⊥
  · rw [hnb, mkUnion_bot_right _]; exact hna
  intro h
  have hl := toList_mkUnion ha hna hnb
  rw [h, toList_eq_self (by simp), toList_append_eq, smartDedup_cons] at hl
  obtain ⟨h1, h2⟩ := List.cons_eq_cons.mp hl
  cases a with
  | union x y zs =>
    have n : (x :: y :: zs).Nodup := by cases ha with | union _ n _ => exact n
    have hyx : y ≠ x := fun e => by simp [e] at n
    have hy : y ∈ List.eraseAll x (smartDedup ((y :: zs) ++ toList b)) := by
      rw [mem_eraseAll_iff]; exact ⟨by simp [mem_smartDedup_iff], hyx⟩
    simp only [EreNorm.first, EreNorm.rest] at h2
    rw [← h2] at hy
    simp at hy
  | _ => exact hna h1.symm

theorem mkUnion_idem {a : EreNorm α} (h : WellFormed a) : (a ⋓' a) = a := by
  by_cases hna : a = pred ⊥
  · rw [hna, mkUnion_bot_left]
  · exact eq_of_toList_eq
      (by rw [toList_mkUnion h hna hna, smartDedup_append_self (toList_nodup h)])

theorem mkUnion_dedup {a b : EreNorm α} (ha : WellFormed a) (hb : WellFormed b) :
    ((a ⋓' b) ⋓' a) = a ⋓' b := by
  by_cases hna : a = pred ⊥
  · subst hna; simp
  by_cases hnb : b = pred ⊥
  · subst hnb; simp [mkUnion_idem ha]
  have hab : WellFormed (a ⋓' b) := wellFormed_mkUnion ha hb
  have hnab : (a ⋓' b) ≠ pred ⊥ := mkUnion_ne_bot ha hna
  have hsub : ∀ x ∈ toList a, x ∈ toList (a ⋓' b) := fun x hx => by
    rw [toList_mkUnion ha hna hnb, mem_smartDedup_iff]; exact List.mem_append_left _ hx
  exact eq_of_toList_eq
    (by rw [toList_mkUnion hab hnab hna, smartDedup_append_subset (toList_nodup hab) hsub])

/-- `⋓'` is associative when `a` and `b` are well-formed. -/
theorem mkUnion_assoc {a b c : EreNorm α} (ha : WellFormed a) (hb : WellFormed b) :
    ((a ⋓' b) ⋓' c) = (a ⋓' (b ⋓' c)) := by
  by_cases hna : a = pred ⊥
  · subst hna; simp
  by_cases hnb : b = pred ⊥
  · subst hnb; simp
  by_cases hnc : c = pred ⊥
  · subst hnc; simp
  apply eq_of_toList_eq
  rw [toList_mkUnion (wellFormed_mkUnion ha hb) (mkUnion_ne_bot ha hna) hnc,
    toList_mkUnion ha hna hnb,
    toList_mkUnion ha hna (mkUnion_ne_bot hb hnb), toList_mkUnion hb hnb hnc,
    smartDedup_assoc]

/-! ## The n-ary fold

The derivative of a union is `unionAll` over the derivatives of its operands
(`eval_derivative_toList`). Unlike `unionOf`, `unionAll` satisfies its laws up to `=`
rather than `≅`. -/

/-- `⋓'` folded over a list. -/
def unionAll (xs : List (EreNorm α)) : EreNorm α := xs.foldr mkUnion (pred ⊥)

@[simp] theorem unionAll_nil : unionAll ([] : List (EreNorm α)) = pred ⊥ := rfl

@[simp] theorem unionAll_cons (x : EreNorm α) (xs : List (EreNorm α)) :
    unionAll (x :: xs) = x ⋓' unionAll xs := rfl

theorem unionAll_singleton (x : EreNorm α) : unionAll [x] = x := mkUnion_bot_right x

theorem wellFormed_unionAll {xs : List (EreNorm α)} (h : ∀ x ∈ xs, WellFormed x) :
    WellFormed (unionAll xs) := by
  induction xs with
  | nil => exact .pred ⊥
  | cons x xs ih => exact wellFormed_mkUnion (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Folding an append gives the smart union of the two folds. -/
theorem unionAll_append {xs ys : List (EreNorm α)} (h : ∀ x ∈ xs, WellFormed x) :
    unionAll (xs ++ ys) = unionAll xs ⋓' unionAll ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, unionAll_cons]
    rw [ih (fun y hy => h y (by simp [hy])),
      ← mkUnion_assoc (h x (by simp)) (wellFormed_unionAll (fun y hy => h y (by simp [hy])))]

/-- A fold absorbs any operand it already contains. -/
theorem unionAll_absorb {xs : List (EreNorm α)} {w : EreNorm α}
    (h : ∀ x ∈ xs, WellFormed x) (hw : w ∈ xs) : (unionAll xs ⋓' w) = unionAll xs := by
  induction xs with
  | nil => simp at hw
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, WellFormed y := fun y hy => h y (by simp [hy])
    rcases List.mem_cons.mp hw with rfl | hw
    · exact mkUnion_dedup hx (wellFormed_unionAll hxs)
    · rw [unionAll_cons, mkUnion_assoc hx (wellFormed_unionAll hxs), ih hxs hw]

/-- A repeated operand can be deleted anywhere in the list without changing the fold. -/
theorem unionAll_dedup {xs ys : List (EreNorm α)} {w : EreNorm α}
    (h : ∀ x ∈ xs ++ w :: ys, WellFormed x) (hw : w ∈ xs) :
    unionAll (xs ++ w :: ys) = unionAll (xs ++ ys) := by
  have hxs : ∀ x ∈ xs, WellFormed x := fun x hx => h x (by simp [hx])
  rw [unionAll_append hxs, unionAll_append hxs, unionAll_cons,
    ← mkUnion_assoc (wellFormed_unionAll hxs) (h w (by simp)), unionAll_absorb hxs hw]

/-! ### Unions of mapped lists

Stated for an arbitrary `g`, where the derivative uses `g := fun w => (ρₙ w)[c]`. -/
section Map
variable {β : Type*} [BEq β] [LawfulBEq β]

/-- Erasing every copy of `x` from `l₂` leaves the fold unchanged, provided `x`
    still occurs in the prefix `l₁`. -/
theorem unionAll_map_eraseAll (g : β → EreNorm α) {x : β} {l₁ l₂ : List β}
    (hwf : ∀ y ∈ l₁ ++ l₂, WellFormed (g y)) (h : x ∈ l₁) :
    unionAll ((l₁ ++ List.eraseAll x l₂).map g) = unionAll ((l₁ ++ l₂).map g) := by
  induction l₂ generalizing l₁ with
  | nil => rfl
  | cons a as ih =>
    by_cases hax : a = x
    · -- `a` is `x`: `eraseAll` drops it, and its copy in `l₁` absorbs it in the fold
      subst hax
      have hwf_as : ∀ y ∈ l₁ ++ as, WellFormed (g y) := by
        intro y hy
        apply hwf
        simp at hy ⊢
        tauto
      have hwf_map : ∀ y ∈ l₁.map g ++ g a :: as.map g, WellFormed y := by
        simp only [List.mem_append, List.mem_cons, List.mem_map]
        rintro _ (⟨z, hz, rfl⟩ | rfl | ⟨z, hz, rfl⟩) <;> exact hwf _ (by simp [*])
      have hdedup := unionAll_dedup hwf_map (List.mem_map_of_mem h)
      rw [eraseAll_cons_self, ih hwf_as h]
      simpa using hdedup.symm
    · -- `a` is not `x`: it stays, so move it into the prefix and use the induction hypothesis
      have hwf_a : ∀ y ∈ (l₁ ++ [a]) ++ as, WellFormed (g y) := by
        intro y hy
        apply hwf
        simp at hy ⊢
        tauto
      rw [eraseAll_cons_of_ne (Ne.symm hax)]
      simpa using ih hwf_a (List.mem_append_left _ h)

/-- Removing duplicates does not change the fold, which `derivative_mkUnion` relies on. -/
theorem unionAll_map_smartDedup (g : β → EreNorm α) (xs : List β)
    (hwf : ∀ y ∈ xs, WellFormed (g y)) :
    unionAll ((smartDedup xs).map g) = unionAll (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hwf_xs : ∀ y ∈ xs, WellFormed (g y) := by
      intro y hy
      apply hwf
      simp [hy]
    have hwf_dedup : ∀ y ∈ [x] ++ smartDedup xs, WellFormed (g y) := by
      intro y hy
      apply hwf
      simp [mem_smartDedup_iff] at hy ⊢
      tauto
    -- Erasing the later copies of `x` does not change the fold
    have hstep := unionAll_map_eraseAll g hwf_dedup (List.mem_singleton_self x)
    simp only [List.singleton_append, List.map_cons, unionAll_cons] at hstep
    rw [smartDedup_cons]
    simp only [List.map_cons, unionAll_cons]
    rw [hstep, ih hwf_xs]

end Map

end EreNorm
