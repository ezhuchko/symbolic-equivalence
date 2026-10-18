import SymbolicEquivalence.Ereq.NormalForm.Syntax
import Mathlib.Tactic.Tauto

/-!
# Smart union (`⋓'`)

`mkUnion` concatenates operand lists, deduplicates (keeping first occurrences) and
rebuilds. It satisfies the union laws of `≅` as equations:

  Idempotence:            `r ⋓' r = r`
  Right-deduplication:    `(r ⋓' s) ⋓' r = r ⋓' s`
  Associativity:          `(r ⋓' s) ⋓' t = r ⋓' (s ⋓' t)`

`unionAll x xs` folds the non-empty list `x :: xs` with `⋓'`.
-/

open EreqNormList

variable {α : Type*} [DecidableEq α]

namespace EreqNorm

/-- Rebuild a node from its first operand and the rest, deduplicating. -/
def mkUnionOf (x : EreqNorm α n) (xs : List (EreqNorm α n)) : EreqNorm α n :=
  fromList x (List.eraseAll x (smartDedup xs))

theorem wellFormed_mkUnionOf {x : EreqNorm α n} {xs : List (EreqNorm α n)}
    (hwf : ∀ w ∈ x :: xs, WellFormed w) (hflat : ∀ w ∈ x :: xs, isUnion w = false) :
    WellFormed (mkUnionOf x xs) := by
  refine fromList_wf ?_ ?_ ?_ <;> rw [← smartDedup_cons]
  · exact fun w hw => hwf w (by simpa using hw)
  · exact smartDedup_nodup
  · exact fun w hw => hflat w (by simpa using hw)

theorem toList_mkUnionOf {x : EreqNorm α n} (xs : List (EreqNorm α n))
    (h : isUnion x = false) : toList (mkUnionOf x xs) = smartDedup (x :: xs) := by
  rw [mkUnionOf, toList_fromList h, ← smartDedup_cons]

variable [Bot α]

/-- Smart union returns the other operand if one is `bot` and merges the operand lists
    otherwise.

    Dropping `bot` simplifies more than `≅` allows. This is safe, since it preserves the
    language, nullability, derivatives and well-formedness (`lang_mkUnion`,
    `nullable_mkUnion`, `derivative_mkUnion`, `wellFormed_mkUnion`). -/
def mkUnion (A B : EreqNorm α n) : EreqNorm α n :=
  if A = bot then B
  else if B = bot then A
  else mkUnionOf A.first (A.rest ++ toList B)

scoped infixr:65 " ⋓' " => mkUnion

@[simp] theorem mkUnion_bot_left (B : EreqNorm α n) : (bot ⋓' B) = B := by simp [mkUnion]

@[simp] theorem mkUnion_bot_right (A : EreqNorm α n) : (A ⋓' bot) = A := by
  by_cases h : A = bot <;> simp [mkUnion, h]

/-- If neither operand is `bot`, `A ⋓' B` merges their operand lists. -/
theorem mkUnion_of_ne_bot {A B : EreqNorm α n} (ha : A ≠ bot) (hb : B ≠ bot) :
    (A ⋓' B) = mkUnionOf A.first (A.rest ++ toList B) := by
  simp [mkUnion, ha, hb]

theorem wellFormed_mkUnion {A B : EreqNorm α n} (ha : WellFormed A) (hb : WellFormed B) :
    WellFormed (A ⋓' B) := by
  by_cases hna : A = bot
  · subst hna; simpa
  by_cases hnb : B = bot
  · subst hnb; simpa
  rw [mkUnion_of_ne_bot hna hnb]
  exact wellFormed_mkUnionOf
    (fun w hw => (mem_toList_append ha hb hw).1)
    (fun w hw => (mem_toList_append ha hb hw).2)

/-- If neither operand is `bot`, the operands of `a ⋓' b` are those of `a` and `b` without
    duplicates. -/
theorem toList_mkUnion {a b : EreqNorm α n} (ha : WellFormed a)
    (hna : a ≠ bot) (hnb : b ≠ bot) :
    toList (a ⋓' b) = smartDedup (toList a ++ toList b) := by
  rw [mkUnion_of_ne_bot hna hnb,
    toList_mkUnionOf _ (toList_not_isUnion ha _ (by simp [toList])), toList_append_eq]

/-- If `a` is not `bot`, neither is `a ⋓' b`. -/
theorem mkUnion_ne_bot {a b : EreqNorm α n} (ha : WellFormed a) (hna : a ≠ bot) :
    (a ⋓' b) ≠ bot := by
  by_cases hnb : b = bot
  · rw [hnb, mkUnion_bot_right _]; exact hna
  intro h
  have hl := toList_mkUnion ha hna hnb
  rw [h, toList_eq_self (by simp), toList_append_eq, smartDedup_cons] at hl
  obtain ⟨h1, h2⟩ := List.cons_eq_cons.mp hl
  cases a with
  | union x y zs =>
    have nd : (x :: y :: zs.toList).Nodup := by
      cases ha with | union _ nd _ => exact nd
    have hyx : y ≠ x := fun e => by simp [e] at nd
    have hy : y ∈ List.eraseAll x (smartDedup ((y :: zs.toList) ++ toList b)) := by
      rw [mem_eraseAll_iff]; exact ⟨by simp [mem_smartDedup_iff], hyx⟩
    simp only [first, rest] at h2
    rw [← h2] at hy
    simp at hy
  | _ => exact hna h1.symm

theorem mkUnion_idem {a : EreqNorm α n} (h : WellFormed a) : (a ⋓' a) = a := by
  by_cases hna : a = bot
  · rw [hna, mkUnion_bot_left]
  · exact eq_of_toList_eq
      (by rw [toList_mkUnion h hna hna, smartDedup_append_self (toList_nodup h)])

theorem mkUnion_dedup {a b : EreqNorm α n} (ha : WellFormed a) (hb : WellFormed b) :
    ((a ⋓' b) ⋓' a) = a ⋓' b := by
  by_cases hna : a = bot
  · subst hna; simp
  by_cases hnb : b = bot
  · subst hnb; simp [mkUnion_idem ha]
  have hab : WellFormed (a ⋓' b) := wellFormed_mkUnion ha hb
  have hnab : (a ⋓' b) ≠ bot := mkUnion_ne_bot ha hna
  have hsub : ∀ x ∈ toList a, x ∈ toList (a ⋓' b) := fun x hx => by
    rw [toList_mkUnion ha hna hnb, mem_smartDedup_iff]; exact List.mem_append_left _ hx
  exact eq_of_toList_eq
    (by rw [toList_mkUnion hab hnab hna, smartDedup_append_subset (toList_nodup hab) hsub])

/-- `⋓'` is associative when `a` and `b` are well-formed. -/
theorem mkUnion_assoc {a b c : EreqNorm α n} (ha : WellFormed a) (hb : WellFormed b) :
    ((a ⋓' b) ⋓' c) = (a ⋓' (b ⋓' c)) := by
  by_cases hna : a = bot
  · subst hna; simp
  by_cases hnb : b = bot
  · subst hnb; simp
  by_cases hnc : c = bot
  · subst hnc; simp
  apply eq_of_toList_eq
  rw [toList_mkUnion (wellFormed_mkUnion ha hb) (mkUnion_ne_bot ha hna) hnc,
    toList_mkUnion ha hna hnb,
    toList_mkUnion ha hna (mkUnion_ne_bot hb hnb), toList_mkUnion hb hnb hnc,
    smartDedup_assoc]

/-! ## The n-ary fold

The derivative of a union is `unionAll` over the derivatives of its operands
(`eval_derivative_toList`). Unlike `unionOf`, `unionAll` satisfies its laws up to `=`
rather than `≅`. Unlike in `Ere`, it takes the first operand separately, so the list is never
empty. -/

/-- `⋓'` folded over a non-empty list, given as its first element and the rest. -/
def unionAll : EreqNorm α n → List (EreqNorm α n) → EreqNorm α n
  | x, [] => x
  | x, y :: ys => x ⋓' unionAll y ys

@[simp] theorem unionAll_nil (x : EreqNorm α n) : unionAll x [] = x := rfl

@[simp] theorem unionAll_cons (x y : EreqNorm α n) (ys : List (EreqNorm α n)) :
    unionAll x (y :: ys) = x ⋓' unionAll y ys := rfl

theorem wellFormed_unionAll {x : EreqNorm α n} {xs : List (EreqNorm α n)}
    (hx : WellFormed x) (h : ∀ z ∈ xs, WellFormed z) : WellFormed (unionAll x xs) :=
  match xs with
  | [] => hx
  | y :: ys =>
    wellFormed_mkUnion hx
      (wellFormed_unionAll (h y (by simp)) (fun z hz => h z (by simp [hz])))

/-- Folding an append gives the smart union of the two folds. -/
theorem unionAll_append {x y : EreqNorm α n} {xs ys : List (EreqNorm α n)}
    (hx : WellFormed x) (h : ∀ z ∈ xs, WellFormed z) :
    unionAll x (xs ++ y :: ys) = unionAll x xs ⋓' unionAll y ys := by
  induction xs generalizing x with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have has : ∀ z ∈ as, WellFormed z := fun z hz => h z (by simp [hz])
    rw [List.cons_append, unionAll_cons, ih ha has, unionAll_cons,
      ← mkUnion_assoc hx (wellFormed_unionAll ha has)]

/-- A fold absorbs any operand it already contains. -/
theorem unionAll_absorb {x w : EreqNorm α n} {xs : List (EreqNorm α n)}
    (hx : WellFormed x) (h : ∀ z ∈ xs, WellFormed z) (hw : w ∈ x :: xs) :
    unionAll x xs ⋓' w = unionAll x xs := by
  induction xs generalizing x with
  | nil =>
    rw [List.mem_singleton] at hw
    subst hw; exact mkUnion_idem hx
  | cons a as ih =>
    have ha := h a (by simp)
    have has : ∀ z ∈ as, WellFormed z := fun z hz => h z (by simp [hz])
    have hU := wellFormed_unionAll ha has
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact mkUnion_dedup hx hU
    · rw [unionAll_cons, mkUnion_assoc hx hU, ih ha has hw']

/-- A repeated operand can be deleted anywhere in the list without changing the fold. -/
theorem unionAll_dedup {x w : EreqNorm α n} {xs ys : List (EreqNorm α n)}
    (hx : WellFormed x) (h : ∀ z ∈ xs, WellFormed z) (hwf : WellFormed w)
    (h' : ∀ z ∈ ys, WellFormed z) (hw : w ∈ x :: xs) :
    unionAll x (xs ++ w :: ys) = unionAll x (xs ++ ys) := by
  rw [unionAll_append hx h]
  match ys with
  | [] => rw [List.append_nil, unionAll_nil]; exact unionAll_absorb hx h hw
  | z :: zs =>
    rw [unionAll_cons, ← mkUnion_assoc (wellFormed_unionAll hx h) hwf,
      unionAll_absorb hx h hw, ← unionAll_append hx h]

/-! ### Unions of mapped lists

Stated for an arbitrary `g`, where the derivative uses `g := fun w => (ρₙ w)[c]ₙ`. -/
section Map
variable {β : Type*} [BEq β] [LawfulBEq β]

/-- Erasing every copy of `u` from `l₂` leaves the fold unchanged, provided `u` still occurs
    in `hd :: l₁`. -/
theorem unionAll_map_eraseAll (g : β → EreqNorm α n) {hd u : β} {l₁ l₂ : List β}
    (hwf : ∀ z ∈ hd :: (l₁ ++ l₂), WellFormed (g z)) (hu : u ∈ hd :: l₁) :
    unionAll (g hd) ((l₁ ++ List.eraseAll u l₂).map g)
      = unionAll (g hd) ((l₁ ++ l₂).map g) := by
  induction l₂ generalizing l₁ with
  | nil => rfl
  | cons a as ih =>
    by_cases hau : a = u
    · -- `a` is `u`: `eraseAll` drops it, and its copy in `hd :: l₁` absorbs it in the fold
      subst hau
      rw [eraseAll_cons_self, ih (fun z hz => hwf z (by simp at hz ⊢; tauto)) hu]
      have hmem : g a ∈ g hd :: l₁.map g := by
        rcases List.mem_cons.mp hu with rfl | h
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_map_of_mem h)
      have hmap : ∀ l ⊆ l₁ ++ a :: as, ∀ z ∈ l.map g, WellFormed z := fun l hl z hz => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
        exact hwf t (List.mem_cons_of_mem _ (hl ht))
      have := unionAll_dedup (x := g hd) (xs := l₁.map g) (w := g a) (ys := as.map g)
        (hwf hd (by simp)) (hmap l₁ (by simp)) (hwf a (by simp)) (hmap as (by simp)) hmem
      simpa using this.symm
    · -- `a` is not `u`: it stays, so move it into the prefix and use the induction hypothesis
      rw [eraseAll_cons_of_ne (Ne.symm hau)]
      have := ih (l₁ := l₁ ++ [a]) (fun z hz => hwf z (by simp at hz ⊢; tauto))
        (by rcases List.mem_cons.mp hu with rfl | h
            · simp
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ h))
      simpa using this

/-- Removing duplicates does not change the fold, which `derivative_mkUnion` relies on. -/
theorem unionAll_map_smartDedup (g : β → EreqNorm α n) {hd : β} {l : List β}
    (hwf : ∀ z ∈ hd :: l, WellFormed (g z)) :
    unionAll (g hd) ((smartDedup l).map g) = unionAll (g hd) (l.map g) := by
  induction l generalizing hd with
  | nil => rfl
  | cons a as ih =>
    rw [smartDedup_cons, List.map_cons, List.map_cons, unionAll_cons, unionAll_cons]
    congr 1
    have hwf' : ∀ z ∈ a :: as, WellFormed (g z) := fun z hz => hwf z (by simp at hz ⊢; tauto)
    -- Erasing the later copies of `a` does not change the fold
    have h1 := unionAll_map_eraseAll g (hd := a) (u := a) (l₁ := []) (l₂ := smartDedup as)
      (by intro z hz
          simp only [List.nil_append, List.mem_cons, mem_smartDedup_iff] at hz
          exact hwf' z (List.mem_cons.mpr hz))
      (by simp)
    simp only [List.nil_append] at h1
    rw [h1, ih (fun z hz => hwf' z (by simp at hz ⊢; tauto))]

end Map

end EreqNorm
