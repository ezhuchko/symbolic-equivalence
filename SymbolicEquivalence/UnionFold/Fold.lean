import SymbolicEquivalence.SmartDedup

/-!
# Folding a list into a union

`fold union bot [a, b, c]` is `union a (union b c)`. The lemmas hold for any `union` satisfying the
laws `UnionSim`. The main theorem is `fold_map_smartDedup` which says that removing duplicate
operands does not change a fold, up to `Sim`. -/

namespace UnionFold

variable {E : Type _}

/-! ## The fold -/

/-- Folds a list into a right-nested `union`. `bot` is used only for the empty list, so `[a]`
folds to `a`, not `union a bot`. -/
def fold (union : E → E → E) (bot : E) : List E → E
  | []  => bot
  | [a] => a
  | a :: b :: bs => union a (fold union bot (b :: bs))

@[simp] theorem fold_nil (union : E → E → E) (bot : E) : fold union bot [] = bot := rfl

@[simp] theorem fold_singleton (union : E → E → E) (bot a : E) : fold union bot [a] = a := rfl

@[simp] theorem fold_cons_cons (union : E → E → E) (bot a b : E) (bs : List E) :
    fold union bot (a :: b :: bs) = union a (fold union bot (b :: bs)) := rfl

/-- If the tail is non-empty, `fold` of a cons is a `union`. -/
theorem fold_cons (union : E → E → E) (bot a : E) {as : List E} (h : as ≠ []) :
    fold union bot (a :: as) = union a (fold union bot as) := by
  match as with
  | _ :: _ => rfl

/-! ## The laws -/

/-- The laws of `union` up to `Sim` that the fold lemmas below rely on. -/
class UnionSim (union : E → E → E) (Sim : E → E → Prop) : Prop where
  /-- `Sim` is reflexive. -/
  refl {R : E} : Sim R R
  /-- `Sim` is symmetric. -/
  symm {R₁ R₂ : E} : Sim R₁ R₂ → Sim R₂ R₁
  /-- `Sim` is transitive. -/
  trans {R R₁ R₂ : E} : Sim R R₁ → Sim R₁ R₂ → Sim R R₂
  /-- `Sim` is a congruence for `union`. -/
  union_cong {R₁ R₂ S₁ S₂ : E} : Sim R₁ R₂ → Sim S₁ S₂ → Sim (union R₁ S₁) (union R₂ S₂)
  /-- `union` is associative up to `Sim`. -/
  assoc {R₁ R₂ R₃ : E} : Sim (union (union R₁ R₂) R₃) (union R₁ (union R₂ R₃))
  /-- `union` is idempotent up to `Sim`. -/
  idem {R : E} : Sim (union R R) R
  /-- An operand may be deleted from the end of a fold that already starts with it. -/
  dedup {R₁ R₂ : E} : Sim (union R₁ (union R₂ R₁)) (union R₁ R₂)

variable {union : E → E → E} {Sim : E → E → Prop} [i : UnionSim union Sim]

/-! ## Similarity of `union`-folds -/

/-- Splitting a fold at an append, up to `Sim`. -/
theorem fold_append (bot : E) {xs ys : List E} (hx : xs ≠ []) (hy : ys ≠ []) :
    Sim (fold union bot (xs ++ ys)) (union (fold union bot xs) (fold union bot ys)) := by
  match xs with
  | [x] =>
    rw [List.singleton_append, fold_cons union bot x hy]
    exact i.refl
  | x :: x' :: xs =>
    have ih := fold_append bot (xs := x' :: xs) (by simp) hy
    simp only [List.cons_append, fold_cons_cons] at ih ⊢
    exact i.trans (i.union_cong i.refl ih) (i.symm i.assoc)

/-- Folds of two lists with non-empty tails are similar if their heads and the folds of
their tails are similar. -/
theorem fold_cons_cong (bot : E) {x y : E} {xs ys : List E} (hx : xs ≠ []) (hy : ys ≠ [])
    (hxy : Sim x y) (hs : Sim (fold union bot xs) (fold union bot ys)) :
    Sim (fold union bot (x :: xs)) (fold union bot (y :: ys)) := by
  rw [fold_cons union bot x hx, fold_cons union bot y hy]
  exact i.union_cong hxy hs

/-- A fold absorbs any operand it already contains. -/
private theorem fold_absorb_mem (bot : E) {x : E} {xs : List E} (h : x ∈ xs) :
    Sim (union (fold union bot xs) x) (fold union bot xs) := by
  match xs with
  | [] => simp at h
  | [y] =>
    obtain rfl := List.mem_singleton.mp h
    exact i.idem
  | y :: y' :: ys =>
    rw [fold_cons_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact i.trans i.assoc i.dedup
    · exact i.trans i.assoc (i.union_cong i.refl (fold_absorb_mem bot h))

/-- If `x` occurs in `l₁`, a later copy of `x` can be deleted anywhere, not only at the end
as in `dedup`, up to `Sim`. -/
private theorem fold_dedup (bot : E) {x : E} {l₁ l₂ : List E} (h : x ∈ l₁) :
    Sim (fold union bot (l₁ ++ x :: l₂)) (fold union bot (l₁ ++ l₂)) := by
  have h1 : l₁ ≠ [] := List.ne_nil_of_mem h
  have habs : Sim (union (fold union bot l₁) x) (fold union bot l₁) := fold_absorb_mem bot h
  match l₂ with
  | [] =>
    rw [List.append_nil]
    exact i.trans (fold_append bot (ys := [x]) h1 (by simp)) habs
  | y :: ys =>
    refine i.trans (fold_append bot h1 (by simp)) ?_
    rw [fold_cons_cons]
    exact i.trans (i.symm i.assoc)
          (i.trans (i.union_cong habs i.refl) (i.symm (fold_append bot h1 (by simp))))

/-! ## Folds of mapped lists

Deduplicating `l` before folding `l.map g` preserves the fold, up to `Sim`. -/

section Map

variable {β : Type _} [BEq β] [LawfulBEq β]

/-- Erasing from `l₂` an operand already in `l₁` preserves the fold, up to `Sim`. -/
private theorem fold_map_eraseAll (bot : E) (g : β → E) {x : β} {l₁ l₂ : List β}
    (h : x ∈ l₁) :
    Sim (fold union bot ((l₁ ++ List.eraseAll x l₂).map g))
      (fold union bot ((l₁ ++ l₂).map g)) := by
  match l₂ with
  | [] => exact i.refl
  | a :: as =>
    by_cases hax : a = x
    · subst hax
      rw [eraseAll_cons_self]
      have hd : Sim (fold union bot ((l₁ ++ a :: as).map g))
          (fold union bot ((l₁ ++ as).map g)) := by
        simpa using fold_dedup (Sim := Sim) bot (l₂ := as.map g) (List.mem_map_of_mem h)
      exact i.trans (fold_map_eraseAll bot g (l₂ := as) h) (i.symm hd)
    · rw [eraseAll_cons_of_ne (Ne.symm hax)]
      simpa using fold_map_eraseAll bot g (x := x) (l₁ := l₁ ++ [a]) (l₂ := as)
        (List.mem_append_left _ h)

/-- Removing duplicates from a list does not change its fold, up to `Sim`. -/
theorem fold_map_smartDedup (bot : E) (g : β → E) (xs : List β) :
    Sim (fold union bot ((smartDedup xs).map g)) (fold union bot (xs.map g)) := by
  match xs with
  | [] => exact i.refl
  | x :: xs =>
    have hstep : Sim (fold union bot ((x :: List.eraseAll x (smartDedup xs)).map g))
        (fold union bot ((x :: smartDedup xs).map g)) := by
      simpa using
        fold_map_eraseAll bot g (x := x) (l₁ := [x]) (l₂ := smartDedup xs) (by simp)
    have htail : Sim (fold union bot ((x :: smartDedup xs).map g))
        (fold union bot ((x :: xs).map g)) := by
      by_cases hne : xs = []
      · subst hne; exact i.refl
      · simp only [List.map_cons]
        exact fold_cons_cong bot (by simpa using smartDedup_ne_nil hne) (by simpa using hne)
          i.refl (fold_map_smartDedup bot g xs)
    rw [smartDedup_cons]
    exact i.trans hstep htail

end Map

end UnionFold
