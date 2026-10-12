import Batteries.Data.UnionFind.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# A union-find keyed by an arbitrary hashable type

Batteries' `UnionFind` works on `Nat` nodes `0, …, size - 1`. `UfManager α` adds a
`HashMap α Nat` giving each key a node and `toNodeMap_inv` ensures that the nodes are
in range.

The equivalence checker only uses `merge`, specified by `merge_equiv_iff` and
`merge_eq_true_iff`.
-/

open Batteries Std

namespace Batteries.UnionFind

/-! ### Lemmas missing from Batteries -/

private theorem size_push {u : UnionFind} : u.push.size = u.size + 1 := by
  simp [UnionFind.push, UnionFind.size]

/-- `union` only changes parents, so it does not change the size. -/
private theorem size_union {u : UnionFind} {x y : Fin u.size} :
    (u.union x y).size = u.size := by
  simp [UnionFind.union, UnionFind.link, UnionFind.size]

/-- An index out of range is its own root. -/
private theorem rootD_of_not_lt {u : UnionFind} {i : Nat} (h : ¬ i < u.size) :
    u.rootD i = i := by
  simp [UnionFind.rootD, h]

/-- An index out of range is related to nothing but itself. -/
private theorem equiv_iff_eq_of_not_lt {u : UnionFind} {i j : Nat}
    (h : ¬ i < u.size ∨ ¬ j < u.size) : u.Equiv i j ↔ i = j := by
  unfold UnionFind.Equiv
  by_cases hi : i < u.size <;> by_cases hj : j < u.size
  · omega
  · -- The root of `i` is in range but `j` is not
    have hri := rootD_lt.mpr hi
    rw [rootD_of_not_lt hj]
    omega
  · -- The root of `j` is in range but `i` is not
    have hrj := rootD_lt.mpr hj
    rw [rootD_of_not_lt hi]
    omega
  · rw [rootD_of_not_lt hi, rootD_of_not_lt hj]

/-- The next pushed node, `u.size`, is not related to any existing node. -/
private theorem not_equiv_size {u : UnionFind} {k : Nat} (hk : k < u.size) :
    ¬ u.Equiv u.size k := by
  rw [equiv_iff_eq_of_not_lt (.inl (Nat.lt_irrefl _))]; omega

end Batteries.UnionFind

universe u

variable {α : Type u} [BEq α] [Hashable α]

structure UfManager (α : Type u) [BEq α] [Hashable α] where
  uf : UnionFind := {}
  toNodeMap : HashMap α Nat := {}
  toNodeMap_inv : ∀ (r : α) i, toNodeMap[r]? = some i → i < uf.size

namespace UfManager

def empty : UfManager α := ⟨{}, {}, by simp⟩

/-- The representative of `s` is its root if inserted and `s` itself otherwise. -/
def rootOf (uf : UfManager α) (s : α) : α ⊕ Nat :=
  match uf.toNodeMap[s]? with
  | some i => .inr (uf.uf.rootD i)
  | none => .inl s

/-- `p` and `q` have the same representative. -/
def Equiv (uf : UfManager α) (p q : α) : Prop :=
  uf.rootOf p = uf.rootOf q

/-- `Equiv` in terms of nodes. -/
private theorem equiv_iff {uf : UfManager α} {p q : α} :
    uf.Equiv p q ↔
      p = q ∨ ∃ i j, uf.toNodeMap[p]? = some i ∧ uf.toNodeMap[q]? = some j ∧ uf.uf.Equiv i j := by
  by_cases h : p = q
  · simp [h, Equiv]
  · -- Compare representatives, splitting on whether `p` and `q` have nodes
    unfold Equiv rootOf
    cases uf.toNodeMap[p]? <;> cases uf.toNodeMap[q]? <;> simp [h, UnionFind.Equiv]

private theorem Equiv.of_indices {uf : UfManager α} {p q : α} {i j : Nat}
    (hi : uf.toNodeMap[p]? = some i) (hj : uf.toNodeMap[q]? = some j)
    (h : uf.uf.Equiv i j) : uf.Equiv p q :=
  equiv_iff.mpr (.inr ⟨i, j, hi, hj, h⟩)

theorem Equiv.refl {uf : UfManager α} {x : α} : uf.Equiv x x := rfl

theorem Equiv.symm {uf : UfManager α} {x y : α} :
    uf.Equiv x y → uf.Equiv y x := Eq.symm

theorem Equiv.trans {uf : UfManager α} {x y z : α} :
    uf.Equiv x y → uf.Equiv y z → uf.Equiv x z := Eq.trans

/-- `Equiv` is an equivalence relation. -/
theorem Equiv.isEquivalence (uf : UfManager α) : Equivalence uf.Equiv :=
  ⟨fun _ => .refl, .symm, .trans⟩

/-- Linking `a` and `b` adds nothing if they are already related. -/
private theorem or_link_iff_of_equiv {uf : UfManager α} {a b p q : α} (h : uf.Equiv a b) :
    (uf.Equiv p q ∨ (uf.Equiv p a ∧ uf.Equiv b q) ∨ (uf.Equiv p b ∧ uf.Equiv a q)) ↔
      uf.Equiv p q := by
  refine ⟨?_, .inl⟩
  rintro (g | ⟨g1, g2⟩ | ⟨g1, g2⟩)
  · exact g
  · exact g1.trans (h.trans g2)
  · exact g1.trans (h.symm.trans g2)

/-! ## The node level -/

/-- Checks if `x` and `y` have the same root and returns the path-compressed manager. -/
private def sameRoot (uf : UfManager α) (x y : Fin uf.uf.size) : UfManager α × Bool :=
  let ⟨uf_x, rx, hrx⟩ := uf.uf.find x
  let ⟨uf_y, ry, hry⟩ := uf_x.find ⟨y, by rw [hrx]; exact y.isLt⟩
  (⟨uf_y, uf.toNodeMap, fun r i hi => by rw [hry, hrx]; exact uf.toNodeMap_inv r i hi⟩,
   rx.val = ry.val)

private theorem sameRoot_eq_true_iff {uf : UfManager α} {x y : Fin uf.uf.size} :
    (sameRoot uf x y).2 = true ↔ uf.uf.Equiv x y := by
  unfold sameRoot UnionFind.Equiv
  simp

/-- Path compression does not change the partition. -/
@[simp] private theorem equiv_sameRoot {uf : UfManager α} {x y : Fin uf.uf.size} {p q : α} :
    (sameRoot uf x y).1.Equiv p q ↔ uf.Equiv p q := by
  rw [equiv_iff, equiv_iff]
  unfold sameRoot
  simp [UnionFind.equiv_find]

/-- Checks if the nodes `i` and `j` are in one class. A node out of range counts as a
    singleton, hence the fallback `i == j`. -/
private def checkEquiv (uf : UfManager α) (i j : Nat) : UfManager α × Bool :=
  if hi : i < uf.uf.size then
    if hj : j < uf.uf.size then sameRoot uf ⟨i, hi⟩ ⟨j, hj⟩
    else (uf, i == j)
  else (uf, i == j)

/-- Merges the classes of the nodes `i` and `j`. -/
private def union (uf : UfManager α) (i j : Fin uf.uf.size) : UfManager α where
  uf := uf.uf.union i j
  toNodeMap := uf.toNodeMap
  toNodeMap_inv r k hk := by rw [UnionFind.size_union]; exact uf.toNodeMap_inv r k hk

/-- Merges the classes of `i` and `j` unless one of them is out of range. -/
private def link (uf : UfManager α) (i j : Nat) : UfManager α :=
  if hi : i < uf.uf.size then
    if hj : j < uf.uf.size then uf.union ⟨i, hi⟩ ⟨j, hj⟩
    else uf
  else uf

@[simp] private theorem toNodeMap_checkEquiv {uf : UfManager α} {i j : Nat} :
    (uf.checkEquiv i j).1.toNodeMap = uf.toNodeMap := by
  unfold checkEquiv; split <;> (try split) <;> rfl

@[simp] private theorem equiv_checkEquiv {uf : UfManager α} {i j : Nat} {x y : α} :
    (uf.checkEquiv i j).1.Equiv x y ↔ uf.Equiv x y := by
  unfold checkEquiv; split <;> (try split) <;> simp

/-- `checkEquiv` returns `true` exactly when Batteries' `Equiv` holds. -/
@[simp] private theorem checkEquiv_eq_true_iff {uf : UfManager α} {i j : Nat} :
    (uf.checkEquiv i j).2 = true ↔ uf.uf.Equiv i j := by
  unfold checkEquiv
  split
  · split
    · exact sameRoot_eq_true_iff
    next hj => simp [UnionFind.equiv_iff_eq_of_not_lt (.inr hj)]
  next hi => simp [UnionFind.equiv_iff_eq_of_not_lt (.inl hi)]

/-- `checkEquiv_eq_true_iff` but stated for the keys on nodes `i` and `j`. -/
private theorem checkEquiv_eq_true_iff_of_getElem? {uf : UfManager α} {p q : α}
    {i j : Nat} (hp : uf.toNodeMap[p]? = some i) (hq : uf.toNodeMap[q]? = some j) :
    (uf.checkEquiv i j).2 = true ↔ uf.Equiv p q := by
  rw [checkEquiv_eq_true_iff, equiv_iff]
  constructor
  · intro h
    exact .inr ⟨i, j, hp, hq, h⟩
  · rintro (rfl | ⟨i', j', hi', hj', h⟩)
    · -- `p` and `q` are the same key, so they have the same node
      obtain rfl : i = j := Option.some.inj (hp.symm.trans hq)
      exact .rfl
    · -- The nodes found for `p` and `q` are `i` and `j`
      obtain rfl : i = i' := Option.some.inj (hp.symm.trans hi')
      obtain rfl : j = j' := Option.some.inj (hq.symm.trans hj')
      exact h

/-- `p` and `q` become related if they were already related, or if the
    new link between `tl` and `tr` joins them. -/
private theorem link_equiv_iff {uf : UfManager α} {tl tr p q : α} {i j : Nat}
    (htl : uf.toNodeMap[tl]? = some i) (htr : uf.toNodeMap[tr]? = some j) :
    (uf.link i j).Equiv p q ↔
      uf.Equiv p q ∨ (uf.Equiv p tl ∧ uf.Equiv tr q) ∨ (uf.Equiv p tr ∧ uf.Equiv tl q) := by
  have hi := uf.toNodeMap_inv _ _ htl
  have hj := uf.toNodeMap_inv _ _ htr
  unfold link
  simp only [hi, hj]
  -- everything already related stays related
  have mono {x y : α} (h : uf.Equiv x y) : (uf.union ⟨i, hi⟩ ⟨j, hj⟩).Equiv x y := by
    rcases equiv_iff.mp h with rfl | ⟨a, b, ha, hb, hab⟩
    · exact .refl
    · exact .of_indices ha hb (UnionFind.equiv_union.mpr (.inl hab))
  have tl_tr : (uf.union ⟨i, hi⟩ ⟨j, hj⟩).Equiv tl tr :=
    .of_indices htl htr (UnionFind.equiv_union.mpr (.inr (.inl ⟨.rfl, .rfl⟩)))
  constructor
  · intro h
    rcases equiv_iff.mp h with rfl | ⟨a, b, ha, hb, hab⟩
    · exact .inl .refl
    rcases UnionFind.equiv_union.mp hab with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl (.of_indices ha hb h)
    · exact .inr (.inl ⟨.of_indices ha htl h1, .of_indices htr hb h2⟩)
    · exact .inr (.inr ⟨.of_indices ha htr h1, .of_indices htl hb h2⟩)
  · rintro (g | ⟨g1, g2⟩ | ⟨g1, g2⟩)
    · exact mono g
    · exact (mono g1).trans (tl_tr.trans (mono g2))
    · exact (mono g1).trans (tl_tr.symm.trans (mono g2))

section LawfulBEq
variable [LawfulBEq α]

/-! ## Inserting keys -/

/-- Give `r` a node if it does not have one, and return that node. -/
private def insertNode (uf : UfManager α) (r : α) : UfManager α × Nat :=
  match uf.toNodeMap[r]? with
  | some i => (uf, i)
  | none =>
    ({ uf := uf.uf.push,
       toNodeMap := uf.toNodeMap.insert r uf.uf.size,
       toNodeMap_inv := fun r' ri hri => by
         rw [Std.HashMap.getElem?_insert] at hri
         rw [UnionFind.size_push]
         split at hri
         · -- `r'` is the key just inserted, so it maps to the fresh node
           obtain rfl : ri = uf.uf.size := (Option.some.inj hri).symm
           omega
         · exact Nat.lt_succ_of_lt (uf.toNodeMap_inv r' ri hri) },
     uf.uf.size)

private theorem insertNode_of_getElem?_eq_some {uf : UfManager α} {r : α} {i : Nat}
    (h : uf.toNodeMap[r]? = some i) : uf.insertNode r = (uf, i) := by
  unfold insertNode; rw [h]

private theorem uf_insertNode {uf : UfManager α} {r : α} (h : uf.toNodeMap[r]? = none) :
    (uf.insertNode r).1.uf = uf.uf.push := by
  unfold insertNode; rw [h]

private theorem toNodeMap_insertNode {uf : UfManager α} {r : α} (h : uf.toNodeMap[r]? = none) :
    (uf.insertNode r).1.toNodeMap = uf.toNodeMap.insert r uf.uf.size := by
  unfold insertNode; rw [h]

private theorem snd_insertNode {uf : UfManager α} {r : α} (h : uf.toNodeMap[r]? = none) :
    (uf.insertNode r).2 = uf.uf.size := by
  unfold insertNode; rw [h]

@[simp] private theorem getElem?_insertNode_of_ne {uf : UfManager α} {r s : α}
    (h : s ≠ r) : (uf.insertNode r).1.toNodeMap[s]? = uf.toNodeMap[s]? := by
  cases hr : uf.toNodeMap[r]? with
  | some i => rw [insertNode_of_getElem?_eq_some hr]
  | none => simp [toNodeMap_insertNode hr, Std.HashMap.getElem?_insert, Ne.symm h]

/-- The node `insertNode` returns is the one `r` has afterwards. -/
@[simp] private theorem getElem?_insertNode_self {uf : UfManager α} {r : α} :
    (uf.insertNode r).1.toNodeMap[r]? = some (uf.insertNode r).2 := by
  cases hr : uf.toNodeMap[r]? with
  | some i => rw [insertNode_of_getElem?_eq_some hr]; exact hr
  | none => simp [toNodeMap_insertNode hr, snd_insertNode hr]

/-- Inserting a key neither creates nor removes any equivalence, because the new node is in a
    class of its own. -/
@[simp] private theorem insertNode_equiv {uf : UfManager α} {r x y : α} :
    (uf.insertNode r).1.Equiv x y ↔ uf.Equiv x y := by
  cases hr : uf.toNodeMap[r]? with
  | some i => rw [insertNode_of_getElem?_eq_some hr]
  | none =>
    -- `r` gets the fresh node `uf.uf.size`, which `push` isolates
    have hself : (uf.insertNode r).1.toNodeMap[r]? = some uf.uf.size := by
      rw [getElem?_insertNode_self, snd_insertNode hr]
    rw [equiv_iff, equiv_iff, uf_insertNode hr]
    constructor
    · rintro (rfl | ⟨i, j, hi, hj, hij⟩)
      · exact .inl rfl
      rw [UnionFind.equiv_push] at hij
      by_cases hx : x = r <;> by_cases hy : y = r
      · -- Both are `r`
        exact .inl (hx.trans hy.symm)
      · -- Only `x` is `r`, so it has the fresh node, which is related to no older node
        subst hx
        obtain rfl : uf.uf.size = i := Option.some.inj (hself.symm.trans hi)
        rw [getElem?_insertNode_of_ne hy] at hj
        exact absurd hij (UnionFind.not_equiv_size (uf.toNodeMap_inv _ _ hj))
      · -- Only `y` is `r`, which is symmetric
        subst hy
        obtain rfl : uf.uf.size = j := Option.some.inj (hself.symm.trans hj)
        rw [getElem?_insertNode_of_ne hx] at hi
        exact absurd hij.symm (UnionFind.not_equiv_size (uf.toNodeMap_inv _ _ hi))
      · -- Neither is `r`, so both keep their old nodes
        rw [getElem?_insertNode_of_ne hx] at hi
        rw [getElem?_insertNode_of_ne hy] at hj
        exact .inr ⟨i, j, hi, hj, hij⟩
    · rintro (rfl | ⟨i, j, hi, hj, hij⟩)
      · exact .inl rfl
      have hx : x ≠ r := by rintro rfl; simp [hr] at hi
      have hy : y ≠ r := by rintro rfl; simp [hr] at hj
      refine .inr ⟨i, j, ?_, ?_, UnionFind.equiv_push.mpr hij⟩
      · rwa [getElem?_insertNode_of_ne hx]
      · rwa [getElem?_insertNode_of_ne hy]

/-! ## The pair level: `merge` -/

/-- Links `p` and `q` unless they are already in one class and returns whether it linked. -/
def merge (uf : UfManager α) (p q : α) : UfManager α × Bool :=
  if p == q then
    (uf, false)
  else
    -- `match` instead of `let` so the manager is not shared and updates in place
    match uf.insertNode p with
    | (uf₁, i) =>
      match uf₁.insertNode q with
      | (uf₂, j) =>
        match uf₂.checkEquiv i j with
        | (uf₃, true) => (uf₃, false)    -- already in one class: nothing to do
        | (uf₃, false) => (uf₃.link i j, true)

/-- `merge` written with `let` instead of `match`, which is easier to use in proofs. -/
private theorem merge_def (uf : UfManager α) (p q : α) :
    uf.merge p q =
      if p == q then
        (uf, false)
      else
        let ip := uf.insertNode p
        let iq := ip.1.insertNode q
        let res := iq.1.checkEquiv ip.2 iq.2
        if res.2 then (res.1, false) else (res.1.link ip.2 iq.2, true) := by
  unfold merge
  split
  · rfl
  · dsimp only
    rcases uf.insertNode p with ⟨uf₁, i⟩
    rcases uf₁.insertNode q with ⟨uf₂, j⟩
    rcases uf₂.checkEquiv i j with ⟨uf₃, _ | _⟩ <;> rfl

/-- After inserting distinct `tl` and `tr`, each maps to the node its insertion returned. -/
private theorem getElem?_insertNode_insertNode {uf : UfManager α} {tl tr : α}
    (hne : tl ≠ tr) :
    ((uf.insertNode tl).1.insertNode tr).1.toNodeMap[tl]? = some (uf.insertNode tl).2 ∧
    ((uf.insertNode tl).1.insertNode tr).1.toNodeMap[tr]? =
      some ((uf.insertNode tl).1.insertNode tr).2 :=
  ⟨by rw [getElem?_insertNode_of_ne hne, getElem?_insertNode_self], getElem?_insertNode_self⟩

/-- After merging `tl` and `tr`, two states are related if they were already related or if
    they are connected through the new link. -/
theorem merge_equiv_iff {uf : UfManager α} {tl tr p q : α} :
    (uf.merge tl tr).1.Equiv p q ↔
      uf.Equiv p q ∨ (uf.Equiv p tl ∧ uf.Equiv tr q) ∨ (uf.Equiv p tr ∧ uf.Equiv tl q) := by
  rw [merge_def]
  by_cases h : tl = tr
  · -- Merging a state with itself changes nothing
    subst h
    simp only [beq_self_eq_true]
    exact (or_link_iff_of_equiv .refl).symm
  · simp only [beq_iff_eq, h, ↓reduceIte]
    obtain ⟨htl, htr⟩ := getElem?_insertNode_insertNode (uf := uf) h
    split
    next hchk =>
      -- `tl` and `tr` are already related, so nothing is linked
      have hrel : uf.Equiv tl tr := by
        simpa using (checkEquiv_eq_true_iff_of_getElem? htl htr).mp hchk
      simp only [equiv_checkEquiv, insertNode_equiv]
      exact (or_link_iff_of_equiv hrel).symm
    · -- `tl` and `tr` are not yet related, so their classes are linked
      rw [link_equiv_iff (tl := tl) (tr := tr)]
      · simp
      -- The two keys keep their nodes after `checkEquiv`
      · rw [toNodeMap_checkEquiv]; exact htl
      · rw [toNodeMap_checkEquiv]; exact htr

/-- A merge links exactly when the pair was not already related. -/
@[simp] theorem merge_eq_true_iff {uf : UfManager α} {p q : α} :
    (uf.merge p q).2 = true ↔ ¬ uf.Equiv p q := by
  rw [merge_def]
  by_cases h : p = q
  · -- Merging a state with itself never links
    subst h
    simp [Equiv.refl]
  · simp only [beq_iff_eq, h, ↓reduceIte]
    obtain ⟨hp, hq⟩ := getElem?_insertNode_insertNode (uf := uf) h
    have hchk := checkEquiv_eq_true_iff_of_getElem? hp hq
    simp only [insertNode_equiv] at hchk
    split
    next hres => simpa using hchk.mp hres
    next hres => simpa [hchk] using hres

/-! ### Corollaries -/

/-- A merge always leaves the pair related, whether it linked or not. -/
theorem merge_equiv_self {uf : UfManager α} {rx ry : α} :
    (uf.merge rx ry).1.Equiv rx ry :=
  merge_equiv_iff.mpr (.inr (.inl ⟨.refl, .refl⟩))

/-- A merge preserves every equivalence. -/
theorem merge_equiv_of_equiv {uf : UfManager α} {a b p q : α}
    (h : uf.Equiv p q) : (uf.merge a b).1.Equiv p q :=
  merge_equiv_iff.mpr (.inl h)

/-- A merge that did not link found the pair already related. -/
theorem equiv_of_merge_eq_false {uf : UfManager α} {p q : α}
    (h : (uf.merge p q).2 = false) : uf.Equiv p q := by
  apply Classical.byContradiction
  intro hcon
  simp [merge_eq_true_iff.mpr hcon] at h

/-- A merge that did not link leaves `Equiv` unchanged, since it only inserted nodes and
    compressed paths. -/
theorem equiv_merge_iff_of_eq_false {uf : UfManager α} {p q x y : α}
    (h : (uf.merge p q).2 = false) :
    (uf.merge p q).1.Equiv x y ↔ uf.Equiv x y := by
  rw [merge_equiv_iff]
  exact or_link_iff_of_equiv (equiv_of_merge_eq_false h)

/-- The empty manager relates only equal states. -/
@[simp] theorem empty_equiv_iff {x y : α} :
    (empty : UfManager α).Equiv x y ↔ x = y := by
  simp [empty, Equiv, rootOf]

/-- Merging `p` and `q` into the empty manager relates each state to itself and `p` to `q`,
    and nothing else. -/
theorem merge_empty_equiv_iff {p q x y : α} :
    ((empty : UfManager α).merge p q).1.Equiv x y ↔
      x = y ∨ (x = p ∧ y = q) ∨ (x = q ∧ y = p) := by
  rw [merge_equiv_iff]
  simp [eq_comm (a := q), eq_comm (a := p)]

end LawfulBEq

end UfManager
