import SymbolicEquivalence.UnionFind.UfManager
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

/-!
# Counting classes after a merge

The equivalence checker terminates because each merge that links two classes decreases the number
of classes (`UfManager.numClasses`).
-/

namespace Finset

variable {ι β : Type*} [DecidableEq β] {L : Finset ι} {f g : ι → β}

/-- If elements with the same `f`-value also have the same `g`-value (`coarser`), the pair
    `(f x, g x)` carries no more information than `f x`, so there are as many distinct
    pairs as distinct `f`-values. -/
private theorem card_image_pair (coarser : ∀ x ∈ L, ∀ y ∈ L, f x = f y → g x = g y) :
    (L.image fun x => (f x, g x)).card = (L.image f).card := by
  let P := L.image fun x => (f x, g x)
  -- dropping the second component maps the pairs onto the `f`-values
  have himage : P.image Prod.fst = L.image f := by rw [Finset.image_image]; rfl
  -- taking the first component is injective on the pairs: if two pairs agree on `f x`,
  -- they also agree on `g x` (by `coarser`), so they are the same pair
  have hinj : Set.InjOn Prod.fst (P : Set (β × β)) := by
    intro p hp q hq h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact Prod.ext h (coarser x hx y hy h)
  rw [← himage, Finset.card_image_of_injOn hinj]

/-- Dropping the first component of each pair leaves the `g`-values. -/
private theorem image_snd_image_pair :
    (L.image fun x => (f x, g x)).image Prod.snd = L.image g := by
  rw [Finset.image_image]; rfl

/-- Joining classes never increases their number. -/
theorem card_image_le_of_coarser (coarser : ∀ x ∈ L, ∀ y ∈ L, f x = f y → g x = g y) :
    (L.image g).card ≤ (L.image f).card := by
  rw [← card_image_pair coarser, ← image_snd_image_pair (f := f)]
  exact Finset.card_image_le

/-- Joining the classes of `a` and `b`, which were different, decreases their number. -/
theorem card_image_lt_of_collapse {a b : ι}
    (coarser : ∀ x ∈ L, ∀ y ∈ L, f x = f y → g x = g y)
    (ha : a ∈ L) (hb : b ∈ L) (hfne : f a ≠ f b) (hgeq : g a = g b) :
    (L.image g).card < (L.image f).card := by
  rw [← card_image_pair coarser, ← image_snd_image_pair (f := f)]
  apply lt_of_le_of_ne Finset.card_image_le
  -- Equal sizes would make `Prod.snd` injective on the pairs, but the pairs of `a` and `b`
  -- differ (`f a ≠ f b`) while having the same `Prod.snd` (`g a = g b`)
  intro hcard
  have hinj := Finset.card_image_iff.mp hcard
  have hab := hinj (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb) hgeq
  exact hfne (congrArg Prod.fst hab)

end Finset

namespace UfManager

variable {α : Type*} [BEq α] [Hashable α]

/-! ## Counting classes

The termination measure counts classes among a fixed finite set `L` of keys, fixed
because the manager keeps growing. -/

open scoped Classical in
/-- The termination measure is the number of classes among the keys in `L`. -/
noncomputable def numClasses (uf : UfManager α) (L : Finset α) : Nat :=
  (L.image uf.rootOf).card

/-- If `L` contains a key `a`, there is at least one class (the class of `a`). -/
theorem numClasses_pos {uf : UfManager α} {L : Finset α} {a : α} (ha : a ∈ L) :
    0 < uf.numClasses L := by
  classical exact Finset.card_pos.mpr (Finset.image_nonempty.mpr ⟨a, ha⟩)

/-- There are at most as many classes as keys in `L`. -/
theorem numClasses_le_card {uf : UfManager α} {L : Finset α} :
    uf.numClasses L ≤ L.card := by
  classical exact Finset.card_image_le

/-- If `uf'` relates everything `uf` relates, it has at most as many classes. -/
private theorem numClasses_le_of_mono {uf uf' : UfManager α} {L : Finset α}
    (h : ∀ x ∈ L, ∀ y ∈ L, uf.Equiv x y → uf'.Equiv x y) :
    uf'.numClasses L ≤ uf.numClasses L := by
  classical exact Finset.card_image_le_of_coarser h

/-- If `uf'` relates everything `uf` relates and also two keys of `L` that `uf` did not, it
    has strictly fewer classes. -/
private theorem numClasses_lt_of_merge {uf uf' : UfManager α} {L : Finset α} {a b : α}
    (ha : a ∈ L) (hb : b ∈ L)
    (hmono : ∀ x y, uf.Equiv x y → uf'.Equiv x y)
    (hold : ¬ uf.Equiv a b) (hnew : uf'.Equiv a b) :
    uf'.numClasses L < uf.numClasses L := by
  classical
  exact Finset.card_image_lt_of_collapse (fun x _ y _ hxy => hmono x y hxy) ha hb hold hnew

section LawfulBEq
variable [LawfulBEq α]

/-! ### The class count of a merge -/

/-- A merge never increases the class count. -/
theorem numClasses_merge_le {uf : UfManager α} {a b : α} {L : Finset α} :
    (uf.merge a b).1.numClasses L ≤ uf.numClasses L :=
  numClasses_le_of_mono fun _ _ _ _ h => merge_equiv_of_equiv h

/-- A merge that did not link keeps the class count exactly. -/
theorem numClasses_merge_eq {uf : UfManager α} {a b : α} {L : Finset α}
    (h : (uf.merge a b).2 = false) :
    (uf.merge a b).1.numClasses L = uf.numClasses L :=
  Nat.le_antisymm numClasses_merge_le
    (numClasses_le_of_mono fun _ _ _ _ hxy => (equiv_merge_iff_of_eq_false h).mp hxy)

/-- A merge that linked two states of the fixed set strictly decreases the class count. -/
theorem numClasses_merge_lt {uf : UfManager α} {a b : α} {L : Finset α}
    (ha : a ∈ L) (hb : b ∈ L) (h : (uf.merge a b).2 = true) :
    (uf.merge a b).1.numClasses L < uf.numClasses L :=
  numClasses_lt_of_merge ha hb (fun _ _ => merge_equiv_of_equiv)
    (merge_eq_true_iff.mp h) merge_equiv_self

end LawfulBEq

end UfManager
