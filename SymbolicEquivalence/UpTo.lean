/-!
# Lists up to a relation

`MemUpTo`, `SubsetUpTo` and `EqualityUpTo` are membership, inclusion and equality of
lists, taken up to a relation `R`.
-/

variable {α : Type _} {R : α → α → Prop}

/-- `x` is in `ys` up to `R` if `R x y` holds for some `y` in `ys`. -/
def MemUpTo (R : α → α → Prop) : α → List α → Prop :=
  fun x ys => ∃ y ∈ ys, R x y

namespace UpTo
scoped notation x " ∈[ " R " ] " ys => MemUpTo R x ys
end UpTo

open scoped UpTo

/-- Every element of `xs` is in `ys` up to `R`. -/
def SubsetUpTo (R : α → α → Prop) : List α → List α → Prop :=
  fun xs ys => ∀ x ∈ xs, x ∈[ R ] ys

namespace UpTo
scoped notation xs " ⊆[ " R " ] " ys => SubsetUpTo R xs ys
end UpTo

/-- Each of `xs` and `ys` is a subset of the other up to `R`. -/
def EqualityUpTo (R : α → α → Prop) : List α → List α → Prop :=
  fun xs ys => (xs ⊆[ R ] ys) ∧ (ys ⊆[ R ] xs)

namespace UpTo
scoped notation xs " =[ " R " ] " ys => EqualityUpTo R xs ys
end UpTo

theorem subsetUpTo_refl {xs : List α} (hr : Std.Refl R) :
    xs ⊆[ R ] xs := fun x hx => ⟨x, hx, Std.Refl.refl x⟩

theorem subsetUpTo_trans {xs ys zs : List α} (ht : Trans R R R)
    (h1 : xs ⊆[ R ] ys) (h2 : ys ⊆[ R ] zs) :
    xs ⊆[ R ] zs :=
  fun x hx =>
  have ⟨y, hy, hxy⟩ := h1 x hx
  have ⟨z, hz, hyz⟩ := h2 y hy
  ⟨z, hz, ht.trans hxy hyz⟩

theorem subset_to_subsetUpTo {xs ys : List α} (hr : Std.Refl R) (h : xs ⊆ ys) :
    xs ⊆[ R ] ys := fun x hx => ⟨x, h hx, Std.Refl.refl x⟩

theorem equalityUpTo_refl {xs : List α} (hr : Std.Refl R) :
    xs =[ R ] xs := ⟨subsetUpTo_refl hr, subsetUpTo_refl hr⟩

theorem equalityUpTo_symm {xs ys : List α} (h : xs =[ R ] ys) :
    ys =[ R ] xs := ⟨h.2, h.1⟩

theorem equalityUpTo_trans {xs ys zs : List α} (ht : Trans R R R)
    (h1 : xs =[ R ] ys) (h2 : ys =[ R ] zs) :
    xs =[ R ] zs :=
  ⟨subsetUpTo_trans ht h1.1 h2.1, subsetUpTo_trans ht h2.2 h1.2⟩
