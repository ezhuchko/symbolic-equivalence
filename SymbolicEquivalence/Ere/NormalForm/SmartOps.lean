import SymbolicEquivalence.Ere.NormalForm.SmartUnion
import Mathlib.Tactic.SplitIfs

/-!
# Smart concatenation and intersection (`mkCat`, `mkInter`)

`mkCat` and `mkInter` simplify with laws that `≅` cannot express:

  `mkCat`    `⊥ ⬝ R → ⊥`,  `R ⬝ ⊥ → ⊥`,  `ε ⬝ R → R`,  `R ⬝ ε → R`
  `mkInter`  `⊥ ⋒ R → ⊥`,  `R ⋒ ⊥ → ⊥`

The simplifications are safe, since they preserve the language, nullability, derivatives
and well-formedness. Well-formedness is proved below, the rest in `Language` and `Derivative`.
-/
open scoped Ere EreNorm

variable {α : Type*} [Bot α] [DecidableEq α]
open EreNorm
namespace EreNorm

/-- Smart concatenation returns `⊥` if either operand is `⊥`, drops an `ε` operand, and
    concatenates otherwise. -/
def mkCat (A B : EreNorm α) : EreNorm α :=
  if A = pred ⊥ then pred ⊥
  else if B = pred ⊥ then pred ⊥
  else if A = ε then B
  else if B = ε then A
  else A ⬝ₙ B

/-- Smart intersection returns `⊥` if either operand is `⊥` and intersects otherwise. -/
def mkInter (A B : EreNorm α) : EreNorm α :=
  if A = pred ⊥ then pred ⊥
  else if B = pred ⊥ then pred ⊥
  else A ⋒ₙ B

/-! ### Simplification laws -/

@[simp] theorem mkCat_bot_left (B : EreNorm α) : mkCat (pred ⊥) B = pred ⊥ := by simp [mkCat]

@[simp] theorem mkCat_bot_right (A : EreNorm α) : mkCat A (pred ⊥) = pred ⊥ := by
  by_cases h : A = pred ⊥ <;> simp [mkCat, h]

@[simp] theorem mkCat_eps_left (B : EreNorm α) : mkCat ε B = B := by
  by_cases h : B = pred ⊥ <;> simp [mkCat, h]

@[simp] theorem mkCat_eps_right (A : EreNorm α) : mkCat A ε = A := by
  by_cases h : A = pred ⊥ <;> by_cases h' : A = ε <;> simp_all [mkCat]

@[simp] theorem mkInter_bot_left (B : EreNorm α) : mkInter (pred ⊥) B = pred ⊥ := by
  simp [mkInter]

@[simp] theorem mkInter_bot_right (A : EreNorm α) : mkInter A (pred ⊥) = pred ⊥ := by
  by_cases h : A = pred ⊥ <;> simp [mkInter, h]

/-- If neither operand is `⊥` or `ε`, `mkCat` is plain concatenation. -/
theorem mkCat_eq_cat {A B : EreNorm α} (bl : A ≠ pred ⊥) (br : B ≠ pred ⊥)
    (el : A ≠ ε) (er : B ≠ ε) : mkCat A B = (A ⬝ₙ B) := by
  simp [mkCat, bl, br, el, er]

theorem mkInter_eq_inter {A B : EreNorm α} (bl : A ≠ pred ⊥) (br : B ≠ pred ⊥) :
    mkInter A B = (A ⋒ₙ B) := by
  simp [mkInter, bl, br]

/-! ### Well-formedness -/

theorem wellFormed_mkCat {A B : EreNorm α} (ha : WellFormed A) (hb : WellFormed B) :
    WellFormed (mkCat A B) := by
  unfold mkCat
  split_ifs <;> first | exact .pred ⊥ | assumption | exact .concatenation ha hb

theorem wellFormed_mkInter {A B : EreNorm α} (ha : WellFormed A) (hb : WellFormed B) :
    WellFormed (mkInter A B) := by
  unfold mkInter
  split_ifs <;> first | exact .pred ⊥ | exact .intersection ha hb

end EreNorm
