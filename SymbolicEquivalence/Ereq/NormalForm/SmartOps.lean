import SymbolicEquivalence.Ereq.NormalForm.SmartUnion
import Mathlib.Tactic.SplitIfs

/-!
# Smart concatenation and intersection (`mkCat`, `mkInter`)

`mkCat` and `mkInter` simplify with laws that `≅` cannot express:

  `mkCat`    `⊥ ⬝ R → ⊥`,  `R ⬝ ⊥ → ⊥`,  `ε ⬝ R → R`,  `R ⬝ ε → R`
  `mkInter`  `⊥ ⋒ R → ⊥`,  `R ⋒ ⊥ → ⊥`

The simplifications are safe, since they preserve the language, nullability, derivatives
and well-formedness. Well-formedness is proved below, the rest in `Language` and `Derivative`.
-/

open scoped EreqNorm

variable {α : Type*} [Bot α] [DecidableEq α]

namespace EreqNorm

/-- Smart concatenation returns `bot` if either operand is `bot`, drops an `ε` operand, and
    concatenates otherwise. -/
def mkCat (A B : EreqNorm α n) : EreqNorm α n :=
  if A = bot then bot
  else if B = bot then bot
  else if A = ε then B
  else if B = ε then A
  else A ⬝ₙ B

/-- Smart intersection returns `bot` if either operand is `bot` and intersects otherwise. -/
def mkInter (A B : EreqNorm α n) : EreqNorm α n :=
  if A = bot then bot
  else if B = bot then bot
  else A ⋒ₙ B

/-! ### Simplification laws -/

@[simp] theorem mkCat_bot_left (B : EreqNorm α n) : mkCat bot B = bot := by simp [mkCat]

@[simp] theorem mkCat_bot_right (A : EreqNorm α n) : mkCat A bot = bot := by
  by_cases h : A = bot <;> simp [mkCat, h]

@[simp] theorem mkCat_eps_left (B : EreqNorm α n) : mkCat ε B = B := by
  by_cases h : B = bot <;> simp [mkCat, h]

@[simp] theorem mkCat_eps_right (A : EreqNorm α n) : mkCat A ε = A := by
  by_cases h : A = bot <;> by_cases h' : A = ε <;> simp_all [mkCat]

@[simp] theorem mkInter_bot_left (B : EreqNorm α n) : mkInter bot B = bot := by
  simp [mkInter]

@[simp] theorem mkInter_bot_right (A : EreqNorm α n) : mkInter A bot = bot := by
  by_cases h : A = bot <;> simp [mkInter, h]

/-- If neither operand is `bot` or `ε`, `mkCat` is plain concatenation. -/
theorem mkCat_eq_cat {A B : EreqNorm α n} (bl : A ≠ bot) (br : B ≠ bot)
    (el : A ≠ ε) (er : B ≠ ε) : mkCat A B = (A ⬝ₙ B) := by
  simp [mkCat, bl, br, el, er]

theorem mkInter_eq_inter {A B : EreqNorm α n} (bl : A ≠ bot) (br : B ≠ bot) :
    mkInter A B = (A ⋒ₙ B) := by
  simp [mkInter, bl, br]

/-! ### Well-formedness -/

theorem wellFormed_mkCat {A B : EreqNorm α n} (ha : WellFormed A) (hb : WellFormed B) :
    WellFormed (mkCat A B) := by
  unfold mkCat
  split_ifs <;> first | exact .pred _ | assumption | exact .concatenation ha hb

theorem wellFormed_mkInter {A B : EreqNorm α n} (ha : WellFormed A) (hb : WellFormed B) :
    WellFormed (mkInter A B) := by
  unfold mkInter
  split_ifs <;> first | exact .pred _ | exact .intersection ha hb

end EreqNorm
