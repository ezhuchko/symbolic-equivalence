import Mathlib.Order.Notation
import SymbolicEquivalence.Ere.Syntax
import SymbolicEquivalence.SmartDedup

/-!
# Normal forms for `Ere` modulo similarity

`EreNorm` replaces the binary `⋓` of `Ere` by an n-ary `union` node with at least two
operands, so that the union laws of `≅` (associativity, deduplication, idempotence) become
properties of a list. `WellFormed` adds the two invariants those laws need: no duplicate
operands and no nested unions.
-/
open scoped Ere

variable {α : Type*}

/-- Normal forms of `Ere`, in which a union is a single node with at least two
    operands. -/
inductive EreNorm (α : Type u) where
  | ε                  : EreNorm α
  | pred (e : α)       : EreNorm α
  | union              : EreNorm α → EreNorm α → List (EreNorm α) → EreNorm α
  | intersection       : EreNorm α → EreNorm α → EreNorm α
  | concatenation      : EreNorm α → EreNorm α → EreNorm α
  | star               : EreNorm α → EreNorm α
  | negation           : EreNorm α → EreNorm α
  | xor                : EreNorm α → EreNorm α → EreNorm α
  deriving Repr, Hashable

open EreNorm

namespace EreNorm

scoped infixr:40 " ⋒ₙ " => EreNorm.intersection
scoped infixr:50 " ⬝ₙ " => EreNorm.concatenation
scoped prefix:max "~ₙ"  => EreNorm.negation
scoped postfix:max "★ₙ" => EreNorm.star

/-- `⋃ₙ[x, y | zs]` is `union x y zs`, and `⋃ₙ[x, y, z, …]` the same with a literal
    tail. -/
scoped syntax:max "⋃ₙ[" term ", " term " | " term "]" : term
scoped syntax:max "⋃ₙ[" term ", " term,* "]" : term

end EreNorm

open scoped EreNorm

macro_rules
  | `(⋃ₙ[$x, $y | $zs])  => `(EreNorm.union $x $y $zs)
  | `(⋃ₙ[$x, $y])        => `(EreNorm.union $x $y [])
  | `(⋃ₙ[$x, $y, $zs,*]) => `(EreNorm.union $x $y [$zs,*])

@[app_unexpander EreNorm.union]
def EreNorm.unexpandUnion : Lean.PrettyPrinter.Unexpander
  | `($_ $x $y [])      => `(⋃ₙ[$x, $y])
  | `($_ $x $y [$zs,*]) => `(⋃ₙ[$x, $y, $zs,*])
  | `($_ $x $y $zs)     => `(⋃ₙ[$x, $y | $zs])
  | _                   => throw ()

/-! ### Operands -/

/-- `true` iff the head constructor is `union`. -/
@[simp] def EreNorm.isUnion : EreNorm α → Bool
  | .union .. => true
  | _ => false

/-- The first operand of a union, or the node itself for any other node. -/
@[simp] def EreNorm.first : EreNorm α → EreNorm α
  | ⋃ₙ[x, _ | _] => x
  | r => r

/-- The remaining operands of a union, or `[]` for any other node. -/
@[simp] def EreNorm.rest : EreNorm α → List (EreNorm α)
  | ⋃ₙ[_, y | zs] => y :: zs
  | _ => []

namespace EreNorm

/-- The operands of a node, as a non-empty list. -/
def toList (r : EreNorm α) : List (EreNorm α) := r.first :: r.rest

@[simp] theorem toList_union (x y : EreNorm α) (zs : List (EreNorm α)) :
    toList ⋃ₙ[x, y | zs] = x :: y :: zs := rfl

/-- A non-union is its own singleton operand list. -/
theorem toList_eq_self {r : EreNorm α} (h : isUnion r = false) : toList r = [r] := by
  cases r <;> simp_all [toList]

/-- Rebuild a node from its first operand and the rest. -/
def fromList : EreNorm α → List (EreNorm α) → EreNorm α
  | x, [] => x
  | x, y :: zs => ⋃ₙ[x, y | zs]

@[simp] theorem fromList_nil (x : EreNorm α) : fromList x [] = x := rfl
@[simp] theorem fromList_cons (x y : EreNorm α) (zs) :
    fromList x (y :: zs) = ⋃ₙ[x, y | zs] := rfl

/-- `fromList` undoes `toList`. -/
theorem fromList_toList (r : EreNorm α) : fromList r.first r.rest = r := by
  cases r <;> rfl

/-- `toList` undoes `fromList` when the first operand is not a union. -/
theorem toList_fromList {x : EreNorm α} {xs : List (EreNorm α)} (h : isUnion x = false) :
    toList (fromList x xs) = x :: xs := by
  cases xs with
  | nil => simpa using toList_eq_self h
  | cons => rfl

@[simp] theorem toList_ne_nil (r : EreNorm α) : toList r ≠ [] := by simp [toList]

/-- `toList` is injective. -/
theorem eq_of_toList_eq {r s : EreNorm α} (h : toList r = toList s) : r = s := by
  unfold toList at h
  injection h with h1 h2
  rw [← fromList_toList r, ← fromList_toList s, h1, h2]

/-! ### Well-formed normal forms -/

/-- A normal form has no duplicate operands and no union directly inside a union,
    which are exactly the hypotheses of the union laws in `SmartUnion`. -/
inductive WellFormed : EreNorm α → Prop where
  | ε : WellFormed ε
  | pred (e : α) : WellFormed (pred e)
  | union {x y : EreNorm α} {zs : List (EreNorm α)}
    (h : ∀ w ∈ x :: y :: zs, WellFormed w)
    (n : (x :: y :: zs).Nodup)
    (f : ∀ w ∈ x :: y :: zs, isUnion w = false) : WellFormed ⋃ₙ[x, y | zs]
  | intersection {l r : EreNorm α} (hl : WellFormed l) (hr : WellFormed r) :
    WellFormed (l ⋒ₙ r)
  | concatenation {l r : EreNorm α} (hl : WellFormed l) (hr : WellFormed r) :
    WellFormed (l ⬝ₙ r)
  | star {r : EreNorm α} (h : WellFormed r) : WellFormed (r★ₙ)
  | negation {r : EreNorm α} (h : WellFormed r) : WellFormed (~ₙ r)
  | xor {l r : EreNorm α} (hl : WellFormed l) (hr : WellFormed r) : WellFormed (.xor l r)

/-! ### `WellFormed`, read off `toList` -/

theorem toList_wf {r : EreNorm α} (h : WellFormed r) : ∀ x ∈ toList r, WellFormed x := by
  cases r with
  | union => cases h with | union h _ _ => simpa using h
  | _ => simpa [toList] using h

theorem toList_nodup {r : EreNorm α} (h : WellFormed r) : (toList r).Nodup := by
  cases h with
  | union _ n _ => simpa using n
  | _ => simp [toList]

theorem toList_not_isUnion {r : EreNorm α} (h : WellFormed r) :
    ∀ x ∈ toList r, isUnion x = false := by
  cases h with
  | union _ _ f => simpa using f
  | _ => simp [toList]

theorem toList_append_eq (A B : EreNorm α) :
    toList A ++ toList B = A.first :: (A.rest ++ toList B) := rfl

/-- An element of two appended operand lists is well-formed and not a union. -/
theorem mem_toList_append {a b x : EreNorm α}
    (ha : WellFormed a) (hb : WellFormed b) (hx : x ∈ toList a ++ toList b) :
    WellFormed x ∧ isUnion x = false := by
  rcases List.mem_append.mp hx with h | h
  · exact ⟨toList_wf ha x h, toList_not_isUnion ha x h⟩
  · exact ⟨toList_wf hb x h, toList_not_isUnion hb x h⟩

/-- If `x :: xs` has no duplicates and consists of well-formed non-unions, then
    `fromList x xs` is well-formed. -/
theorem fromList_wf {x : EreNorm α} {xs : List (EreNorm α)}
    (hwf : ∀ w ∈ x :: xs, WellFormed w) (hnd : (x :: xs).Nodup)
    (hflat : ∀ w ∈ x :: xs, isUnion w = false) : WellFormed (fromList x xs) :=
  match xs with
  | [] => hwf x (List.mem_singleton.mpr rfl)
  | _ :: _ => .union hwf hnd hflat

end EreNorm

/-! ### Boolean and decidable equality -/

mutual
  /-- Structural Boolean equality. -/
  def EreNorm.beq [BEq α] : EreNorm α → EreNorm α → Bool
    | .ε, .ε => true
    | .pred p, .pred q => p == q
    | ⋃ₙ[x, y | zs], ⋃ₙ[x', y' | zs'] =>
        EreNorm.beq x x' && EreNorm.beq y y' && EreNorm.beqList zs zs'
    | a ⋒ₙ b, c ⋒ₙ d => EreNorm.beq a c && EreNorm.beq b d
    | a ⬝ₙ b, c ⬝ₙ d => EreNorm.beq a c && EreNorm.beq b d
    | a★ₙ, b★ₙ => EreNorm.beq a b
    | ~ₙ a, ~ₙ b => EreNorm.beq a b
    | .xor a b, .xor c d => EreNorm.beq a c && EreNorm.beq b d
    | _, _ => false

  def EreNorm.beqList [BEq α] : List (EreNorm α) → List (EreNorm α) → Bool
    | [], [] => true
    | x :: xs, y :: ys => EreNorm.beq x y && EreNorm.beqList xs ys
    | _, _ => false
end

instance [BEq α] : BEq (EreNorm α) := ⟨EreNorm.beq⟩

mutual
  theorem EreNorm.lawful_rfl [BEq α] [LawfulBEq α] : ∀ (a : EreNorm α), EreNorm.beq a a = true
    | .ε => rfl
    | .pred p => by simp [EreNorm.beq]
    | ⋃ₙ[x, y | zs] => by
      simp [EreNorm.beq, lawful_rfl x, lawful_rfl y, lawful_rfl_list zs]
    | l ⋒ₙ r | l ⬝ₙ r | .xor l r => by simp [EreNorm.beq, lawful_rfl l, lawful_rfl r]
    | r★ₙ | ~ₙ r => by simp [EreNorm.beq, lawful_rfl r]

  theorem EreNorm.lawful_rfl_list [BEq α] [LawfulBEq α] :
      ∀ (xs : List (EreNorm α)), EreNorm.beqList xs xs = true
    | [] => rfl
    | x :: xs => by simp [EreNorm.beqList, lawful_rfl x, lawful_rfl_list xs]
end

mutual
  /-- If two normal forms are equal under `beq`, they are equal. -/
  theorem EreNorm.lawful_eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ {a b : EreNorm α}, EreNorm.beq a b = true → a = b
    | .ε, b, h | .pred _, b, h => by cases b <;> simp_all [EreNorm.beq]
    | ⋃ₙ[x, y | zs], b, h => by
      cases b <;> simp only [EreNorm.beq, Bool.and_eq_true, reduceCtorEq] at h
      rw [lawful_eq_of_beq h.1.1, lawful_eq_of_beq h.1.2, lawful_eq_of_beq_list h.2]
    | _ ⋒ₙ _, b, h | _ ⬝ₙ _, b, h | .xor _ _, b, h => by
      cases b <;> simp only [EreNorm.beq, Bool.and_eq_true, reduceCtorEq] at h
      rw [lawful_eq_of_beq h.1, lawful_eq_of_beq h.2]
    | _★ₙ, b, h | ~ₙ _, b, h => by
      cases b <;> simp only [EreNorm.beq, reduceCtorEq] at h
      rw [lawful_eq_of_beq h]

  theorem EreNorm.lawful_eq_of_beq_list [BEq α] [LawfulBEq α] :
      ∀ {xs ys : List (EreNorm α)}, EreNorm.beqList xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp_all [EreNorm.beqList]
    | x :: xs, ys, h => by
      cases ys <;> simp only [EreNorm.beqList, Bool.and_eq_true, reduceCtorEq] at h
      rw [lawful_eq_of_beq h.1, lawful_eq_of_beq_list h.2]
end

instance [BEq α] [LawfulBEq α] : LawfulBEq (EreNorm α) where
  eq_of_beq := EreNorm.lawful_eq_of_beq
  rfl       := EreNorm.lawful_rfl _

/-- Decidable equality, from the lawful `BEq` above. -/
instance [BEq α] [LawfulBEq α] : DecidableEq (EreNorm α) := instDecidableEqOfLawfulBEq
