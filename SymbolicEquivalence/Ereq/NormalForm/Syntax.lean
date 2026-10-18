import SymbolicEquivalence.Ereq.Syntax
import SymbolicEquivalence.SmartDedup

/-!
# Normal forms for `EreqAtomic` modulo similarity

`EreqNorm α n` replaces the binary `⋓ₐ` of `EreqAtomic` by an n-ary `union` node with at least
two operands, as `EreNorm` does for `Ere`. `WellFormed` adds the two invariants the union laws
need: no duplicate operands and no nested unions.

The tail of a union is an `EreqNormList` rather than a `List (EreqNorm α n)`, since Lean does
not accept the `List` version here. `first` and `rest` give the operands as a `List`, and the
lemmas are stated about that.
-/

universe u

variable {α : Type u}

mutual
/-- Normal forms of `EreqAtomic`, in which a union is a single node with at least two
    operands. -/
inductive EreqNorm (α : Type u) : Nat → Type u where
  | ε             : EreqNorm α n
  | pred (e : FundamentalPredicate α n) : EreqNorm α n
  | union         : EreqNorm α n → EreqNorm α n → EreqNormList α n → EreqNorm α n
  | intersection  : EreqNorm α n → EreqNorm α n → EreqNorm α n
  | concatenation : EreqNorm α n → EreqNorm α n → EreqNorm α n
  | star          : EreqNorm α n → EreqNorm α n
  | negation      : EreqNorm α n → EreqNorm α n
  | existential   : EreqNorm α (n + 1) → EreqNorm α n

/-- The operands of a union after the first two. -/
inductive EreqNormList (α : Type u) : Nat → Type u where
  | nil : EreqNormList α n
  | cons : EreqNorm α n → EreqNormList α n → EreqNormList α n
end

open EreqNorm EreqNormList

namespace EreqNorm

scoped infixr:40 " ⋒ₙ " => EreqNorm.intersection
scoped infixr:50 " ⬝ₙ " => EreqNorm.concatenation
scoped prefix:max "~ₙ"  => EreqNorm.negation
scoped postfix:max "★ₙ" => EreqNorm.star
scoped prefix:max "∃ₙ " => EreqNorm.existential

/-- `⋃ₙ[x, y | zs]` is `union x y zs`, and `⋃ₙ[x, y]` the same with an empty tail. -/
scoped syntax:max "⋃ₙ[" term ", " term " | " term "]" : term
scoped syntax:max "⋃ₙ[" term ", " term "]" : term

end EreqNorm

open scoped EreqNorm

macro_rules
  | `(⋃ₙ[$x, $y | $zs]) => `(EreqNorm.union $x $y $zs)
  | `(⋃ₙ[$x, $y])       => `(EreqNorm.union $x $y .nil)

@[app_unexpander EreqNorm.union]
def EreqNorm.unexpandUnion : Lean.PrettyPrinter.Unexpander
  | `($_ $x $y EreqNormList.nil) => `(⋃ₙ[$x, $y])
  | `($_ $x $y $zs)              => `(⋃ₙ[$x, $y | $zs])
  | _                            => throw ()

/-! ### `EreqNormList` is a list -/

def EreqNormList.toList : EreqNormList α n → List (EreqNorm α n)
  | .nil => []
  | .cons x xs => x :: xs.toList

def List.toEreqNormList : List (EreqNorm α n) → EreqNormList α n
  | [] => .nil
  | x :: xs => .cons x xs.toEreqNormList

@[simp] theorem EreqNormList.toList_nil : (EreqNormList.nil : EreqNormList α n).toList = [] :=
  rfl
@[simp] theorem EreqNormList.toList_cons (x : EreqNorm α n) (xs : EreqNormList α n) :
    (EreqNormList.cons x xs).toList = x :: xs.toList := rfl

@[simp]
theorem EreqNormList.toList_toEreqNormList (xs : List (EreqNorm α n)) :
    xs.toEreqNormList.toList = xs := by
  match xs with
  | [] => rfl
  | x :: xs => simp [List.toEreqNormList, toList_toEreqNormList]

@[simp]
theorem EreqNormList.toEreqNormList_toList (xs : EreqNormList α n) :
    xs.toList.toEreqNormList = xs := by
  match xs with
  | .nil => rfl
  | .cons x xs => simp [List.toEreqNormList, toEreqNormList_toList]

/-! ### Operands -/

/-- `true` iff the head constructor is `union`. -/
@[simp] def EreqNorm.isUnion : EreqNorm α n → Bool
  | .union .. => true
  | _ => false

/-- The first operand of a union, or the node itself for any other node. -/
@[simp] def EreqNorm.first : EreqNorm α n → EreqNorm α n
  | ⋃ₙ[x, _ | _] => x
  | r => r

/-- The remaining operands of a union, or `[]` for any other node. -/
@[simp] def EreqNorm.rest : EreqNorm α n → List (EreqNorm α n)
  | ⋃ₙ[_, y | zs] => y :: zs.toList
  | _ => []

namespace EreqNorm

/-- The operands of a node, as a non-empty list. -/
def toList (r : EreqNorm α n) : List (EreqNorm α n) := r.first :: r.rest

theorem toList_eq (r : EreqNorm α n) : toList r = r.first :: r.rest := rfl

@[simp] theorem toList_union (x y : EreqNorm α n) (zs : EreqNormList α n) :
    toList ⋃ₙ[x, y | zs] = x :: y :: zs.toList := rfl

/-- A non-union is its own singleton operand list. -/
theorem toList_eq_self {r : EreqNorm α n} (h : isUnion r = false) : toList r = [r] := by
  cases r <;> simp_all [toList]

/-- Rebuild a node from its first operand and the rest. -/
def fromList : EreqNorm α n → List (EreqNorm α n) → EreqNorm α n
  | x, [] => x
  | x, y :: zs => ⋃ₙ[x, y | zs.toEreqNormList]

@[simp] theorem fromList_nil (x : EreqNorm α n) : fromList x [] = x := rfl
@[simp] theorem fromList_cons (x y : EreqNorm α n) (zs : List (EreqNorm α n)) :
    fromList x (y :: zs) = ⋃ₙ[x, y | zs.toEreqNormList] := rfl

/-- `fromList` undoes `toList`. -/
theorem fromList_toList (r : EreqNorm α n) : fromList r.first r.rest = r := by
  cases r <;> simp [fromList]

/-- `toList` undoes `fromList` when the first operand is not a union. -/
theorem toList_fromList {x : EreqNorm α n} {xs : List (EreqNorm α n)}
    (h : isUnion x = false) : toList (fromList x xs) = x :: xs := by
  cases xs with
  | nil => simpa using toList_eq_self h
  | cons y ys => simp [toList]

@[simp] theorem toList_ne_nil (r : EreqNorm α n) : toList r ≠ [] := by simp [toList]

/-- `toList` is injective. -/
theorem eq_of_toList_eq {r s : EreqNorm α n} (h : toList r = toList s) : r = s := by
  unfold toList at h
  injection h with h1 h2
  rw [← fromList_toList r, ← fromList_toList s, h1, h2]

/-- The expression that matches no word. -/
abbrev bot {α : Type u} [Bot α] {n : Nat} : EreqNorm α n := .pred (.pred ⊥)

/-! ### Well-formed normal forms -/

/-- A normal form has no duplicate operands and no union directly inside a union, which are
    exactly the hypotheses of the union laws in `SmartUnion`. -/
inductive WellFormed : EreqNorm α n → Prop where
  | ε : WellFormed ε
  | pred (e : FundamentalPredicate α n) : WellFormed (pred e)
  | union {x y : EreqNorm α n} {zs : EreqNormList α n}
    (h : ∀ w ∈ x :: y :: zs.toList, WellFormed w)
    (nd : (x :: y :: zs.toList).Nodup)
    (f : ∀ w ∈ x :: y :: zs.toList, isUnion w = false) :
    WellFormed ⋃ₙ[x, y | zs]
  | intersection {l r : EreqNorm α n} (hl : WellFormed l) (hr : WellFormed r) :
    WellFormed (l ⋒ₙ r)
  | concatenation {l r : EreqNorm α n} (hl : WellFormed l) (hr : WellFormed r) :
    WellFormed (l ⬝ₙ r)
  | star {r : EreqNorm α n} (h : WellFormed r) : WellFormed r★ₙ
  | negation {r : EreqNorm α n} (h : WellFormed r) : WellFormed ~ₙr
  | existential {r : EreqNorm α (n + 1)} (h : WellFormed r) : WellFormed (∃ₙ r)

/-! ### `WellFormed`, read off `toList` -/

theorem toList_wf {r : EreqNorm α n} (h : WellFormed r) : ∀ x ∈ toList r, WellFormed x := by
  cases r with
  | union => cases h with | union h _ _ => simpa using h
  | _ => simpa [toList] using h

theorem toList_nodup {r : EreqNorm α n} (h : WellFormed r) : (toList r).Nodup := by
  cases h with
  | union _ nd _ => simpa using nd
  | _ => simp [toList]

theorem toList_not_isUnion {r : EreqNorm α n} (h : WellFormed r) :
    ∀ x ∈ toList r, isUnion x = false := by
  cases h with
  | union _ _ f => simpa using f
  | _ => simp [toList]

theorem toList_append_eq (A B : EreqNorm α n) :
    toList A ++ toList B = A.first :: (A.rest ++ toList B) := rfl

/-- An element of two appended operand lists is well-formed and not a union. -/
theorem mem_toList_append {a b x : EreqNorm α n}
    (ha : WellFormed a) (hb : WellFormed b) (hx : x ∈ toList a ++ toList b) :
    WellFormed x ∧ isUnion x = false := by
  rcases List.mem_append.mp hx with h | h
  · exact ⟨toList_wf ha x h, toList_not_isUnion ha x h⟩
  · exact ⟨toList_wf hb x h, toList_not_isUnion hb x h⟩

/-- If `x :: xs` has no duplicates and consists of well-formed non-unions, then
    `fromList x xs` is well-formed. -/
theorem fromList_wf {x : EreqNorm α n} {xs : List (EreqNorm α n)}
    (hwf : ∀ w ∈ x :: xs, WellFormed w) (hnd : (x :: xs).Nodup)
    (hflat : ∀ w ∈ x :: xs, isUnion w = false) : WellFormed (fromList x xs) := by
  cases xs with
  | nil => simpa using hwf x (by simp)
  | cons y zs =>
    refine WellFormed.union ?_ ?_ ?_ <;> rw [EreqNormList.toList_toEreqNormList]
    · exact hwf
    · exact hnd
    · exact hflat

end EreqNorm

/-! ### Boolean and decidable equality, and hashing -/

def FundamentalPredicate.beq [BEq α] :
    FundamentalPredicate α n → FundamentalPredicate α n → Bool
  | .p i, .p j => i == j
  | .notP i, .notP j => i == j
  | .pred x, .pred y => x == y
  | _, _ => false

instance [BEq α] : BEq (FundamentalPredicate α n) := ⟨FundamentalPredicate.beq⟩

instance [BEq α] [LawfulBEq α] : LawfulBEq (FundamentalPredicate α n) where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, FundamentalPredicate.beq]
  rfl {a} := by cases a <;> simp [BEq.beq, FundamentalPredicate.beq]

mutual
  /-- Structural Boolean equality. -/
  def EreqNorm.beq [BEq α] : EreqNorm α n → EreqNorm α n → Bool
    | .ε, .ε => true
    | .pred p, .pred q => p == q
    | ⋃ₙ[x, y | zs], ⋃ₙ[x', y' | zs'] =>
        EreqNorm.beq x x' && EreqNorm.beq y y' && EreqNormList.beqList zs zs'
    | l₁ ⋒ₙ r₁, l₂ ⋒ₙ r₂ => EreqNorm.beq l₁ l₂ && EreqNorm.beq r₁ r₂
    | l₁ ⬝ₙ r₁, l₂ ⬝ₙ r₂ => EreqNorm.beq l₁ l₂ && EreqNorm.beq r₁ r₂
    | r₁★ₙ, r₂★ₙ => EreqNorm.beq r₁ r₂
    | ~ₙ r₁, ~ₙ r₂ => EreqNorm.beq r₁ r₂
    | ∃ₙ r₁, ∃ₙ r₂ => EreqNorm.beq r₁ r₂
    | _, _ => false

  def EreqNormList.beqList [BEq α] : EreqNormList α n → EreqNormList α n → Bool
    | .nil, .nil => true
    | .cons x xs, .cons y ys => EreqNorm.beq x y && EreqNormList.beqList xs ys
    | _, _ => false
end

instance [BEq α] : BEq (EreqNorm α n) := ⟨EreqNorm.beq⟩

mutual
  theorem EreqNorm.lawful_rfl [BEq α] [LawfulBEq α] : ∀ (a : EreqNorm α n), EreqNorm.beq a a = true
    | .ε => rfl
    | .pred p => by simp [EreqNorm.beq]
    | ⋃ₙ[x, y | zs] => by
      simp [EreqNorm.beq, lawful_rfl x, lawful_rfl y, lawful_rfl_list zs]
    | l ⋒ₙ r | l ⬝ₙ r => by simp [EreqNorm.beq, lawful_rfl l, lawful_rfl r]
    | r★ₙ | ~ₙ r | ∃ₙ r => by simp [EreqNorm.beq, lawful_rfl r]

  theorem EreqNorm.lawful_rfl_list [BEq α] [LawfulBEq α] :
      ∀ (xs : EreqNormList α n), EreqNormList.beqList xs xs = true
    | .nil => rfl
    | .cons x xs => by simp [EreqNormList.beqList, lawful_rfl x, lawful_rfl_list xs]
end

mutual
  /-- If two normal forms are equal under `beq`, they are equal. -/
  theorem EreqNorm.lawful_eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ {a b : EreqNorm α n}, EreqNorm.beq a b = true → a = b
    | .ε, b, h | .pred _, b, h => by cases b <;> simp_all [EreqNorm.beq]
    | ⋃ₙ[x, y | zs], b, h => by
      cases b <;> simp only [EreqNorm.beq, Bool.and_eq_true, reduceCtorEq] at h
      rw [lawful_eq_of_beq h.1.1, lawful_eq_of_beq h.1.2, lawful_eq_of_beq_list h.2]
    | _ ⋒ₙ _, b, h | _ ⬝ₙ _, b, h => by
      cases b <;> simp only [EreqNorm.beq, Bool.and_eq_true, reduceCtorEq] at h
      rw [lawful_eq_of_beq h.1, lawful_eq_of_beq h.2]
    | _★ₙ, b, h | ~ₙ _, b, h => by
      cases b <;> simp only [EreqNorm.beq, reduceCtorEq] at h
      rw [lawful_eq_of_beq h]
    | ∃ₙ _, b, h => by
      cases b <;> simp only [EreqNorm.beq, reduceCtorEq] at h
      rw [lawful_eq_of_beq h]

  theorem EreqNorm.lawful_eq_of_beq_list [BEq α] [LawfulBEq α] :
      ∀ {xs ys : EreqNormList α n}, EreqNormList.beqList xs ys = true → xs = ys
    | .nil, ys, h => by cases ys <;> simp_all [EreqNormList.beqList]
    | .cons x xs, ys, h => by
      cases ys <;> simp only [EreqNormList.beqList, Bool.and_eq_true, reduceCtorEq] at h
      rw [lawful_eq_of_beq h.1, lawful_eq_of_beq_list h.2]
end

instance [BEq α] [LawfulBEq α] : LawfulBEq (EreqNorm α n) where
  eq_of_beq := EreqNorm.lawful_eq_of_beq
  rfl       := EreqNorm.lawful_rfl _

/-- Decidable equality, from the lawful `BEq` above. -/
instance [BEq α] [LawfulBEq α] : DecidableEq (EreqNorm α n) := instDecidableEqOfLawfulBEq

deriving instance Hashable for FundamentalPredicate, EreqNorm
deriving instance Repr for EreqNorm
