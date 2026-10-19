import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Dedup
import SymbolicEquivalence.EffectiveBooleanAlgebra

/-!
# Predicate extensions

To model MSO-style quantification, we extend the alphabet:

* `Elem σ n = σ × {0,1}^n` — symbols paired with a bitvector encoding
  membership of the position in each of `n` variables.

* `Word σ n` — words over the extended alphabet.

* `PExtension α n` — predicates that can refer both to:
  - base predicates `α`, and
  - membership atoms `pᵢ` of variable `i` (testing the `i`-th bit).

* `FundamentalPredicate α n` — the atomic predicates `pᵢ`, `¬pᵢ` and base predicates.

It also decides satisfiability of `PExtension α n`, by trying each value of the bits and
checking the remaining base predicate with the satisfiability check of `α`.
-/

/-- Predicates over `Elem σ n`: base predicates, the bit atoms `pᵢ`, and Boolean connectives. -/
inductive PExtension (α : Type u) (n : Nat) where
  | p    (i : Fin n) : PExtension α n
  | pred (p : α) : PExtension α n
  | top : PExtension α n
  | bot : PExtension α n
  | and : PExtension α n → PExtension α n → PExtension α n
  | or  : PExtension α n → PExtension α n → PExtension α n
  | not : PExtension α n → PExtension α n
  deriving Repr, DecidableEq

/-- `(c, v)` is an element of the extended alphabet where `c : σ` is a symbol together with an
    `n`-bit vector `v`. -/
abbrev Elem σ (n : Nat) := σ × List.Vector Bool n

/-- Words over the extended alphabet are lists of `Elem σ n`'s. -/
abbrev Word σ n := List (Elem σ n)

/-- Semantics of extended predicates on a single element. -/
@[simp]
def PExtension.models [Models α σ] : PExtension α n → Elem σ n → Bool
  | .p i,    ⟨_, u⟩ => u[i]
  | .pred φ, ⟨a, _⟩ => Models.models φ a
  | .top,    _     => true
  | .bot,    _     => false
  | .and φ ψ, c => PExtension.models φ c && PExtension.models ψ c
  | .or φ ψ,  c => PExtension.models φ c || PExtension.models ψ c
  | .not φ,   c => !PExtension.models φ c

/-- `PExtension α n` is an effective Boolean algebra over `Elem σ n`. -/
instance [Models α σ] :
    EffectiveBooleanAlgebra (PExtension α n) (Elem σ n) where
  bot := .bot
  top := .top
  min := .and
  max := .or
  compl := .not
  models p c := PExtension.models p c
  models_bot := rfl
  models_top := rfl
  models_min := rfl
  models_max := rfl
  models_compl := rfl

/-- The atomic predicates over `Elem σ n`, which are a bit atom `pᵢ`, its negation, or a base
    predicate. -/
inductive FundamentalPredicate (α : Type u) (n : Nat) where
  | p    (i : Fin n) : FundamentalPredicate α n
  | notP (i : Fin n) : FundamentalPredicate α n
  | pred (p : α) : FundamentalPredicate α n
  deriving Repr, DecidableEq

/-- Semantics of a fundamental predicate on a single element. -/
@[simp]
def FundamentalPredicate.models [Models α σ] : FundamentalPredicate α n → Elem σ n → Bool
  | .p i,    ⟨_, u⟩ => u[i]
  | .notP i, ⟨_, u⟩ => !u[i]
  | .pred φ, ⟨a, _⟩ => Models.models φ a

/-! ## Satisfiability

A predicate `ψ` is satisfiable when, for some choice of bits `v`, the base predicate
`ψ.assign v` is satisfiable. To decide this we only try the bits that `ψ` uses. -/

section Sat

variable {α σ : Type*}

/-- Resolve the atoms `pᵢ` of `ψ` at `v`, folding the residual
    predicate into the base algebra. -/
def PExtension.assign [Top α] [Bot α] [Min α] [Max α] [Compl α] :
  PExtension α n → List.Vector Bool n → α
  | .p i, v => if v[i] then ⊤ else ⊥
  | .pred q, _ => q
  | .top, _ => ⊤
  | .bot, _ => ⊥
  | .and q r, v => assign q v ⊓ assign r v
  | .or q r, v => assign q v ⊔ assign r v
  | .not q, v => (assign q v)ᶜ

theorem PExtension.models_assign [EffectiveBooleanAlgebra α σ] (ψ : PExtension α n) (a : σ)
    (v : List.Vector Bool n) :
    PExtension.models ψ (a, v) = Models.models (ψ.assign v) a := by
  induction ψ with
  | p i => by_cases hv : v[i] = true <;> simp [PExtension.assign, hv, PExtension.models]
  | pred q => rfl
  | top | bot => simp [PExtension.assign, PExtension.models]
  | and q r ihq ihr | or q r ihq ihr => simp [PExtension.assign, PExtension.models, ihq, ihr]
  | not q ihq => simp [PExtension.assign, PExtension.models, ihq]

/-- The bit positions `ψ` inspects (possibly with repeats). -/
def PExtension.usedBits : PExtension α n → List (Fin n)
  | .p i => [i]
  | .pred _ => []
  | .top => []
  | .bot => []
  | .and q r => q.usedBits ++ r.usedBits
  | .or q r => q.usedBits ++ r.usedBits
  | .not q => q.usedBits

/-- `assign` reads only the used bits. -/
theorem PExtension.assign_congr [EffectiveBooleanAlgebra α σ] (ψ : PExtension α n)
    {v v' : List.Vector Bool n} :
    (∀ i ∈ ψ.usedBits, v[i] = v'[i]) → ψ.assign v = ψ.assign v' := by
  induction ψ with
  | p i => intro h; simp only [PExtension.assign, h i (by simp [PExtension.usedBits])]
  | pred _ | top | bot => intro _; rfl
  | and q r ihq ihr | or q r ihq ihr =>
    intro h
    simp only [PExtension.usedBits, List.mem_append] at h
    simp only [PExtension.assign]
    rw [ihq (fun i hi => h i (Or.inl hi)), ihr (fun i hi => h i (Or.inr hi))]
  | not q ihq =>
    intro h
    simp only [PExtension.usedBits] at h
    simp only [PExtension.assign]
    rw [ihq h]

/-- Bit-vectors realising every truth pattern on `bs` (others `false`); `2 ^ bs.length`
    of them. -/
def PExtension.coverVecs : List (Fin n) → List (List.Vector Bool n)
  | [] => [List.Vector.replicate n false]
  | i :: is => (coverVecs is).flatMap (fun v => [v.set i true, v.set i false])

/-- `coverVecs bs` contains a vector agreeing with `v` on `bs`. -/
theorem PExtension.exists_cover (bs : List (Fin n)) (v : List.Vector Bool n) :
    ∃ v' ∈ coverVecs bs, ∀ i ∈ bs, v'[i] = v[i] := by
  induction bs with
  | nil => exact ⟨List.Vector.replicate n false, by simp [coverVecs], by simp⟩
  | cons i is ih =>
    obtain ⟨v', hmem, hv'⟩ := ih
    refine ⟨v'.set i v[i], ?_, ?_⟩
    · simp only [coverVecs, List.mem_flatMap]
      refine ⟨v', hmem, ?_⟩
      cases hb : v[i] <;> simp
    · intro j hj
      by_cases hji : j = i
      · subst hji; exact List.Vector.get_set_same _ _ _
      · have hset : (v'.set i v[i])[j] = v'[j] := List.Vector.get_set_of_ne (Ne.symm hji) v[i]
        rw [hset]
        exact hv' j (List.mem_of_ne_of_mem hji hj)

/-! ### Satisfiability over the extended alphabet -/

/-- `ψ` is satisfiable iff some candidate bit-vector leaves a satisfiable residual. -/
theorem PExtension.satisfiable_iff [EffectiveBooleanAlgebra α σ] (ψ : PExtension α n) :
    (∃ v ∈ coverVecs ψ.usedBits.dedup, Models.Satisfiable (σ := σ) (ψ.assign v))
      ↔ Models.Satisfiable (σ := Elem σ n) ψ := by
  constructor
  · rintro ⟨v, -, d, hd⟩
    refine ⟨(d, v), ?_⟩
    change PExtension.models ψ (d, v) = true
    rw [PExtension.models_assign]; exact hd
  · rintro ⟨⟨a, v⟩, hav⟩
    have hav : PExtension.models ψ (a, v) = true := hav
    obtain ⟨v', hmem, hcov⟩ := exists_cover ψ.usedBits.dedup v
    refine ⟨v', hmem, a, ?_⟩
    rw [← PExtension.assign_congr ψ (fun i hi => (hcov i (List.mem_dedup.mpr hi)).symm),
      ← PExtension.models_assign]
    exact hav

/-- The satisfiability oracle on extended predicates. -/
instance [EffectiveBooleanAlgebra α σ] [DecidableSat α] : DecidableSat (PExtension α n) :=
  fun ψ => decidable_of_iff _ (PExtension.satisfiable_iff (σ := σ) ψ)

end Sat
