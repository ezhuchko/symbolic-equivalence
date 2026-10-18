import SymbolicEquivalence.Ereq.ExtendedEBA
import SymbolicEquivalence.OrderedTTerm
import SymbolicEquivalence.VectorHelpers
import Mathlib.Data.Fin.SuccPred

/-!
# Stratified transition terms

A `BitTree α n L` is a decision tree that first branches on bits `Fin n`, then on
predicates `α`, with values of `L` at the leaves. `DerTree` and `DerTreeNorm` both use it.

This file defines the lifted operators and existential projection on bit trees, and
proves that they preserve ordering and commute with evaluation.
-/

universe u v w
variable {α : Type u} {β γ : Type w}
open TTerm

/-! ## Stratified terms

`TTerm κ (TTerm α β)`: the outer level tests `κ` against `x.2`, the inner level `α`
against `x.1`. -/

namespace TTerm
variable {κ σ₁ σ₂ : Type*}

/-- All leaves of a two-level term, i.e. the leaves of each inner term. -/
def leaves₂ (f : TTerm κ (TTerm α β)) : List β := (leaves f).flatMap leaves

@[simp] theorem leaves₂_leaf (t : TTerm α β) :
    leaves₂ (leaf t : TTerm κ (TTerm α β)) = leaves t := by simp [leaves₂]

@[simp] theorem leaves₂_node (cond : κ) (l r : TTerm κ (TTerm α β)) :
    leaves₂ (node cond l r) = leaves₂ l ++ leaves₂ r := by simp [leaves₂]

section Eval
variable [Models κ σ₂] [Models α σ₁]

/-- Evaluate a stratified term: outer level at `x.2`, inner level at `x.1`. -/
def evaluation₂ (x : σ₁ × σ₂) (f : TTerm κ (TTerm α β)) : β := (f[x.2])[x.1]

@[simp] theorem eval₂_leaf (x : σ₁ × σ₂) (t : TTerm α β) :
    evaluation₂ x (leaf t : TTerm κ (TTerm α β)) = t[x.1] := rfl

@[simp] theorem eval₂_node (x : σ₁ × σ₂) (cond : κ) (l r : TTerm κ (TTerm α β)) :
    evaluation₂ x (node cond l r)
      = if models cond x.2 then evaluation₂ x l else evaluation₂ x r := by
  simp only [evaluation₂, eval_node]; split_ifs <;> rfl

end Eval

end TTerm

/-! ## Bit trees -/

variable {σ : Type v} {L L' : Type w} [EffectiveBooleanAlgebra α σ]

/-- Bit-lookup makes `Fin n` a predicate over `List.Vector Bool n`. -/
instance : Models (Fin n) (List.Vector Bool n) := ⟨fun i v => v[i]⟩

@[simp] theorem BitTree.models_fin (i : Fin n) (v : List.Vector Bool n) : models i v = v[i] := rfl

/-- Outer level on `Fin n`, inner level on `α`, values of `L` at the leaves. -/
abbrev BitTree (α : Type u) (n : Nat) (L : Type w) := TTerm (Fin n) (TTerm α L)

/-- Evaluate the bit level at `x.2`, then the predicate level at `x.1`. -/
notation f "[" x "]ₙ" => TTerm.evaluation₂ x f

namespace BitTree

/-! ### Lifted operators -/

def liftUnaryNorm (op : L → L') (f : BitTree α n L) : BitTree α n L' :=
  liftUnary (liftUnary op) f

section
variable [DecidableSat α]

def liftBinaryNorm (op : L → L → L') (l r : BitTree α n L) : BitTree α n L' :=
  apply (liftBinaryR op) l r

/-! ### Existential projection

`liftUProj cup op f` applies `op` to every leaf and removes bit `n` by joining the two
branches of each node that tests it with `cup`. -/

def liftUProj (cup : L' → L' → L') (op : L → L') :
    BitTree α (n + 1) L → BitTree α n L'
  | leaf t => leaf (liftUnary op t)
  | .node cond f₁ f₀ =>
    if hk : cond.val = n then
      liftBinaryNorm cup (liftUProj cup op f₁) (liftUProj cup op f₀)
    else
      .node (cond.castPredVal hk) (liftUProj cup op f₁) (liftUProj cup op f₀)

@[simp] theorem liftUProj_leaf (cup : L' → L' → L') (op : L → L') (t : TTerm α L) :
    liftUProj (n := n) cup op (leaf t) = leaf (liftUnary op t) := rfl

@[simp] theorem liftUProj_node (cup : L' → L' → L') (op : L → L')
    (cond : Fin (n + 1)) (f₁ f₀ : BitTree α (n + 1) L) :
    liftUProj cup op (.node cond f₁ f₀)
      = if hk : cond.val = n then
          liftBinaryNorm cup (liftUProj cup op f₁) (liftUProj cup op f₀)
        else
          .node (cond.castPredVal hk) (liftUProj cup op f₁) (liftUProj cup op f₀) := rfl

/-! ### The lifted operators preserve the ordering invariant -/

theorem ordered_liftUnaryNorm {l : BitTree α n L} (h : Ordered l) (op : L → L') :
    Ordered (liftUnaryNorm op l) := h.map _

theorem ordered_liftBinaryNorm {l r : BitTree α n L}
    (h : Ordered l) (g : Ordered r) (op : L → L → L') :
    Ordered (liftBinaryNorm op l r) := h.apply _ g

/-- If `l` only tests bits below `b`, so does its projection. -/
theorem below_liftUProj (cup : L' → L' → L') (op : L → L')
    {b : Fin (n + 1)} (hb : ¬ b.val = n) :
    ∀ {l : BitTree α (n + 1) L}, Below l b → Below (liftUProj cup op l) (b.castPredVal hb)
  | leaf _, _ => .base
  | .node _ _ _, .ind hc hl hr => by
    rw [liftUProj_node]
    split_ifs with hk
    · exact (below_liftUProj cup op hb hl).apply _ (below_liftUProj cup op hb hr)
    · exact .ind hc (below_liftUProj cup op hb hl) (below_liftUProj cup op hb hr)

theorem ordered_liftUProj (cup : L' → L' → L') (op : L → L') :
    ∀ {l : BitTree α (n + 1) L}, Ordered l → Ordered (liftUProj cup op l)
  | leaf _, _ => .base
  | .node _ _ _, .ind hl hr bl br => by
    rw [liftUProj_node]
    split_ifs with hk
    · exact ordered_liftBinaryNorm (ordered_liftUProj cup op hl)
        (ordered_liftUProj cup op hr) _
    · exact .ind (ordered_liftUProj cup op hl) (ordered_liftUProj cup op hr)
        (below_liftUProj cup op hk bl) (below_liftUProj cup op hk br)

/-! ### The lifted operators commute with evaluation -/

omit [DecidableSat α] in
theorem eval_liftUnaryNorm (op : L → L') (f : BitTree α n L) (x : Elem σ n) :
    (liftUnaryNorm op f)[x]ₙ = op (f[x]ₙ) := by
  simp only [liftUnaryNorm, evaluation₂, eval_liftUnary]

theorem eval_liftBinaryNorm (op : L → L → L') (f g : BitTree α n L) (x : Elem σ n) :
    (liftBinaryNorm op f g)[x]ₙ = op (f[x]ₙ) (g[x]ₙ) := by
  simp only [liftBinaryNorm, evaluation₂, eval_apply, eval_liftBinaryR]

/-- Projecting out a bit that `f` never tests is the same as fixing it to any `b`. -/
theorem eval_liftUProj_of_below (cup : L' → L' → L') (op : L → L')
    {f : BitTree α (n + 1) L} {p : n < n + 1} (l : Below f ⟨n, p⟩) (x : Elem σ n) (b : Bool) :
    (liftUProj cup op f)[x]ₙ = op (f[(⟨x.1, x.2.snoc b⟩ : Elem σ (n + 1))]ₙ) := by
  match f, l with
  | leaf _, _ => simp [eval_liftUnary]
  | .node ⟨c, _⟩ l r, .ind bound l_less r_less =>
    simp only [Fin.mk_lt_mk] at bound
    have snoc : (x.2.snoc b)[c] = x.2[c] := List.Vector.getElem_snoc_lt bound
    by_cases hx : x.2[c] <;>
      simp [Nat.ne_of_lt bound, snoc, hx, eval_liftUProj_of_below cup op l_less x b,
        eval_liftUProj_of_below cup op r_less x b]

@[simp] theorem leaves₂_liftUnaryNorm (op : L → L') (f : BitTree α n L) :
    leaves₂ (liftUnaryNorm op f) = (leaves₂ f).map op := by
  unfold liftUnaryNorm
  induction f with
  | leaf t => simp
  | node _ l r ihl ihr => simp [ihl, ihr]

/-- Every leaf of a binary lift is `op` applied to a leaf of each argument. -/
theorem mem_leaves₂_liftBinaryNorm (op : L → L → L') {f g : BitTree α n L} {e : L'}
    (h : e ∈ leaves₂ (liftBinaryNorm op f g)) :
    ∃ x ∈ leaves₂ f, ∃ y ∈ leaves₂ g, e = op x y := by
  obtain ⟨t, ht, he⟩ := List.mem_flatMap.mp h
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := mem_leaves_apply _ _ _ ht
  -- pruning only removes leaves
  replace he := leaves_liftBinaryR_subset op t₁ t₂ he
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_productWith.mp (leaves_binary op t₁ t₂ ▸ he)
  exact ⟨x, List.mem_flatMap.mpr ⟨t₁, ht₁, hx⟩, y, List.mem_flatMap.mpr ⟨t₂, ht₂, hy⟩, rfl⟩

end

/-! ### Evaluation lands in the leaves -/

/-- Every evaluation of a bit-then-predicate tree is one of its leaves. -/
theorem eval₂_mem_leaves₂ (f : BitTree α n L) (c : Elem σ n) : f[c]ₙ ∈ leaves₂ f := by
  induction f with
  | leaf t => simpa using eval_mem_leaves t c.1
  | node cond l r ihl ihr =>
    simp only [eval₂_node, leaves₂_node, List.mem_append]
    split_ifs
    · exact Or.inl ihl
    · exact Or.inr ihr

/-! ### Flattening

`flatten₂` turns a bit tree into a single `TTerm` over `PExtension α n`, since this is what a
`SymbolicDerivativeSystem` asks for. -/

private def promoteAtoms : TTerm α L → TTerm (PExtension α n) L
  | leaf r => leaf r
  | .node p t e => .node (.pred p) (promoteAtoms t) (promoteAtoms e)

/-- Flatten a bit-then-predicate tree into one transition term over `PExtension α n`. -/
def flatten₂ : BitTree α n L → TTerm (PExtension α n) L
  | leaf inner => promoteAtoms inner
  | .node i t e => .node (.p i) (flatten₂ t) (flatten₂ e)

private theorem promoteAtoms_eval (t : TTerm α L) (c : Elem σ n) :
    (promoteAtoms (n := n) t)[c] = t[c.1] := by
  induction t with
  | leaf r => rfl
  | node p f g ihf ihg =>
    have h : models (.pred p : PExtension α n) c = models p c.1 := rfl
    simp only [promoteAtoms, eval_node, h, ihf, ihg]

theorem flatten₂_eval (f : BitTree α n L) (c : Elem σ n) : (flatten₂ f)[c] = f[c]ₙ := by
  induction f with
  | leaf inner => simp [flatten₂, promoteAtoms_eval]
  | node cond t e iht ihe =>
    simp only [flatten₂, eval_node, eval₂_node, models_fin, iht, ihe]
    rfl

end BitTree
