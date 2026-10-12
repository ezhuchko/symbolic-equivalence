import SymbolicEquivalence.TransitionTerm
import Mathlib.Data.Set.Finite.Basic

/-!
# Symbolic derivative systems

A `SymbolicDerivativeSystem α σ β` presents languages by symbolic derivatives. Here `α` is the
predicate algebra, `σ` the (possibly infinite) alphabet, and `β` the type of states, which are
the leaves of `TTerm α β`.

The structure needs only `Models α σ`, since its fields just evaluate transition terms.
The Boolean structure and satisfiability oracle are required only where systems are
combined or enumerated (`succs` below, `SymbolicEquivalence.Checker.Product`).
-/

open TTerm

/-- A symbolic derivative system has states `β` over predicates `α` and alphabet `σ`, together
with the laws relating derivatives to languages. -/
structure SymbolicDerivativeSystem (α σ β : Type*) [Models α σ] where
  /-- Whether a state accepts the empty word. -/
  null : β → Bool
  /-- The symbolic derivative. -/
  symDer : β → TTerm α β
  /-- The language of a state. -/
  Lang : β → List σ → Prop
  /-- Well-formedness of states. -/
  WF : β → Prop
  /-- (C1) `null` decides the empty word. -/
  null_iff : ∀ {s}, WF s → (Lang s [] ↔ null s)
  /-- (C2) The derivative computes the one-character quotient. -/
  deriv_iff : ∀ {s}, WF s → ∀ (c : σ) (w : List σ), Lang s (c :: w) ↔ Lang ((symDer s)[c]) w
  /-- (C3) Derivatives preserve well-formedness, so (C2) can be iterated. -/
  wf_deriv : ∀ {s}, WF s → ∀ c : σ, WF ((symDer s)[c])

namespace SymbolicDerivativeSystem

variable {α σ β : Type*}

section Core
variable [Models α σ] (D : SymbolicDerivativeSystem α σ β)

/-! ### Derivatives along words -/

/-- The derivative by a character. -/
def deriv (s : β) (c : σ) : β := (D.symDer s)[c]

/-- The derivative along a word. -/
def derivWord : β → List σ → β
  | s, [] => s
  | s, c :: w => derivWord (D.deriv s c) w

@[simp] theorem derivWord_nil (s : β) : D.derivWord s [] = s := rfl

@[simp] theorem derivWord_cons (s : β) (c : σ) (w : List σ) :
    D.derivWord s (c :: w) = D.derivWord (D.deriv s c) w := rfl

@[simp] theorem derivWord_append (s : β) (v w : List σ) :
    D.derivWord s (v ++ w) = D.derivWord (D.derivWord s v) w := by
  induction v generalizing s with
  | nil => rfl
  | cons c v ih => exact ih _

/-- (C3) Derivatives along a word preserve well-formedness. -/
theorem wf_derivWord : ∀ (w : List σ) {s : β}, D.WF s → D.WF (D.derivWord s w)
  | [], _, hs => hs
  | c :: w, _, hs => wf_derivWord w (D.wf_deriv hs c)

/-- (C2) The derivative along `v` denotes the left quotient by `v`. -/
theorem lang_derivWord : ∀ (v : List σ) {s : β}, D.WF s → ∀ w : List σ,
    D.Lang (D.derivWord s v) w ↔ D.Lang s (v ++ w)
  | [], _, _, _ => Iff.rfl
  | c :: v, _, hs, w =>
    (lang_derivWord v (D.wf_deriv hs c) w).trans (D.deriv_iff hs c (v ++ w)).symm

/-! ### Matching -/

/-- The matcher, which derives along the word and then tests nullability. -/
def accepts (s : β) (w : List σ) : Bool := D.null (D.derivWord s w)

theorem accepts_iff {s : β} (hs : D.WF s) (w : List σ) : D.accepts s w ↔ D.Lang s w := by
  rw [accepts, ← D.null_iff (D.wf_derivWord w hs), D.lang_derivWord w hs [], List.append_nil]

/-! ### Reachability -/

section Reach

/-- `t` is the derivative of `s` along some word. -/
def Reach (s t : β) : Prop := ∃ v, D.derivWord s v = t

variable {D}

theorem Reach.refl (s : β) : D.Reach s s := ⟨[], rfl⟩

theorem Reach.trans {s t u} : D.Reach s t → D.Reach t u → D.Reach s u
  | ⟨v, hv⟩, ⟨w, hw⟩ => ⟨v ++ w, by rw [derivWord_append, hv, hw]⟩

theorem Reach.deriv {s t} (h : D.Reach s t) (c : σ) : D.Reach s (D.deriv t c) :=
  h.trans ⟨[c], rfl⟩

/-- If `s` accepts every word, every state reachable from `s` is nullable. -/
theorem Reach.null_of_forall_lang {s t} (h : D.Reach s t) (hs : D.WF s)
    (hall : ∀ w, D.Lang s w) : D.null t = true := by
  obtain ⟨v, rfl⟩ := h
  exact (D.accepts_iff hs v).2 (hall v)

end Reach

/-! ### Language equivalence -/

/-- Language equivalence of two states. -/
def SemEquiv (p q : β) : Prop := ∀ w : List σ, D.Lang p w ↔ D.Lang q w

variable {D} in
/-- Equivalent well-formed states agree on `null`, by (C1). -/
theorem SemEquiv.null_eq {p q} (hp : D.WF p) (hq : D.WF q) (h : D.SemEquiv p q) :
    D.null p = D.null q := by
  rw [Bool.eq_iff_iff, ← D.null_iff hp, ← D.null_iff hq]
  exact h []

/-! ### Boundedness -/

/-- (C4) A well-formed state has finitely many derivatives, which is what makes a worklist
    loop terminate. -/
class Bounded (D : SymbolicDerivativeSystem α σ β) : Prop where
  finite_reach : ∀ {s}, D.WF s → {t | D.Reach s t}.Finite

/-- Derivatives along a word stay inside a list closed under derivatives. -/
theorem derivWord_mem_of_closed {B : List β} (hB : ∀ t ∈ B, ∀ c : σ, D.deriv t c ∈ B) :
    ∀ (v : List σ) {t : β}, t ∈ B → D.derivWord t v ∈ B
  | [], _, ht => ht
  | c :: v, _, ht => derivWord_mem_of_closed hB v (hB _ ht c)

variable {D} in
/-- (C4) holds if every well-formed state lies in a finite list closed under derivatives. -/
theorem Bounded.of_closed
    (h : ∀ {s}, D.WF s → ∃ B : List β, s ∈ B ∧ ∀ t ∈ B, ∀ c : σ, D.deriv t c ∈ B) :
    D.Bounded where
  finite_reach hs :=
    let ⟨B, hsB, hB⟩ := h hs
    B.finite_toSet.subset fun _ ⟨v, hv⟩ => hv ▸ D.derivWord_mem_of_closed hB v hsB

end Core

/-! ### Successors

The worklist explores `succs s` instead of all of `σ`. Computing it needs the
satisfiability oracle, hence the extra assumptions on `α`. -/

section Succs
variable [EffectiveBooleanAlgebra α σ] [DecidableSat α] (D : SymbolicDerivativeSystem α σ β)

/-- The successors of a state, which are the reachable leaves of its transition term. -/
def succs (s : β) : List β := reachableLeaves (D.symDer s) ⊤

/-- `succs` describes exactly the derivatives of `s`. -/
theorem mem_succs {s t : β} : t ∈ D.succs s ↔ ∃ c : σ, D.deriv s c = t :=
  mem_reachableLeaves_top

@[simp] theorem deriv_mem_succs (s : β) (c : σ) : D.deriv s c ∈ D.succs s :=
  D.mem_succs.mpr ⟨c, rfl⟩

variable {D}

theorem Reach.succ {s t u : β} (h : D.Reach s t) (hu : u ∈ D.succs t) : D.Reach s u := by
  obtain ⟨c, rfl⟩ := D.mem_succs.mp hu
  exact h.deriv c

end Succs

end SymbolicDerivativeSystem
