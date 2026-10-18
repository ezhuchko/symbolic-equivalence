import SymbolicEquivalence.Ereq.Syntax
import SymbolicEquivalence.Ereq.Word

/-!
# Negation normal form of predicates

`Ereq.nnf` turns an `Ereq` into an `EreqAtomic`. It pushes the negations in each predicate
down to the atoms, then replaces `and` and `or` with regex intersection and union.
-/

open scoped Ereq EreqAtomic

universe u

variable {α σ : Type*}

/-- Negation normal form of `PExtension`, where negation appears only directly in front of
    atoms and the only connectives above atoms are `and` and `or`.

    `p, q ::= ⊤ | ⊥ | pᵢ | ψ | ¬pᵢ | ¬ψ | (p ∧ q) | (p ∨ q)` -/
inductive PExtensionNNF (α : Type u) (n : Nat) where
  | p    (i : Fin n) : PExtensionNNF α n
  | notP (i : Fin n) : PExtensionNNF α n
  | pred (p : α) : PExtensionNNF α n
  | notPred (p : α) : PExtensionNNF α n
  | top : PExtensionNNF α n
  | bot : PExtensionNNF α n
  | and : PExtensionNNF α n → PExtensionNNF α n → PExtensionNNF α n
  | or  : PExtensionNNF α n → PExtensionNNF α n → PExtensionNNF α n

@[simp]
def PExtensionNNF.negate : PExtensionNNF α n → PExtensionNNF α n
  | .p i       => .notP i
  | .notP i    => .p i
  | .pred a    => .notPred a
  | .notPred q => .pred q
  | .and q r   => .or (negate q) (negate r)
  | .or q r    => .and (negate q) (negate r)
  | .bot       => .top
  | .top       => .bot

/-- Negation normal form for `PExtension α n` predicates. -/
@[simp]
def PExtension.nnfp : PExtension α n → PExtensionNNF α n
  | .not φ   => (nnfp φ).negate
  | .and φ ψ => .and (nnfp φ) (nnfp ψ)
  | .or φ ψ  => .or (nnfp φ) (nnfp ψ)
  | .bot    => .bot
  | .top    => .top
  | .p i    => .p i
  | .pred a => .pred a

/-- Turn the connectives of an NNF predicate into regex connectives over atomic predicates. -/
@[simp]
def PExtensionNNF.externaliseNnf [Compl α] [Top α] [Bot α] : PExtensionNNF α n → EreqAtomic α n
  | .p i       => .pred (.p i)
  | .pred a    => .pred (.pred a)
  | .notP i    => .pred (.notP i)
  | .notPred a => .pred (.pred aᶜ)
  | .top       => .pred (.pred ⊤)
  | .bot       => .pred (.pred ⊥)
  | .and φ ψ   => .intersection (externaliseNnf φ) (externaliseNnf ψ)
  | .or φ ψ    => .union (externaliseNnf φ) (externaliseNnf ψ)

@[simp]
def PExtensionNNF.models [Models α σ] : PExtensionNNF α n → Elem σ n → Bool
  | .p i,       ⟨_, u⟩ => u[i]
  | .notP i,    ⟨_, u⟩ => !u[i]
  | .pred φ,    ⟨a, _⟩ => Models.models φ a
  | .notPred φ, ⟨a, _⟩ => !Models.models φ a
  | .top,       _      => true
  | .bot,       _      => false
  | .and φ ψ,   c      => φ.models c && ψ.models c
  | .or φ ψ,    c      => φ.models c || ψ.models c

/-- Negating an NNF predicate negates its denotation. -/
@[simp]
theorem PExtensionNNF.models_negate [Models α σ] (p : PExtensionNNF α n) (c : Elem σ n) :
    p.negate.models c = !p.models c := by
  induction p <;> simp [*]

/-- `nnfp` preserves the denotation. -/
theorem PExtension.nnfp_correct [Models α σ] (q : PExtension α n) (c : Elem σ n) :
    (nnfp q).models c = q.models c := by
  induction q <;> simp [PExtension.models, *]

/-- Replace every predicate `e` by `e.nnfp.externaliseNnf`. -/
@[simp]
def Ereq.nnf [Compl α] [Top α] [Bot α] : Ereq α n → EreqAtomic α n
  | .pred e => e.nnfp.externaliseNnf
  | .ε      => .ε
  | l ⋓ r   => nnf l ⋓ₐ nnf r
  | l ⋒ r   => nnf l ⋒ₐ nnf r
  | l ⬝ r   => nnf l ⬝ₐ nnf r
  | r★      => (nnf r)★ₐ
  | ~r      => ~ₐ(nnf r)
  | ∃ʳ r    => ∃ₐ (nnf r)
