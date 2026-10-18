import SymbolicEquivalence.Ereq.ExtendedEBA

/-!
# Syntax of regular expressions with existential quantification

`Ereq` are regular expressions with existential quantification, and `EreqAtomic` are the same
expressions restricted to atomic predicates.
-/

register_simp_attr matches_simps

universe u

variable {α : Type*}

/-- The type of regular expressions with the existential quantifier. -/
inductive Ereq (α : Type u) : Nat → Type u
  | ε             : Ereq α n
  | pred (e : PExtension α n) : Ereq α n
  | union         : Ereq α n → Ereq α n → Ereq α n
  | intersection  : Ereq α n → Ereq α n → Ereq α n
  | concatenation : Ereq α n → Ereq α n → Ereq α n
  | star          : Ereq α n → Ereq α n
  | negation      : Ereq α n → Ereq α n
  | existential   : Ereq α (n + 1) → Ereq α n
  deriving Repr, DecidableEq

namespace Ereq

scoped infixr:35 " ⋓ "  => Ereq.union
scoped infixr:40 " ⋒ "  => Ereq.intersection
scoped infixr:50 " ⬝ "  => Ereq.concatenation
scoped postfix:max "★"  => Ereq.star
scoped prefix:max "~"   => Ereq.negation
scoped prefix:max "∃ʳ " => Ereq.existential

/-- `R⁽k⁾` is `R` concatenated `k` times. -/
@[simp]
def repeatCat (R : Ereq α n) (k : Nat) : Ereq α n :=
  match k with
  | 0          => .ε
  | Nat.succ k => R ⬝ (repeatCat R k)

scoped notation f "⁽" n "⁾" => Ereq.repeatCat f n

/-- `_*`, matching every word. -/
def any [Top α] : Ereq α n := (.pred (.pred (⊤ : α)))★

end Ereq

/-- Regular expressions with the existential quantifier whose predicates are atomic
    `FundamentalPredicate`s. -/
inductive EreqAtomic (α : Type u) : Nat → Type u
  | ε             : EreqAtomic α n
  | pred (e : FundamentalPredicate α n) : EreqAtomic α n
  | union         : EreqAtomic α n → EreqAtomic α n → EreqAtomic α n
  | intersection  : EreqAtomic α n → EreqAtomic α n → EreqAtomic α n
  | concatenation : EreqAtomic α n → EreqAtomic α n → EreqAtomic α n
  | star          : EreqAtomic α n → EreqAtomic α n
  | negation      : EreqAtomic α n → EreqAtomic α n
  | existential   : EreqAtomic α (n + 1) → EreqAtomic α n
  deriving Repr, DecidableEq

namespace EreqAtomic

scoped infixr:35 " ⋓ₐ "  => EreqAtomic.union
scoped infixr:40 " ⋒ₐ "  => EreqAtomic.intersection
scoped infixr:50 " ⬝ₐ "  => EreqAtomic.concatenation
scoped postfix:max "★ₐ"  => EreqAtomic.star
scoped prefix:max "~ₐ"   => EreqAtomic.negation
scoped prefix:max "∃ₐ "  => EreqAtomic.existential

/-- `R⁽k⁾ₐ` is `R` concatenated `k` times. -/
@[simp]
def repeatCat (R : EreqAtomic α n) (k : Nat) : EreqAtomic α n :=
  match k with
  | 0          => .ε
  | Nat.succ k => R ⬝ₐ (repeatCat R k)

scoped notation f "⁽" n "⁾ₐ" => EreqAtomic.repeatCat f n

/-- The expression that matches no word. -/
abbrev bot {α : Type u} [Bot α] {n : Nat} : EreqAtomic α n := .pred (.pred ⊥)

end EreqAtomic
