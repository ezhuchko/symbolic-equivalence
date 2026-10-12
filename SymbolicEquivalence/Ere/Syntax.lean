universe u

/-- Extended regular expressions, with intersection and negation. -/
inductive Ere (α : Type u) where
  | ε                 : Ere α
  | pred (e : α)      : Ere α
  | union       : Ere α → Ere α → Ere α
  | intersection      : Ere α → Ere α → Ere α
  | concatenation     : Ere α → Ere α → Ere α
  | star              : Ere α → Ere α
  | negation          : Ere α → Ere α
  deriving Repr, Ord, DecidableEq, Hashable

namespace Ere

scoped infixr:35 " ⋓ "  => Ere.union
scoped infixr:40 " ⋒ "  => Ere.intersection
scoped infixr:50 " ⬝ "  => Ere.concatenation
scoped postfix:max "★"  => Ere.star
scoped prefix:max "~"   => Ere.negation

end Ere

/-- `R⁽n⁾` is `R` concatenated `n` times. -/
@[simp]
def Ere.repeatCat (R : Ere α) (n : Nat) : Ere α :=
  match n with
  | 0          => .ε
  | Nat.succ n => .concatenation R (repeatCat R n)

namespace Ere
scoped notation f "⁽" n "⁾" => Ere.repeatCat f n
end Ere
