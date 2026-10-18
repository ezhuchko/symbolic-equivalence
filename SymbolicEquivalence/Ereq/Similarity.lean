import SymbolicEquivalence.UpTo
import SymbolicEquivalence.Ereq.Syntax

/-! # Similarity: `⋓ₐ` up to associativity, deduplication and idempotence -/

open EreqAtomic
open scoped UpTo

universe u

variable {α : Type u}

namespace EreqAtomic

/-- Associativity, right deduplication and idempotence of `⋓ₐ`, closed under congruence. -/
inductive Sim : EreqAtomic α n → EreqAtomic α n → Prop where
  | assoc       : Sim ((R₁ ⋓ₐ R₂) ⋓ₐ R₃) (R₁ ⋓ₐ (R₂ ⋓ₐ R₃))
  | dedup       : Sim (R₁ ⋓ₐ R₂ ⋓ₐ R₁) (R₁ ⋓ₐ R₂)
  | idem        : Sim (R ⋓ₐ R) R
  | refl        : Sim R R
  | symm        : Sim R₁ R₂ → Sim R₂ R₁
  | trans       : Sim R R₁ → Sim R₁ R₂ → Sim R R₂
  | neg_cong    : Sim R₁ R₂ → Sim ~ₐR₁ ~ₐR₂
  | union_cong  : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⋓ₐ S₁) (R₂ ⋓ₐ S₂)
  | inter_cong  : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⋒ₐ S₁) (R₂ ⋒ₐ S₂)
  | cat_cong    : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⬝ₐ S₁) (R₂ ⬝ₐ S₂)
  | star_cong   : Sim R₁ R₂ → Sim (R₁★ₐ) (R₂★ₐ)
  | exists_cong : Sim R₁ R₂ → Sim (∃ₐ R₁) (∃ₐ R₂)
scoped infix:37 " ≅ " => Sim
open EreqAtomic.Sim

theorem subsetUpTo_trans_sim {xs ys zs : List (EreqAtomic α n)}
    (h : xs ⊆[ (· ≅ ·) ] ys) (h1 : ys ⊆[ (· ≅ ·) ] zs) :
    xs ⊆[ (· ≅ ·) ] zs := subsetUpTo_trans { trans := Sim.trans } h h1

theorem subset_to_subsetUpTo_sim {xs ys : List (EreqAtomic α n)} (h : xs ⊆ ys) :
    xs ⊆[ (· ≅ ·) ] ys := subset_to_subsetUpTo { refl := fun _ => Sim.refl } h

theorem equalityUpTo_refl_sim {xs : List (EreqAtomic α n)} :
    xs =[ (· ≅ ·) ] xs := equalityUpTo_refl { refl := fun _ => Sim.refl }

theorem equalityUpTo_trans_sim {xs ys zs : List (EreqAtomic α n)}
    (h : xs =[ (· ≅ ·) ] ys) (h1 : ys =[ (· ≅ ·) ] zs) :
    xs =[ (· ≅ ·) ] zs :=
  equalityUpTo_trans { trans := Sim.trans } h h1

end EreqAtomic
