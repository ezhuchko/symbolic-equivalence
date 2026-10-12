import SymbolicEquivalence.UpTo
import SymbolicEquivalence.Ere.Syntax

/-! # Similarity: `⋓` up to associativity, deduplication and idempotence -/

open Ere
open scoped UpTo

universe u

variable {α : Type u}

namespace Ere

/-- Associativity, right deduplication and idempotence of `⋓`, closed under congruence. -/
inductive Sim : Ere α → Ere α → Prop where
  | assoc      : Sim ((R₁ ⋓ R₂) ⋓ R₃) (R₁ ⋓ (R₂ ⋓ R₃))
  | dedup      : Sim (R₁ ⋓ R₂ ⋓ R₁) (R₁ ⋓ R₂)
  | idem       : Sim (R ⋓ R) R
  | refl       : Sim R R
  | symm       : Sim R₁ R₂ → Sim R₂ R₁
  | trans      : Sim R R₁ → Sim R₁ R₂ → Sim R R₂
  | neg_cong   : Sim R₁ R₂ → Sim ~R₁ ~R₂
  | union_cong   : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⋓ S₁) (R₂ ⋓ S₂)
  | inter_cong : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⋒ S₁) (R₂ ⋒ S₂)
  | cat_cong   : Sim R₁ R₂ → Sim S₁ S₂ → Sim (R₁ ⬝ S₁) (R₂ ⬝ S₂)
  | star_cong  : Sim R₁ R₂ → Sim (R₁★) (R₂★)
scoped infix:37 " ≅ " => Sim
end Ere
open Ere.Sim

theorem subsetUpTo_trans_sim {xs ys zs : List (Ere α)}
    (h : xs ⊆[ (· ≅ ·) ] ys) (h1 : ys ⊆[ (· ≅ ·) ] zs) :
    xs ⊆[ (· ≅ ·) ] zs := subsetUpTo_trans { trans := Sim.trans } h h1

theorem subset_to_subsetUpTo_sim {xs ys : List (Ere α)} (h : xs ⊆ ys) :
    xs ⊆[ (· ≅ ·) ] ys := subset_to_subsetUpTo { refl := fun _ => Sim.refl } h

theorem subsetUpTo_sim_cons (xs : List (Ere α)) :
    xs ⊆[ (· ≅ ·) ] (x :: xs) :=
  match xs with
  | [] => subset_to_subsetUpTo_sim (List.nil_subset [x])
  | y :: ys => fun z hz =>
    match List.mem_cons.mp hz with
    | Or.inl _ => ⟨z, List.mem_cons_of_mem x hz, refl⟩
    | Or.inr hz' =>
      have ⟨w, hw, hzw⟩ := (subsetUpTo_sim_cons (x := y) ys) z hz'
      ⟨w, List.mem_cons_of_mem x hw, hzw⟩

theorem equalityUpTo_refl_sim {xs : List (Ere α)} :
    xs =[ (· ≅ ·) ] xs := equalityUpTo_refl { refl := fun _ => Sim.refl }

theorem equalityUpTo_trans_sim {xs ys zs : List (Ere α)}
    (h : xs =[ (· ≅ ·) ] ys) (h1 : ys =[ (· ≅ ·) ] zs) :
    xs =[ (· ≅ ·) ] zs :=
  equalityUpTo_trans { trans := Sim.trans } h h1
