import SymbolicEquivalence.Ereq.Derivative
import SymbolicEquivalence.Ereq.Finiteness.Pieces

/-!
# Finiteness of the state space

`⊕(pieces r)` is a fixed finite list containing, up to `≅`, every state reachable from `r` by
iterated symbolic derivation (`EreqAtomic.derivWord_mem_pieces`), and every derivative of its
own members (`EreqAtomic.deriv_mem_subsetUnions_pieces`).

The `∃ₐ` case differs from the others because `liftUProj` joins the two branches of the
projected bit with `⋓ₐ`. A single leaf of the projected tree is therefore a union of leaves of
the original one (`mem_leaves₂_liftUExists`).
-/

open EreqAtomic TTerm BitTree List Sim
open scoped UpTo

variable {α σ : Type*} [EffectiveBooleanAlgebra α σ] [DecidableSat α]

namespace EreqAtomic

/-- The leaves (states) of the transition term of `r`. -/
def step (r : EreqAtomic α n) : List (EreqAtomic α n) := leaves₂ (ρ r)

/-! ### Unfolding `step` one constructor at a time -/

theorem step_eps : step (ε : EreqAtomic α n) = [bot] := rfl

/-- The derivative of a predicate has the two leaves `ε` and `bot`, in an order that depends
    on `φ`. -/
theorem mem_step_pred {φ : FundamentalPredicate α n} {e : EreqAtomic α n}
    (h : e ∈ step (pred φ)) : e = ε ∨ e = bot := by
  cases φ <;> simp_all [step, derivative]; tauto

theorem step_union (l r : EreqAtomic α n) :
    step (l ⋓ₐ r) = leaves₂ (liftBinaryNorm (· ⋓ₐ ·) (ρ l) (ρ r)) := rfl

theorem step_inter (l r : EreqAtomic α n) :
    step (l ⋒ₐ r) = leaves₂ (liftBinaryNorm (· ⋒ₐ ·) (ρ l) (ρ r)) := rfl

theorem step_cat_nullable (l r : EreqAtomic α n) (h : nullable l = true) :
    step (l ⬝ₐ r) =
      leaves₂ (liftBinaryNorm (· ⋓ₐ ·) (liftUnaryNorm (· ⬝ₐ r) (ρ l)) (ρ r)) := by
  rw [step, derivative, ite_eq_left_of_eq_true _ _ (eq_true h)]

theorem step_cat_not_nullable (l r : EreqAtomic α n) (h : nullable l = false) :
    step (l ⬝ₐ r) = (step l).map (· ⬝ₐ r) := by
  rw [step, derivative, ite_eq_right_of_eq_false _ _ (by simp [h]), leaves₂_liftUnaryNorm, step]

theorem step_star (r : EreqAtomic α n) : step (r★ₐ) = (step r).map (· ⬝ₐ r★ₐ) :=
  leaves₂_liftUnaryNorm _ _

theorem step_neg (r : EreqAtomic α n) : step (~ₐ r) = (step r).map (~ₐ ·) :=
  leaves₂_liftUnaryNorm _ _

theorem step_exists (r : EreqAtomic α (n + 1)) :
    step (∃ₐ r) = leaves₂ (liftUExists (ρ r)) := rfl

/-- A leaf of an existentially projected tree is a union of `∃ₐ`-images of leaves of the
    original tree. -/
theorem mem_leaves₂_liftUExists {f : DerTree α (n + 1)} {e : EreqAtomic α n}
    (h : e ∈ leaves₂ (liftUExists f)) :
    ∃ xs : List (EreqAtomic α (n + 1)),
      xs ≠ [] ∧ xs ⊆ leaves₂ f ∧ e ≅ unionOf (xs.map (∃ₐ ·)) := by
  match f with
  | .leaf t =>
    simp only [liftUProj_leaf, leaves₂_leaf, leaves_map, mem_map] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨[x], cons_ne_nil x [], by simpa using hx, refl⟩
  | .node cond f₁ f₀ =>
    rw [liftUExists, liftUProj_node] at h
    split at h
    · obtain ⟨x, hx, y, hy, rfl⟩ := mem_leaves₂_liftBinaryNorm _ h
      obtain ⟨as, as_ne, as_sub, as_eq⟩ := mem_leaves₂_liftUExists hx
      obtain ⟨bs, bs_ne, bs_sub, bs_eq⟩ := mem_leaves₂_liftUExists hy
      refine ⟨as ++ bs, append_ne_nil_of_left_ne_nil as_ne _, ?_, ?_⟩
      · rw [leaves₂_node, append_subset]
        exact ⟨List.Subset.trans as_sub (subset_append_left _ _),
               List.Subset.trans bs_sub (subset_append_right _ _)⟩
      · rw [map_append]
        exact trans (union_cong as_eq bs_eq)
          (symm (unionOf_append (mt map_eq_nil_iff.mp as_ne) (mt map_eq_nil_iff.mp bs_ne)))
    · rw [leaves₂_node] at h ⊢
      rcases mem_append.mp h with h | h <;>
        obtain ⟨xs, ne, sub, eq⟩ := mem_leaves₂_liftUExists h
      · exact ⟨xs, ne, List.Subset.trans sub (subset_append_left _ _), eq⟩
      · exact ⟨xs, ne, List.Subset.trans sub (subset_append_right _ _), eq⟩

theorem step_to_pieces {e f : EreqAtomic α n} (e_in : e ∈ step f) :
    ∃ xs, unionOf xs ≅ e ∧ xs ∈ neSubsets (pieces f) := by
  induction f with
  | ε =>
    obtain rfl : e = bot := by simpa only [step_eps, mem_singleton] using e_in
    exact ⟨[_], refl, neSubsets_singleton (by rw [pieces]; simp)⟩
  | pred φ =>
    rcases mem_step_pred e_in with rfl | rfl <;>
      exact ⟨[_], refl, neSubsets_singleton (by rw [pieces]; simp)⟩
  | union l r ihl ihr =>
    rw [step_union] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves₂_liftBinaryNorm _ e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨xs ++ ys,
      trans (unionOf_append (ne_nil_of_mem_neSubsets xs_in) (ne_nil_of_mem_neSubsets ys_in))
        (union_cong hx hy),
      by rw [pieces]; exact neSubsets_append xs_in ys_in⟩
  | intersection l r ihl ihr =>
    rw [step_inter] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves₂_liftBinaryNorm _ e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨[_], inter_cong hx hy, neSubsets_singleton (by
      rw [pieces]
      exact mem_productWith.mpr ⟨_, mem_subsetUnions xs_in, _, mem_subsetUnions ys_in, rfl⟩)⟩
  | concatenation l r ihl ihr =>
    by_cases hnull : nullable l = true
    · rw [step_cat_nullable l r hnull] at e_in
      obtain ⟨_, ha, b, hb, rfl⟩ := mem_leaves₂_liftBinaryNorm _ e_in
      rw [leaves₂_liftUnaryNorm, mem_map] at ha
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨xs, hx, xs_in⟩ := ihl ha
      obtain ⟨ys, hy, ys_in⟩ := ihr hb
      refine ⟨(unionOf xs ⬝ₐ r) :: ys, ?_,
        by rw [pieces]
           exact neSubsets_append (neSubsets_singleton (mem_map_subsetUnions xs_in)) ys_in⟩
      rw [unionOf_cons _ (ne_nil_of_mem_neSubsets ys_in)]
      exact union_cong (cat_cong hx refl) hy
    · rw [step_cat_not_nullable l r (Bool.eq_false_of_ne_true hnull), mem_map] at e_in
      obtain ⟨a, ha, rfl⟩ := e_in
      obtain ⟨xs, hx, xs_in⟩ := ihl ha
      exact ⟨[_], cat_cong hx refl, neSubsets_singleton
        (by rw [pieces]; exact mem_append_left _ (mem_map_subsetUnions xs_in))⟩
  | star r ih =>
    rw [step_star, mem_map] at e_in
    obtain ⟨a, ha, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ih ha
    exact ⟨[_], cat_cong hx refl, neSubsets_singleton
      (by rw [pieces]; exact mem_cons_of_mem _ (mem_map_subsetUnions xs_in))⟩
  | negation r ih =>
    rw [step_neg, mem_map] at e_in
    obtain ⟨a, ha, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ih ha
    exact ⟨[_], neg_cong hx,
      neSubsets_singleton (by rw [pieces]; exact mem_map_subsetUnions xs_in)⟩
  | existential r ih =>
    rw [step_exists] at e_in
    obtain ⟨as, as_ne, as_sub, e_eq⟩ := mem_leaves₂_liftUExists e_in
    -- each `∃ₐ a` is, up to `≅`, a piece of `∃ₐ r`, then deduplicate the union
    have sub : as.map (∃ₐ ·) ⊆[ (· ≅ ·) ] pieces (∃ₐ r) := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
      obtain ⟨xs, hx, xs_in⟩ := ih (as_sub ha)
      exact ⟨_, by rw [pieces]; exact mem_map_subsetUnions xs_in, exists_cong (symm hx)⟩
    obtain ⟨us, us_nd, us_ne, us_sub, us_eq⟩ :=
      unionOf_nodup_equiv (mt map_eq_nil_iff.mp as_ne) sub
    exact ⟨us, symm (trans e_eq us_eq), mem_neSubsets_of_nodup us_ne us_sub us_nd⟩

theorem step_to_subsetUnions {r : EreqAtomic α n} :
    step r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun _ in_step =>
  have ⟨xs, hx, xs_in⟩ := step_to_pieces in_step
  ⟨unionOf xs, mem_subsetUnions xs_in, symm hx⟩

/-- Every iterated derivative of `r` is similar to a member of `⊕(pieces r)`. -/
theorem derivWord_mem_pieces {r : EreqAtomic α n} (v : Word σ n) :
    (rawSystem α σ n).derivWord r v ∈[ (· ≅ ·) ] ⊕(pieces r) :=
  match v with
  | []     => subsetUnions_pieces_refl
  | c :: v => by
    change (rawSystem α σ n).derivWord ((flatten₂ (ρ r))[c]) v ∈[ (· ≅ ·) ] _
    rw [flatten₂_eval]
    exact subsetUnions_pieces_trans (derivWord_mem_pieces v)
      (step_to_subsetUnions _ (eval₂_mem_leaves₂ (ρ r) c))

/-- A derivative of a member of `⊕(pieces root)` is again in it up to `≅`. -/
theorem deriv_mem_subsetUnions_pieces {root y : EreqAtomic α n} (hy : y ∈ ⊕(pieces root))
    (c : Elem σ n) :
    (ρ y)[c]ₙ ∈[ (· ≅ ·) ] ⊕(pieces root) :=
  subsetUnions_pieces_trans (step_to_subsetUnions _ (eval₂_mem_leaves₂ (ρ y) c))
    ⟨y, hy, Sim.refl⟩

end EreqAtomic
