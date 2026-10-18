import SymbolicEquivalence.TransitionTerm
import SymbolicEquivalence.Ereq.UnionOf

/-!
# Pieces

`pieces r` is a finite list of expressions out of which every derivative of `r` is built, up
to `≅`. `UnionOf.lean` folds it into `⊕(pieces r)`, and `Closure.lean` proves that this list is
closed under derivatives, up to `≅`.
-/

open EreqAtomic TTerm List Sim
open scoped UpTo

variable {α : Type*} [Bot α]

namespace EreqAtomic

/-- The building blocks of the derivatives of `r`. Every derivative of `r` is, up to `≅`, a
    union of elements of `pieces r`. -/
def pieces : EreqAtomic α n → List (EreqAtomic α n)
  | ε       => [ε, bot]
  | pred φ  => [pred φ, ε, bot]
  | l ⋓ₐ r  => pieces l ++ pieces r
  | l ⋒ₐ r  => productWith (· ⋒ₐ ·) ⊕(pieces l) ⊕(pieces r)
  | l ⬝ₐ r  => map (· ⬝ₐ r) ⊕(pieces l) ++ pieces r
  | r★ₐ     => r★ₐ :: map (· ⬝ₐ r★ₐ) ⊕(pieces r)
  | ~ₐ r    => map (~ₐ ·) ⊕(pieces r)
  | ∃ₐ r    => map (∃ₐ ·) ⊕(pieces r)

theorem pieces_refl {r : EreqAtomic α n} :
    ∃ xs, xs ∈ neSubsets (pieces r) ∧ unionOf xs ≅ r :=
  match r with
  | ε       => ⟨[ε], neSubsets_singleton mem_cons_self, refl⟩
  | pred φ  => ⟨[pred φ], neSubsets_singleton mem_cons_self, refl⟩
  | r★ₐ     => ⟨[r★ₐ], neSubsets_singleton mem_cons_self, refl⟩
  | l ⋓ₐ r  =>
    have ⟨xs, xs_in, hx⟩ := pieces_refl (r := l)
    have ⟨ys, ys_in, hy⟩ := pieces_refl (r := r)
    ⟨xs ++ ys, neSubsets_append xs_in ys_in,
     trans (unionOf_append (ne_nil_of_mem_neSubsets xs_in) (ne_nil_of_mem_neSubsets ys_in))
       (union_cong hx hy)⟩
  | l ⋒ₐ r  =>
    have ⟨xs, xs_in, hx⟩ := pieces_refl (r := l)
    have ⟨ys, ys_in, hy⟩ := pieces_refl (r := r)
    ⟨[unionOf xs ⋒ₐ unionOf ys],
     neSubsets_singleton (mem_productWith.mpr ⟨unionOf xs, mem_subsetUnions xs_in,
                             unionOf ys, mem_subsetUnions ys_in, rfl⟩), inter_cong hx hy⟩
  | l ⬝ₐ r  =>
    have ⟨xs, xs_in, hx⟩ := pieces_refl (r := l)
    ⟨[unionOf xs ⬝ₐ r],
     neSubsets_singleton (mem_append_left _ (mem_map_subsetUnions xs_in)), cat_cong hx refl⟩
  | ~ₐ r    =>
    have ⟨xs, xs_in, hx⟩ := pieces_refl (r := r)
    ⟨[~ₐ(unionOf xs)], neSubsets_singleton (mem_map_subsetUnions xs_in), neg_cong hx⟩
  | ∃ₐ r    =>
    have ⟨xs, xs_in, hx⟩ := pieces_refl (r := r)
    ⟨[∃ₐ(unionOf xs)], neSubsets_singleton (mem_map_subsetUnions xs_in), exists_cong hx⟩

/-! ### Congruence of `pieces` under `≅` -/
section Congruence
variable {l₁ l₂ r₁ r₂ : EreqAtomic α n}

theorem pieces_assoc {R₁ R₂ R₃ : EreqAtomic α n} :
    pieces ((R₁ ⋓ₐ R₂) ⋓ₐ R₃) = pieces (R₁ ⋓ₐ (R₂ ⋓ₐ R₃)) := by
  simp only [pieces, append_assoc]

theorem pieces_idem {R : EreqAtomic α n} : pieces (R ⋓ₐ R) =[ (· ≅ ·) ] pieces R := by
  refine ⟨subset_to_subsetUpTo_sim ?_, subset_to_subsetUpTo_sim ?_⟩
  · intro x hx
    simpa only [pieces, mem_append, or_self] using hx
  · intro x hx
    simp only [pieces, mem_append]
    exact Or.inl hx

theorem pieces_dedup {R₁ R₂ : EreqAtomic α n} :
    pieces (R₁ ⋓ₐ R₂ ⋓ₐ R₁) =[ (· ≅ ·) ] pieces (R₁ ⋓ₐ R₂) := by
  refine ⟨subset_to_subsetUpTo_sim ?_, subset_to_subsetUpTo_sim ?_⟩
  all_goals
    intro x hx
    simp only [pieces, mem_append] at hx ⊢
    tauto

theorem pieces_union_mono
    (hl : pieces l₁ ⊆[ (· ≅ ·) ] pieces l₂) (hr : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
    pieces (l₁ ⋓ₐ r₁) ⊆[ (· ≅ ·) ] pieces (l₂ ⋓ₐ r₂) := by
  intro e he
  rcases mem_append.mp he with h | h
  · obtain ⟨a', a'_mem, a'_sim⟩ := hl e h; exact ⟨a', mem_append_left _ a'_mem, a'_sim⟩
  · obtain ⟨a', a'_mem, a'_sim⟩ := hr e h; exact ⟨a', mem_append_right _ a'_mem, a'_sim⟩

theorem pieces_inter_mono
    (hl : pieces l₁ ⊆[ (· ≅ ·) ] pieces l₂) (hr : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
    pieces (l₁ ⋒ₐ r₁) ⊆[ (· ≅ ·) ] pieces (l₂ ⋒ₐ r₂) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_productWith.mp he
  obtain ⟨a', a'_mem, a'_sim⟩ := subsetUnions_monotone hl _ ha
  obtain ⟨b', b'_mem, b'_sim⟩ := subsetUnions_monotone hr _ hb
  exact ⟨a' ⋒ₐ b', mem_productWith.mpr ⟨a', a'_mem, b', b'_mem, rfl⟩, inter_cong a'_sim b'_sim⟩

theorem pieces_cat_mono
    (hl : pieces l₁ ⊆[ (· ≅ ·) ] pieces l₂) (hr : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂)
    (hsim : r₁ ≅ r₂) :
    pieces (l₁ ⬝ₐ r₁) ⊆[ (· ≅ ·) ] pieces (l₂ ⬝ₐ r₂) := by
  intro e he
  simp only [pieces, mem_append, mem_map] at he
  rcases he with ⟨xs, g1, rfl⟩ | g1
  · obtain ⟨a', a'_mem, a'_sim⟩ := subsetUnions_monotone hl _ g1
    exact ⟨a' ⬝ₐ r₂, mem_append_left _ (mem_map_of_mem a'_mem), cat_cong a'_sim hsim⟩
  · obtain ⟨a', a'_mem, a'_sim⟩ := hr _ g1
    exact ⟨a', mem_append_right _ a'_mem, a'_sim⟩

theorem pieces_star_mono
    (h : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) (hsim : r₁ ≅ r₂) :
    pieces (r₁★ₐ) ⊆[ (· ≅ ·) ] pieces (r₂★ₐ) := by
  intro e he
  simp only [pieces, mem_cons, mem_map] at he
  rcases he with rfl | ⟨zs, hz1, rfl⟩
  · exact ⟨r₂★ₐ, mem_cons_self, star_cong hsim⟩
  · obtain ⟨a', a'_mem, a'_sim⟩ := subsetUnions_monotone h _ hz1
    exact ⟨a' ⬝ₐ r₂★ₐ, mem_cons_of_mem _ (mem_map_of_mem a'_mem),
           cat_cong a'_sim (star_cong hsim)⟩

theorem pieces_neg_mono (h : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
    pieces (~ₐr₁) ⊆[ (· ≅ ·) ] pieces (~ₐr₂) := by
  intro e he
  obtain ⟨zs, hz1, rfl⟩ := mem_map.mp he
  obtain ⟨a', a'_mem, a'_sim⟩ := subsetUnions_monotone h _ hz1
  exact ⟨~ₐa', mem_map_of_mem a'_mem, neg_cong a'_sim⟩

theorem pieces_exists_mono {r₁ r₂ : EreqAtomic α (n + 1)}
    (h : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
    pieces (∃ₐ r₁) ⊆[ (· ≅ ·) ] pieces (∃ₐ r₂) := by
  intro e he
  obtain ⟨zs, hz1, rfl⟩ := mem_map.mp he
  obtain ⟨a', a'_mem, a'_sim⟩ := subsetUnions_monotone h _ hz1
  exact ⟨∃ₐ a', mem_map_of_mem a'_mem, exists_cong a'_sim⟩

end Congruence

/-- If `f ≅ f'`, then `pieces f` and `pieces f'` are equal up to `≅`. -/
theorem pieces_equiv {f f' : EreqAtomic α n} (eqv : f ≅ f') :
    pieces f =[ (· ≅ ·) ] pieces f' := by
  induction eqv with
  | refl                   => exact equalityUpTo_refl_sim
  | symm _ ih              => exact equalityUpTo_symm ih
  | trans _ _ ih1 ih2      => exact equalityUpTo_trans_sim ih1 ih2
  | assoc                  => rw [pieces_assoc]; exact equalityUpTo_refl_sim
  | idem                   => exact pieces_idem
  | dedup                  => exact pieces_dedup
  | union_cong _ _ ih1 ih2 => exact ⟨pieces_union_mono ih1.1 ih2.1, pieces_union_mono ih1.2 ih2.2⟩
  | inter_cong _ _ ih1 ih2 => exact ⟨pieces_inter_mono ih1.1 ih2.1, pieces_inter_mono ih1.2 ih2.2⟩
  | cat_cong _ g ih1 ih2   =>
    exact ⟨pieces_cat_mono ih1.1 ih2.1 g, pieces_cat_mono ih1.2 ih2.2 (symm g)⟩
  | star_cong h ih         => exact ⟨pieces_star_mono ih.1 h, pieces_star_mono ih.2 (symm h)⟩
  | neg_cong _ ih          => exact ⟨pieces_neg_mono ih.1, pieces_neg_mono ih.2⟩
  | exists_cong _ ih       => exact ⟨pieces_exists_mono ih.1, pieces_exists_mono ih.2⟩

/-- A piece of a union is a piece of one of the operands. -/
theorem pieces_unionOf {e : EreqAtomic α n} {xs : List (EreqAtomic α n)} (ne : xs ≠ [])
    (h : e ∈ pieces (unionOf xs)) :
    ∃ g ∈ xs, e ∈ pieces g :=
  match xs with
  | [_] => exists_mem_cons_of [] h
  | e1 :: e2 :: es =>
    match mem_append.mp h with
    | Or.inl h1 => ⟨e1, mem_cons_self, h1⟩
    | Or.inr h1 =>
      have ⟨g, g_mem, hg⟩ := pieces_unionOf (cons_ne_nil e2 es) h1
      ⟨g, mem_cons_of_mem e1 g_mem, hg⟩

theorem subsetUnions_pieces_step {ps : List (EreqAtomic α n)} {a b : EreqAtomic α n}
    (ih : ∀ {x y : EreqAtomic α n}, y ∈ ps → x ∈ pieces y → x ∈[ (· ≅ ·) ] ps)
    (ha : a ∈ ⊕ps) (hb : b ∈ ⊕(pieces a)) :
    b ∈[ (· ≅ ·) ] ⊕ps := by
  obtain ⟨zs, ne_zs, rfl, zs_ps⟩ := subsetUnions_to_neSubset ha
  obtain ⟨as, ne_as, rfl, as_sub⟩ := subsetUnions_to_neSubset hb
  refine subsetUnions_monotone (fun x hx => ?_) (unionOf as)
           (mem_subsetUnions (neSubsets_refl ne_as))
  obtain ⟨pi, pi_in, pi_piece⟩ := pieces_unionOf ne_zs (as_sub hx)
  exact ih (zs_ps pi_in) pi_piece

/-- A piece of a piece of `g` is, up to `≅`, a piece of `g`. -/
theorem pieces_trans {e f g : EreqAtomic α n}
    (h1 : e ∈ pieces f)
    (h2 : f ∈ pieces g) :
    e ∈[ (· ≅ ·) ] pieces g := by
  match g with
  -- a piece of a piece of an atom is already a piece of it
  | ε | pred _ =>
    refine ⟨e, ?_, refl⟩
    simp only [pieces, mem_cons, not_mem_nil, or_false] at h2 ⊢
    rcases h2 with rfl | rfl | rfl <;> simp_all [pieces]
    all_goals tauto
  | g₁ ⋓ₐ g₂ =>
    simp only [pieces, mem_append] at h2
    rcases h2 with g | g <;> obtain ⟨a', a'_mem, a'_sim⟩ := pieces_trans h1 g
    · exact ⟨a', mem_append_left _ a'_mem, a'_sim⟩
    · exact ⟨a', mem_append_right _ a'_mem, a'_sim⟩
  | l ⋒ₐ r =>
    simp only [pieces] at h1 h2
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productWith.mp h2
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_productWith.mp h1
    obtain ⟨c', c'_mem, c'_sim⟩ :=
      subsetUnions_pieces_step (fun hy hx => pieces_trans hx hy) ha hc
    obtain ⟨d', d'_mem, d'_sim⟩ :=
      subsetUnions_pieces_step (fun hy hx => pieces_trans hx hy) hb hd
    exact ⟨c' ⋒ₐ d', mem_productWith.mpr ⟨c', c'_mem, d', d'_mem, rfl⟩,
           inter_cong c'_sim d'_sim⟩
  | l ⬝ₐ r =>
    simp only [pieces, mem_append, mem_map] at h2
    rcases h2 with ⟨a, ha, rfl⟩ | g
    · simp only [pieces, mem_append, mem_map] at h1
      rcases h1 with ⟨b, hb, rfl⟩ | g
      · obtain ⟨b', b'_mem, b'_sim⟩ :=
          subsetUnions_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
        exact ⟨b' ⬝ₐ r, mem_append_left _ (mem_map_of_mem b'_mem), cat_cong b'_sim refl⟩
      · exact ⟨e, mem_append_right _ g, refl⟩
    · obtain ⟨a', a'_mem, a'_sim⟩ := pieces_trans h1 g
      exact ⟨a', mem_append_right _ a'_mem, a'_sim⟩
  | ~ₐ g' =>
    simp only [pieces, mem_map] at h2
    obtain ⟨a, ha, rfl⟩ := h2
    simp only [pieces, mem_map] at h1
    obtain ⟨b, hb, rfl⟩ := h1
    obtain ⟨b', b'_mem, b'_sim⟩ :=
      subsetUnions_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
    exact ⟨~ₐb', mem_map_of_mem b'_mem, neg_cong b'_sim⟩
  | ∃ₐ g' =>
    simp only [pieces, mem_map] at h2
    obtain ⟨a, ha, rfl⟩ := h2
    simp only [pieces, mem_map] at h1
    obtain ⟨b, hb, rfl⟩ := h1
    obtain ⟨b', b'_mem, b'_sim⟩ :=
      subsetUnions_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
    exact ⟨∃ₐ b', mem_map_of_mem b'_mem, exists_cong b'_sim⟩
  | r★ₐ =>
    simp only [pieces, mem_cons, mem_map] at h2
    rcases h2 with rfl | ⟨a, ha, rfl⟩
    · exact ⟨e, h1, refl⟩
    · simp only [pieces, mem_append, mem_map] at h1
      rcases h1 with ⟨b, hb, rfl⟩ | g
      · obtain ⟨b', b'_mem, b'_sim⟩ :=
          subsetUnions_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
        exact ⟨b' ⬝ₐ r★ₐ, mem_cons_of_mem _ (mem_map_of_mem b'_mem), cat_cong b'_sim refl⟩
      · exact ⟨e, g, refl⟩

theorem subsetUnions_pieces_refl {r : EreqAtomic α n} : r ∈[ (· ≅ ·) ] ⊕(pieces r) :=
  have ⟨xs, xs_in, xs_eqv⟩ := pieces_refl (r := r)
  ⟨unionOf xs, mem_subsetUnions xs_in, symm xs_eqv⟩

theorem subsetUnions_pieces_trans {e f g : EreqAtomic α n}
    (h1 : e ∈[ (· ≅ ·) ] ⊕(pieces f))
    (h2 : f ∈[ (· ≅ ·) ] ⊕(pieces g)) :
    e ∈[ (· ≅ ·) ] ⊕(pieces g) := by
  obtain ⟨ff, hff, e_ff⟩ := h1
  obtain ⟨gg, hgg, f_gg⟩ := h2
  obtain ⟨as, ne_as, rfl, as_sub⟩ := subsetUnions_to_neSubset hff
  obtain ⟨zs, ne_zs, rfl, zs_sub⟩ := subsetUnions_to_neSubset hgg
  -- every operand of `e` is, up to `≅`, a piece of `g`: transport it along
  -- `f ≅ unionOf zs` with `pieces_equiv`, split the union with `pieces_unionOf`, then
  -- collapse the nesting with `pieces_trans`.
  have sub : as ⊆[ (· ≅ ·) ] pieces g := fun x hx =>
    have ⟨i1, i1_mem, x_i1⟩ := (pieces_equiv f_gg).1 _ (as_sub hx)
    have ⟨gi, gi_mem, i1_piece⟩ := pieces_unionOf ne_zs i1_mem
    have ⟨j1, j1_mem, i1_j1⟩ := pieces_trans i1_piece (zs_sub gi_mem)
    ⟨j1, j1_mem, trans x_i1 i1_j1⟩
  -- so `unionOf as` is similar to a union of distinct pieces of `g`, which is in `⊕(pieces g)`
  obtain ⟨y, y_mem, sum_y⟩ := subset_sim_perm ne_as sub
  exact ⟨y, y_mem, trans e_ff sum_y⟩

end EreqAtomic
