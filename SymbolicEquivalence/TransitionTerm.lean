import SymbolicEquivalence.EffectiveBooleanAlgebra

/-!
# Transition terms

A transition term `TTerm α β` is a binary decision tree whose internal nodes test
predicates `α` and whose leaves carry values `β`.  Evaluating it on a character `x` follows
the branches `x` selects: the left one where `x` satisfies the node's predicate, the right
one otherwise.

* `TTerm α` is a lawful monad (`t >>= f` grafts the tree `f b` in place of every leaf `b`);
  `liftUnary` and `liftBinary` lift operations on leaves to trees.
* `leaves`, `evaluation` (`f[x]`): the leaf list and the evaluation of a tree on a character.
* `restrict`: pruning.  Given a guard `ψ`, it drops every branch that no character
  satisfying `ψ` reaches, using a satisfiability oracle (`DecidableSat`).
* `reachableLeaves`: the leaves that some character satisfying a guard `ψ` reaches
   (with `ψ = ⊤`, the leaves some character reaches).
-/

/-- Transition terms, where `α` is the type of alphabet predicates and `β` the type of leaves. -/
inductive TTerm (α β : Type _) : Type _ where
  | leaf : β → TTerm α β
  | node (cond : α) (t e : TTerm α β) : TTerm α β
  deriving Repr, DecidableEq

namespace TTerm

/-! ### The monad -/

def bind : TTerm α β → (β → TTerm α γ) → TTerm α γ
  | leaf b, f => f b
  | node p l r, f => node p (l.bind f) (r.bind f)

instance : Monad (TTerm α) where
  pure := leaf
  bind := bind

private theorem bind_assoc (x : TTerm α β) (f : β → TTerm α γ) (g : γ → TTerm α δ) :
    x >>= f >>= g = x >>= fun a => f a >>= g := by
  induction x with
  | leaf b => rfl
  | node p l r ihl ihr => exact congrArg₂ (node p) ihl ihr

private theorem id_map (t : TTerm α β) : id <$> t = t := by
  induction t with
  | leaf b => rfl
  | node p l r ihl ihr => exact congrArg₂ (node p) ihl ihr

instance : LawfulMonad (TTerm α) := LawfulMonad.mk'
  (id_map := id_map)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc)

@[simp] theorem bind_leaf (f : β → TTerm α γ) (b : β) : (leaf b : TTerm α β) >>= f = f b := rfl

@[simp] theorem bind_node (f : β → TTerm α γ) (p l r) :
    node p l r >>= f = node p (l >>= f) (r >>= f) := rfl

@[simp] theorem map_leaf (op : β → γ) (b : β) : op <$> (leaf b : TTerm α β) = leaf (op b) := rfl

@[simp] theorem map_node (op : β → γ) (p : α) (l r : TTerm α β) :
    op <$> node p l r = node p (op <$> l) (op <$> r) := rfl

abbrev liftUnary (op : β → γ) (g : TTerm α β) : TTerm α γ := op <$> g

/-- Graft `op x <$> r` under every leaf `x` of `l`. -/
abbrev liftBinary (op : β → γ → δ) (l : TTerm α β) (r : TTerm α γ) : TTerm α δ :=
  l >>= fun x => liftUnary (op x) r

private theorem map_eq_bind (op : β → γ) (t : TTerm α β) :
    liftUnary op t = t >>= (leaf ∘ op) := rfl

/-! ### Leaves -/

def leaves : TTerm α β → List β
  | leaf r => [r]
  | node _ f g => leaves f ++ leaves g

@[simp] theorem leaves_leaf (b : β) : leaves (leaf b : TTerm α β) = [b] := rfl

@[simp] theorem leaves_node (p : α) (f g : TTerm α β) :
    leaves (node p f g) = leaves f ++ leaves g := rfl

/-- Every transition term has a leaf. So `leaves (restrict f ⊥)` is a singleton, not `[]`,
    which is why `reachableLeaves` first checks `Satisfiable ψ`. -/
theorem leaves_ne_nil (f : TTerm α β) : leaves f ≠ [] := by
  induction f with
  | leaf b => simp
  | node p l r ihl _ => simp [ihl]

/-- The leaves of `t >>= f` are the leaves of `f b` for each leaf `b` of `t`, in order. -/
@[simp] theorem leaves_bind (f : β → TTerm α γ) (t : TTerm α β) :
    leaves (t >>= f) = (leaves t).flatMap (leaves ∘ f) := by
  induction t with
  | leaf b => simp
  | node _ l r ihl ihr => simp [ihl, ihr]

@[simp] theorem leaves_map (op : β → γ) (g : TTerm α β) :
    leaves (liftUnary op g) = (leaves g).map op := by
  simp only [map_eq_bind, leaves_bind, List.map_eq_flatMap]
  rfl

/-! ### Pairwise products -/

/-- Every `op x y` with `x` drawn from `xs` and `y` from `ys`, in order. -/
abbrev productWith (op : β → γ → δ) (xs : List β) (ys : List γ) : List δ :=
  op <$> xs <*> ys

theorem mem_productWith {op : β → γ → δ} {xs : List β} {ys : List γ} {e : δ} :
    e ∈ productWith op xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, e = op x y := by
  simp only [productWith, Seq.seq, Functor.map, List.mem_flatMap, List.mem_map]
  aesop

theorem leaves_binary (op : β → γ → δ) (f : TTerm α β) (g : TTerm α γ) :
    leaves (liftBinary op f g) = productWith op (leaves f) (leaves g) := by
  rw [leaves_bind]
  change (leaves f).flatMap (fun x => leaves (liftUnary (op x) g)) = _
  simp only [leaves_map, productWith, Seq.seq]
  exact (List.flatMap_map op (fun y => List.map y (leaves g)) (leaves f)).symm

/-! ### Evaluation -/

section Eval
variable [Models α σ]

def evaluation (x : σ) : TTerm α β → β
  | leaf r => r
  | node p f₁ f₂ => if models p x then evaluation x f₁ else evaluation x f₂

/-- `f[x]` is the evaluation of `f` at `x`. -/
instance : GetElem (TTerm α β) σ β (fun _ _ => True) where
  getElem f x _ := evaluation x f

@[simp] theorem eval_leaf (x : σ) (b : β) : (leaf b : TTerm α β)[x] = b := rfl

@[simp] theorem eval_node (x : σ) (p : α) (f g : TTerm α β) :
    (node p f g)[x] = if models p x then f[x] else g[x] := rfl

/-- Evaluating `t >>= f` at `x` evaluates `t` at `x`, then the tree `f (t[x])` at the same
    `x`. -/
@[simp] theorem eval_bind (f : β → TTerm α γ) (t : TTerm α β) (x : σ) :
    (t >>= f)[x] = (f (t[x]))[x] := by
  induction t with
  | leaf b => rfl
  | node p l r ihl ihr =>
    simp only [bind_node, eval_node]
    split_ifs <;> assumption

@[simp] theorem eval_liftUnary (op : β → γ) (f : TTerm α β) (x : σ) :
    (liftUnary op f)[x] = op (f[x]) := by
  simp [map_eq_bind, Function.comp]

theorem eval_liftBinary (op : β → γ → δ) (f : TTerm α β) (g : TTerm α γ) (x : σ) :
    (liftBinary op f g)[x] = op (f[x]) (g[x]) := by
  simp only [liftBinary, eval_bind, eval_liftUnary]

/-- Every evaluation lands on a leaf. -/
theorem eval_mem_leaves (t : TTerm α β) (x : σ) : t[x] ∈ leaves t := by
  induction t with
  | leaf b => simp
  | node p l r ihl ihr =>
    simp only [eval_node, leaves_node, List.mem_append]
    split_ifs
    · exact .inl ihl
    · exact .inr ihr

end Eval

section NEBA
variable [EffectiveBooleanAlgebra α σ] [DecidableSat α]
open Models EffectiveBooleanAlgebra

/-! ### `restrict`: prune branches infeasible under a guard -/

def restrict : TTerm α β → α → TTerm α β
  | leaf b, _ => leaf b
  | node p f g, ψ =>
    if Satisfiable (ψ ⊓ p) then
      if Satisfiable (ψ ⊓ pᶜ) then
        node p (restrict f (ψ ⊓ p)) (restrict g (ψ ⊓ pᶜ))
      else restrict f (ψ ⊓ p)
    else restrict g (ψ ⊓ pᶜ)

/-- `restrict f ψ` only removes branches that no character satisfying `ψ` takes, so a
    character `x` satisfying `ψ` still reaches the same leaf. -/
theorem eval_restrict (f : TTerm α β) (ψ : α) (x : σ) (hx : x ⊨ ψ) :
    (f.restrict ψ)[x] = f[x] := by
  induction f generalizing ψ with
  | leaf r => rfl
  | node p l r ihl ihr =>
    simp only [restrict]
    split_ifs with h1 h2
    · rw [eval_node, eval_node]
      split_ifs with hp
      · exact ihl (ψ ⊓ p) (by simp [hx, hp])
      · exact ihr (ψ ⊓ pᶜ) (by simp [hx, hp])
    · -- `ψ ⊓ pᶜ` unsatisfiable: every model of `ψ` models `p`
      have hp : x ⊨ p = true := by
        simpa [hx] using models_eq_false_of_not_satisfiable h2 x
      rw [eval_node, ite_eq_left hp]
      exact ihl (ψ ⊓ p) (by simp [hx, hp])
    · -- `ψ ⊓ p` unsatisfiable: no model of `ψ` models `p`
      have hp : x ⊨ p = false := by
        simpa [hx] using models_eq_false_of_not_satisfiable h1 x
      simp only [eval_node, hp, Bool.false_eq_true]
      exact ihr (ψ ⊓ pᶜ) (by simp [hx, hp])

theorem leaves_restrict_subset (f : TTerm α β) (ψ : α) : leaves (f.restrict ψ) ⊆ leaves f := by
  induction f generalizing ψ with
  | leaf b => simp [restrict]
  | node p l r ihl ihr =>
    have hl ψ : leaves (l.restrict ψ) ⊆ leaves (node p l r) :=
      List.Subset.trans (ihl ψ) (List.subset_append_left _ _)
    have hr ψ : leaves (r.restrict ψ) ⊆ leaves (node p l r) :=
      List.Subset.trans (ihr ψ) (List.subset_append_right _ _)
    simp only [restrict]
    split_ifs
    · exact List.append_subset.2 ⟨hl _, hr _⟩
    · exact hl _
    · exact hr _

/-! ### `reachableLeaves`: leaves reachable under a guard -/

/-- The leaves of `f` reachable by characters satisfying `ψ`: the leaves of `f.restrict ψ`,
    or `[]` if `ψ` is unsatisfiable. -/
def reachableLeaves (f : TTerm α β) (ψ : α) : List β :=
  if Satisfiable ψ then leaves (f.restrict ψ) else []

theorem reachableLeaves_eq_leaves_restrict (f : TTerm α β) (ψ : α) (h : Satisfiable ψ) :
    reachableLeaves f ψ = leaves (f.restrict ψ) := ite_eq_left h

/-- Every leaf of `f.restrict ψ` is reached by some character satisfying `ψ`. -/
private theorem mem_leaves_restrict_of {f : TTerm α β} {ψ : α} {x : β}
    (hψ : Satisfiable ψ) (hx : x ∈ leaves (f.restrict ψ)) : ∃ c : σ, c ⊨ ψ ∧ f[c] = x := by
  induction f generalizing ψ with
  | leaf b =>
    obtain ⟨c, hc⟩ := hψ
    simp only [restrict, leaves_leaf, List.mem_singleton] at hx
    exact ⟨c, hc, hx.symm⟩
  | node p l r ihl ihr =>
    simp only [restrict] at hx
    split_ifs at hx with h1 h2
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨c, hc, rfl⟩ := ihl h1 hx; exact ⟨c, by simp_all⟩
      · obtain ⟨c, hc, rfl⟩ := ihr h2 hx; exact ⟨c, by simp_all⟩
    · obtain ⟨c, hc, rfl⟩ := ihl h1 hx; exact ⟨c, by simp_all⟩
    · -- `ψ ⊓ p` is unsatisfiable, so every model of `ψ` is a model of `ψ ⊓ pᶜ`
      have h2 : Satisfiable (ψ ⊓ pᶜ) := by
        obtain ⟨c, hc⟩ := hψ
        have := models_eq_false_of_not_satisfiable h1 c
        exact ⟨c, by simp_all⟩
      obtain ⟨c, hc, rfl⟩ := ihr h2 hx; exact ⟨c, by simp_all⟩

/-- If `ψ` is satisfiable, the leaves of `f.restrict ψ` are exactly those reached by
    characters satisfying `ψ`. -/
theorem mem_leaves_restrict_iff {f : TTerm α β} {ψ : α} (hψ : Satisfiable ψ) {x : β} :
    x ∈ leaves (f.restrict ψ) ↔ ∃ c : σ, c ⊨ ψ ∧ f[c] = x := by
  refine ⟨mem_leaves_restrict_of hψ, ?_⟩
  rintro ⟨c, hc, rfl⟩
  rw [← eval_restrict f ψ c hc]
  exact eval_mem_leaves _ _

theorem mem_reachableLeaves_iff {f : TTerm α β} {ψ : α} {x : β} :
    x ∈ reachableLeaves f ψ ↔ ∃ c : σ, c ⊨ ψ ∧ f[c] = x := by
  by_cases hψ : Satisfiable ψ
  · rw [reachableLeaves_eq_leaves_restrict f ψ hψ, mem_leaves_restrict_iff hψ]
  · rw [reachableLeaves, ite_eq_right hψ]
    simp only [List.not_mem_nil, false_iff]
    exact fun ⟨c, hc, _⟩ => hψ ⟨c, hc⟩

@[simp] theorem mem_reachableLeaves_top {f : TTerm α β} {x : β} :
    x ∈ reachableLeaves f ⊤ ↔ ∃ c : σ, f[c] = x := by
  simp [mem_reachableLeaves_iff]

end NEBA

end TTerm
