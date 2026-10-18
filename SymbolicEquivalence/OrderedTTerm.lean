import SymbolicEquivalence.TransitionTerm

/-!
# Ordered transition terms

A `TTerm` is ordered when its conditions strictly decrease along every path, as in a
binary decision diagram. Two ordered terms can be combined by walking down both at once with
`apply`, and the result is again ordered.

`apply` computes the same function as `liftBinary` on any terms. Ordering only keeps the
result small, since each condition is tested once instead of copying `g` under every leaf
of `f`.
-/

namespace TTerm

variable {κ : Type _} [LinearOrder κ]

/-- Every condition tested in `t` is strictly below `bnd`. -/
inductive Below : TTerm κ β → κ → Prop where
  | base {a : β} {bnd : κ} : Below (leaf a) bnd
  | ind {c bnd : κ} {left right : TTerm κ β} :
      c < bnd → Below left bnd → Below right bnd → Below (node c left right) bnd

/-- Conditions strictly decrease along every path. -/
inductive Ordered : TTerm κ β → Prop where
  | base {a : β} : Ordered (leaf a)
  | ind {c : κ} {left right : TTerm κ β} :
      Ordered left → Ordered right → Below left c → Below right c →
      Ordered (node c left right)

theorem Below.mono {t : TTerm κ β} {b b' : κ} (h : b ≤ b') : Below t b → Below t b'
  | .base => .base
  | .ind hc hl hr => .ind (hc.trans_le h) (hl.mono h) (hr.mono h)

theorem Below.map (op : β → γ) {t : TTerm κ β} {b : κ} : Below t b → Below (op <$> t) b
  | .base => .base
  | .ind hc hl hr => .ind hc (hl.map op) (hr.map op)

theorem Ordered.map (op : β → γ) {t : TTerm κ β} : Ordered t → Ordered (op <$> t)
  | .base => .base
  | .ind hl hr bl br => .ind (hl.map op) (hr.map op) (bl.map op) (br.map op)

/-! ### `apply` -/

/-- Combine two terms pointwise, descending both at once and always splitting on the
    larger root condition. -/
def apply (op : β → γ → δ) : TTerm κ β → TTerm κ γ → TTerm κ δ
  | leaf b, leaf c => leaf (op b c)
  | leaf b, node cond g₁ g₀ => node cond (apply op (leaf b) g₁) (apply op (leaf b) g₀)
  | node cond f₁ f₀, leaf c => node cond (apply op f₁ (leaf c)) (apply op f₀ (leaf c))
  | node condf f₁ f₀, node condg g₁ g₀ =>
    if condf = condg then
      node condf (apply op f₁ g₁) (apply op f₀ g₀)
    else if condg < condf then
      node condf (apply op f₁ (node condg g₁ g₀)) (apply op f₀ (node condg g₁ g₀))
    else
      node condg (apply op (node condf f₁ f₀) g₁) (apply op (node condf f₁ f₀) g₀)
termination_by f g => (f, g)

@[simp] theorem apply_leaf_leaf (op : β → γ → δ) (b : β) (c : γ) :
    apply (κ := κ) op (leaf b) (leaf c) = leaf (op b c) := by
  rw [apply]

@[simp] theorem apply_leaf_node (op : β → γ → δ) (b : β) (cond : κ) (g₁ g₀ : TTerm κ γ) :
    apply op (leaf b) (node cond g₁ g₀) =
      node cond (apply op (leaf b) g₁) (apply op (leaf b) g₀) := by
  rw [apply]

@[simp] theorem apply_node_leaf (op : β → γ → δ) (c : γ) (cond : κ) (f₁ f₀ : TTerm κ β) :
    apply op (node cond f₁ f₀) (leaf c) =
      node cond (apply op f₁ (leaf c)) (apply op f₀ (leaf c)) := by
  rw [apply]

/-- Not `simp`: it exposes a nested `if` that `simp` would split everywhere. -/
theorem apply_node_node (op : β → γ → δ)
    (condf condg : κ) (f₁ f₀ : TTerm κ β) (g₁ g₀ : TTerm κ γ) :
    apply op (node condf f₁ f₀) (node condg g₁ g₀) =
      if condf = condg then
        node condf (apply op f₁ g₁) (apply op f₀ g₀)
      else if condg < condf then
        node condf (apply op f₁ (node condg g₁ g₀)) (apply op f₀ (node condg g₁ g₀))
      else
        node condg (apply op (node condf f₁ f₀) g₁) (apply op (node condf f₁ f₀) g₀) := by
  rw [apply]

/-- Every leaf of `apply op f g` is `op` of a leaf of `f` and a leaf of `g`. The
    converse fails: only consistent combinations are built. -/
theorem mem_leaves_apply (op : β → γ → δ) {e : δ} :
    ∀ (f : TTerm κ β) (g : TTerm κ γ), e ∈ leaves (apply op f g) →
      ∃ x ∈ leaves f, ∃ y ∈ leaves g, e = op x y
  | leaf _, leaf _ => by simp +contextual [eq_comm]
  | leaf b, node _ g₁ g₀ => by
    have := mem_leaves_apply (e := e) op (leaf b) g₁
    have := mem_leaves_apply (e := e) op (leaf b) g₀
    simp only [apply_leaf_node, leaves_node, List.mem_append]
    aesop
  | node _ f₁ f₀, leaf c => by
    have := mem_leaves_apply (e := e) op f₁ (leaf c)
    have := mem_leaves_apply (e := e) op f₀ (leaf c)
    simp only [apply_node_leaf, leaves_node, List.mem_append]
    aesop
  | node condf f₁ f₀, node condg g₁ g₀ => by
    have := mem_leaves_apply (e := e) op f₁ g₁
    have := mem_leaves_apply (e := e) op f₀ g₀
    have := mem_leaves_apply (e := e) op f₁ (node condg g₁ g₀)
    have := mem_leaves_apply (e := e) op f₀ (node condg g₁ g₀)
    have := mem_leaves_apply (e := e) op (node condf f₁ f₀) g₁
    have := mem_leaves_apply (e := e) op (node condf f₁ f₀) g₀
    rw [apply_node_node]
    split_ifs <;> simp only [leaves_node, List.mem_append] <;> aesop
termination_by f g => (f, g)

theorem Below.apply (op : β → γ → δ) {b : κ} :
    ∀ {f : TTerm κ β} {g : TTerm κ γ}, Below f b → Below g b → Below (apply op f g) b
  | leaf _, leaf _, _, _ => by simpa using Below.base
  | leaf _, node _ _ _, hf, .ind hc hl hr => by
    simpa using Below.ind hc (hf.apply op hl) (hf.apply op hr)
  | node _ _ _, leaf _, .ind hc hl hr, hg => by
    simpa using Below.ind hc (hl.apply op hg) (hr.apply op hg)
  | node _ _ _, node _ _ _, .ind hcf hlf hrf, .ind hcg hlg hrg => by
    rw [apply_node_node]
    split_ifs
    · exact .ind hcf (hlf.apply op hlg) (hrf.apply op hrg)
    · exact .ind hcf (hlf.apply op (.ind hcg hlg hrg)) (hrf.apply op (.ind hcg hlg hrg))
    · exact .ind hcg ((Below.ind hcf hlf hrf).apply op hlg)
        ((Below.ind hcf hlf hrf).apply op hrg)
termination_by f g => (f, g)

theorem Ordered.apply (op : β → γ → δ) :
    ∀ {f : TTerm κ β} {g : TTerm κ γ}, Ordered f → Ordered g → Ordered (apply op f g)
  | leaf _, leaf _, _, _ => by simpa using Ordered.base
  | leaf _, node _ _ _, hf, .ind hl hr bl br => by
    simpa using Ordered.ind (hf.apply op hl) (hf.apply op hr)
      (Below.base.apply op bl) (Below.base.apply op br)
  | node _ _ _, leaf _, .ind hl hr bl br, hg => by
    simpa using Ordered.ind (hl.apply op hg) (hr.apply op hg)
      (bl.apply op .base) (br.apply op .base)
  | node condf f₁ f₀, node condg g₁ g₀, .ind hlf hrf blf brf, .ind hlg hrg blg brg => by
    rw [apply_node_node]
    split_ifs with h1 h2
    · subst h1
      exact .ind (hlf.apply op hlg) (hrf.apply op hrg) (blf.apply op blg) (brf.apply op brg)
    · -- `g` moves under `condf`, so it must be shown `Below condf`
      have hg' : Ordered (node condg g₁ g₀) := .ind hlg hrg blg brg
      have bg' : Below (node condg g₁ g₀) condf := .ind h2 (blg.mono h2.le) (brg.mono h2.le)
      exact .ind (hlf.apply op hg') (hrf.apply op hg') (blf.apply op bg') (brf.apply op bg')
    · -- symmetrically, `f` moves under `condg`
      have hlt : condf < condg := lt_of_le_of_ne (not_lt.mp h2) h1
      have hf' : Ordered (node condf f₁ f₀) := .ind hlf hrf blf brf
      have bf' : Below (node condf f₁ f₀) condg := .ind hlt (blf.mono hlt.le) (brf.mono hlt.le)
      exact .ind (hf'.apply op hlg) (hf'.apply op hrg) (bf'.apply op blg) (bf'.apply op brg)
termination_by f g => (f, g)

/-- `apply` denotes the pointwise combination, for any terms, ordered or not. -/
theorem eval_apply [Models κ σ] (op : β → γ → δ) (x : σ) :
    ∀ (f : TTerm κ β) (g : TTerm κ γ), (apply op f g)[x] = op (f[x]) (g[x])
  | leaf _, leaf _ => by simp
  | leaf b, node cond g₁ g₀ => by
    simp only [apply_leaf_node, eval_node, eval_leaf]
    split_ifs
    · exact eval_apply op x (leaf b) g₁
    · exact eval_apply op x (leaf b) g₀
  | node cond f₁ f₀, leaf c => by
    simp only [apply_node_leaf, eval_node, eval_leaf]
    split_ifs
    · exact eval_apply op x f₁ (leaf c)
    · exact eval_apply op x f₀ (leaf c)
  | node condf f₁ f₀, node condg g₁ g₀ => by
    rw [apply_node_node]
    split_ifs with h1 h2
    · subst h1
      simp only [eval_node]
      split_ifs
      · exact eval_apply op x f₁ g₁
      · exact eval_apply op x f₀ g₀
    · simp only [eval_node]
      by_cases hf : models condf x
      · simp only [hf, ite_true]
        rw [eval_apply op x f₁ (node condg g₁ g₀)]; simp only [eval_node]
      · simp only [hf, ite_false, Bool.false_eq_true]
        rw [eval_apply op x f₀ (node condg g₁ g₀)]; simp only [eval_node]
    · simp only [eval_node]
      by_cases hg : models condg x
      · simp only [hg, ite_true]
        rw [eval_apply op x (node condf f₁ f₀) g₁]; simp only [eval_node]
      · simp only [hg, ite_false, Bool.false_eq_true]
        rw [eval_apply op x (node condf f₁ f₀) g₀]; simp only [eval_node]
termination_by f g => (f, g)

end TTerm
