import SymbolicEquivalence.Ereq.ExtendedEBA
import SymbolicEquivalence.VectorHelpers

/-!
# Words over extended alphabets

Words over `σ × {0,1}^n`, where each position carries one bit per variable. `extend` adds a
bit to every position, `project` erases the last one and `extract` reads it off.
-/

variable {σ : Type*}

namespace Word

/-- Append one bit to each position: `[(a,[0]),(b,[1])]` and `[1,0]` give
    `[(a,[0,1]),(b,[1,0])]`. The bit goes last (`snoc`) because `∃ʳ` binds the last
    variable, so the existing variable indices are unchanged. -/
def extend : (w : Word σ n) → List.Vector Bool w.length → Word σ (n + 1)
  | [], _ => []
  | (a, v) :: w', ⟨b :: bs, h⟩ =>
    (a, v.snoc b) :: extend w' ⟨bs, Nat.add_right_cancel h⟩

/-- Erase the last bit of each position. -/
def project (w : Word σ (n + 1)) : Word σ n :=
  w.map (fun ⟨a, v⟩ => (a, v.eraseIdx (Fin.last n)))

/-- Extract the last bit of each position. -/
def extract (w : Word σ (n + 1)) : List Bool :=
  w.map (fun ⟨_, v⟩ => v.last)

/-! ### `extend`, `project` and `extract` -/

@[simp]
theorem extend_nil {s : List.Vector Bool ([] : Word σ n).length} : extend [] s = [] := rfl

@[simp]
theorem extend_cons {a : σ} {v : List.Vector Bool n} {w' : Word σ n}
    {b : Bool} {bs : List Bool} {h : (b :: bs).length = ((a, v) :: w').length} :
    extend ((a, v) :: w') ⟨b :: bs, h⟩
      = (a, v.snoc b) :: extend w' ⟨bs, Nat.add_right_cancel h⟩ := rfl

@[simp]
theorem project_cons {a : σ} {v : List.Vector Bool (n + 1)} {w : Word σ (n + 1)} :
    project ((a, v) :: w) = (a, v.eraseIdx (Fin.last n)) :: project w := rfl

@[simp]
theorem length_project (w : Word σ (n + 1)) : (project w).length = w.length := by
  simp [project]

theorem extract_length_project (w : Word σ (n + 1)) :
    (extract w).length = (project w).length := by
  simp [extract]

/-- `project` is a left inverse of `extend`. -/
theorem project_extend (w : Word σ n) (s : List.Vector Bool w.length) :
    project (extend w s) = w := by
  match w, s with
  | [], _ => rfl
  | (x, v) :: xs, ⟨b :: bs, h⟩ =>
    simp [List.Vector.eraseIdx_last_snoc, project_extend xs ⟨bs, Nat.add_right_cancel h⟩]

@[simp]
theorem length_extend (w : Word σ n) (s : List.Vector Bool w.length) :
    (extend w s).length = w.length := by
  match w, s with
  | [], _ => rfl
  | (x, v) :: xs, ⟨b :: bs, h⟩ => simp [length_extend xs ⟨bs, Nat.add_right_cancel h⟩]

/-- `extend` with the extracted bits is a left inverse of `project`. -/
theorem extend_project (w : Word σ (n + 1)) :
    extend (project w) ⟨extract w, extract_length_project w⟩ = w := by
  match w with
  | [] => rfl
  | (x, v) :: xs =>
    change (x, (v.eraseIdx (Fin.last n)).snoc v.last)
        :: extend (project xs) ⟨extract xs, extract_length_project xs⟩ = (x, v) :: xs
    rw [List.Vector.snoc_eraseIdx_last, extend_project xs]

theorem extend_append (v1 v2 : Word σ n) (s1 : List.Vector Bool v1.length)
    (s2 : List.Vector Bool v2.length) :
    extend (v1 ++ v2) (List.Vector.congr (Eq.symm List.length_append) (s1 ++ s2))
      = extend v1 s1 ++ extend v2 s2 := by
  match v1, s1, s2 with
  | [], ⟨[], _⟩, _ => rfl
  | (a, v) :: w', ⟨b :: bs, h⟩, ⟨l2, h2⟩ =>
    exact congrArg ((a, v.snoc b) :: ·)
      (extend_append w' v2 ⟨bs, Nat.add_right_cancel h⟩ ⟨l2, h2⟩)

end Word
