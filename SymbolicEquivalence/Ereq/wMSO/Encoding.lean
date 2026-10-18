import SymbolicEquivalence.Ereq.wMSO.Formula
import SymbolicEquivalence.Ereq.Word

/-!
# Encoding a word and an assignment

A wMSO formula is checked against a word `xs` together with an assignment `θ` of its set
variables. An `Ereq` is matched against a single word in which every letter carries one bit
per variable. This file defines `「xs, θ」`, which combines `xs` and `θ` into such a word, and
proves lemmas for recovering `xs` and `θ` from it.
-/

variable {σ : Type*}

/-- Pair each letter of `xs` with the bits that `θ` gives its position. For example, with
    `xs = "bbacbc"` and `θ` giving the sets `{2}` and `{0,1,4}`, the result is
    `[(b,[0,1]), (b,[0,1]), (a,[1,0]), (c,[0,0]), (b,[0,1]), (c,[0,0])]`. -/
def List.toWord (xs : List σ) (θ : Assignment xs.length n) : Word σ n :=
  match xs with
  | [] => []
  | x :: xs =>
    let bitsAtX := List.Vector.ofFn (fun i => (θ i).head)
    let tailAssign := fun i => (θ i).tail
    (x, bitsAtX) :: xs.toWord tailAssign

notation "「" xs ", " θ "」" => List.toWord xs θ

@[simp]
theorem List.toWord_length {xs : List σ} (θ : Assignment xs.length n) :
    (List.toWord xs θ).length = xs.length :=
  match xs with
  | [] => by simp only [List.toWord, List.length_nil]
  | _ :: _ => Nat.succ_inj.mpr (List.toWord_length (θ := fun j => (θ j).tail))

/-- We can view a vector of length `xs.length` as one of length `「xs, θ」.length`. -/
abbrev List.toWordBits {xs : List σ} (θ : Assignment xs.length n) (v : List.Vector Bool xs.length) :
    List.Vector Bool (「xs, θ」.length) :=
  List.Vector.congr (List.toWord_length θ).symm v

/-- Extending the assignment by `v` extends the encoded word by the bits of `v`. -/
theorem List.extend_toWord {xs : List σ} {θ : Assignment xs.length n}
    {v : List.Vector Bool (xs.length)} :
    「xs, (extAssignment θ v)」 = Word.extend 「xs, θ」 (toWordBits θ v) := by
  match xs, v with
  | [], _ => rfl
  | x :: xs, ⟨v :: vs, h⟩ =>
    have h' : vs.length = xs.length := Nat.succ_inj.mp h
    have ih := extend_toWord (xs := xs) (θ := fun j => (θ j).tail) (v := ⟨vs, h'⟩)
    simp only [toWordBits, List.Vector.congr] at ih
    simp only [toWordBits, List.Vector.congr, List.toWord, Word.extend, List.cons.injEq,
      Prod.mk.injEq, true_and]
    refine ⟨?_, (congrArg _ (Fin.comp_snoc List.Vector.tail θ _)).trans ih⟩
    rw [← List.Vector.ofFn_snoc]
    exact congrArg _ (Fin.comp_snoc List.Vector.head θ _)

/-- The bit of variable `m` at position `k` of the encoded word is `(θ m)[k]`. -/
theorem List.toWord_getElem_bit {xs : List σ} {m : Fin n} :
    ∀ (θ : Assignment xs.length n) (k : Nat) (hk : k < xs.length)
      (hk' : k < (xs.toWord θ).length), (θ m)[k] = ((xs.toWord θ)[k]'hk').2[m] := by
  match xs with
  | [] => intro θ k hk; simp at hk
  | x :: xs' =>
    intro θ k hk hk'
    match k with
    | 0 =>
      simp only [List.toWord, List.getElem_cons_zero, List.Vector.getElem_ofFn]
      exact (List.Vector.get_zero (θ m)).symm ▸ rfl
    | k + 1 =>
      have ih := toWord_getElem_bit (xs := xs') (m := m) (fun j => (θ j).tail) k
        (by simpa using hk) (by simpa using hk')
      simpa [List.toWord, List.Vector.getElem_def, List.Vector.toList_tail] using ih

/-- Splitting a word into its letters and its bits, then encoding them again, gives back the
    word. -/
theorem List.toWord_transpose (w : Word σ n) : 「w.map Prod.fst, Word.transpose w」 = w := by
  induction w with
  | nil => rfl
  | cons a w' ih =>
    obtain ⟨x, v⟩ := a
    change (x, List.Vector.ofFn (fun i => v.get i)) :: 「w'.map Prod.fst, Word.transpose w'」
      = (x, v) :: w'
    rw [ih, List.Vector.ofFn_get]
