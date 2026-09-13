import Lax434930Proofs.SpaceSemantics

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.WorkTapeView

open Lax434930.PolynomialTime Lax434930.SpaceMachines

structure View (M : Machine) where
  state : M.Q
  inputHead : ℕ
  left : List M.Γ
  current : M.Γ
  right : List M.Γ

def contents (M : Machine) (xs : List M.Γ) (i : ℕ) : M.Γ := (xs[i]?).getD M.blank

def View.word {M : Machine} (v : View M) : List M.Γ := v.left.reverse ++ v.current :: v.right

def View.expand {M : Machine} (v : View M) : M.Config :=
  ⟨v.state, v.inputHead, v.left.length, contents M v.word⟩

def View.cells {M : Machine} (v : View M) : ℕ := v.left.length + 1 + v.right.length

def initial (M : Machine) : View M := ⟨M.start, 0, [], M.blank, []⟩

def apply (M : Machine) (w : Word) (v : View M) (a : Action M.Γ M.Q) : View M :=
  let v' : View M :=
    { v with
      state := a.state
      inputHead := min (a.inputMove.apply v.inputHead) (w.length + 1)
      current := a.write }
  match a.workMove with
  | .stay => v'
  | .left => match v.left with
      | [] => v'
      | g :: xs => {v' with left := xs, current := g, right := a.write :: v.right}
  | .right =>
      { v' with
        left := a.write :: v.left
        current := v.right.headD M.blank
        right := v.right.tail }

lemma contents_append_blank (M : Machine) (xs : List M.Γ) :
    contents M (xs ++ [M.blank]) = contents M xs := by
  funext i
  by_cases hi : i < xs.length
  · simp [contents, List.getElem?_append, hi]
  · have hn : xs[i]? = none := List.getElem?_eq_none (by omega)
    simp [contents, List.getElem?_append, hi, List.getElem?_cons]
    split <;> rfl

lemma contents_write (M : Machine) (left right : List M.Γ) (old value : M.Γ) :
    contents M (left.reverse ++ value :: right) =
      Function.update (contents M (left.reverse ++ old :: right)) left.length value := by
  funext i
  by_cases he : i = left.length
  · subst i
    simp [contents]
  · by_cases hi : i < left.length
    · simp [contents, List.getElem?_append, Function.update_of_ne he, hi]
    · have hs : i - left.length ≠ 0 := by omega
      simp [contents, List.getElem?_append, Function.update_of_ne he, hi, List.getElem?_cons, hs]

lemma current_scanned (M : Machine) (v : View M) : v.expand.tape v.expand.workHead = v.current := by
  simp [View.expand, View.word, contents]

lemma initial_expand (M : Machine) : (initial M).expand = M.initial := by
  simp only [initial, View.expand, View.word, List.reverse_nil, List.nil_append,
    List.length_nil, Machine.initial]
  congr 1
  funext i
  cases i <;> simp [contents]

lemma apply_expand (M : Machine) (w : Word) (v : View M) (a : Action M.Γ M.Q) :
    (apply M w v a).expand = M.execute w v.expand a := by
  cases v with
  | mk state inputHead left current right =>
    cases a with
    | mk next value inputMove workMove =>
      cases workMove with
      | stay =>
        simp only [apply, View.expand, View.word, Machine.execute, Move.apply]
        congr 1
        exact contents_write M left right current value
      | left =>
        cases left with
        | nil =>
          simp only [apply, View.expand, View.word, Machine.execute, Move.apply,
            List.length_nil, Nat.zero_sub]
          congr 1
          exact contents_write M [] right current value
        | cons g xs =>
          simp only [apply, View.expand, View.word, Machine.execute, Move.apply,
            List.length_cons, Nat.add_sub_cancel, List.reverse_cons, List.append_assoc,
            List.singleton_append]
          congr 1
          simpa [List.reverse_cons, List.append_assoc] using contents_write M (g :: xs) right current value
      | right =>
        cases right with
        | nil =>
          simp only [apply, View.expand, View.word, Machine.execute, Move.apply,
            List.headD_nil, List.tail_nil, List.length_cons, List.reverse_cons, List.append_assoc]
          congr 1
          rw [← List.append_assoc, contents_append_blank]
          simpa using contents_write M left [] current value
        | cons g xs =>
          simp only [apply, View.expand, View.word, Machine.execute, Move.apply,
            List.headD_cons, List.tail_cons, List.length_cons, List.reverse_cons,
            List.append_assoc, List.singleton_append]
          congr 1
          exact contents_write M left (g :: xs) current value

lemma cells_preserved (M : Machine) (w : Word) (v : View M) (a : Action M.Γ M.Q) (s : ℕ)
    (hv : v.cells ≤ s) (hh : (apply M w v a).left.length < s) :
    (apply M w v a).cells ≤ s := by
  cases v with
  | mk state inputHead left current right =>
    cases a with
    | mk next value inputMove workMove =>
      cases workMove with
      | stay => exact hv
      | left => cases left <;> simp_all [apply, View.cells] <;> omega
      | right => cases right <;> simp_all [apply, View.cells] <;> omega

lemma cells_eq (M : Machine) (w : Word) (v : View M) (a : Action M.Γ M.Q)
    (hh : (apply M w v a).left.length < v.cells) :
    (apply M w v a).cells = v.cells := by
  cases v with
  | mk state inputHead left current right =>
    cases a with
    | mk next value inputMove workMove =>
      cases workMove with
      | stay => rfl
      | left => cases left <;> simp [apply, View.cells] <;> omega
      | right => cases right <;> simp_all [apply, View.cells] <;> omega

lemma contents_replicate_blank (M : Machine) (n : ℕ) :
    contents M (List.replicate n M.blank) = fun _ => M.blank := by
  funext i
  by_cases hi : i < n <;> simp [contents, List.getElem?_replicate, hi]

def padded (M : Machine) (t : ℕ) : View M := ⟨M.start, 0, [], M.blank, List.replicate t M.blank⟩

lemma padded_expand (M : Machine) (t : ℕ) : (padded M t).expand = M.initial := by
  simp only [padded, View.expand, View.word, List.reverse_nil, List.nil_append, List.length_nil,
    ← List.replicate_succ, contents_replicate_blank, Machine.initial]

@[simp] lemma padded_cells (M : Machine) (t : ℕ) : (padded M t).cells = t + 1 := by
  simp [padded, View.cells]
  omega

end Lax434930Proofs.WorkTapeView
