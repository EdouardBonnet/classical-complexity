import Lax434930Proofs.SpaceSemantics

/-! Two finite stacks represent the unchanged read-only input and its endmarkers. -/

namespace Lax434930Proofs.InputTapeView

open Lax434930.PolynomialTime Lax434930.SpaceMachines

structure View where
  left : Word
  current : InputSymbol
  right : Word

def View.word (v : View) : Word :=
  v.left.reverse ++ (match v.current with | .bit b => [b] | _ => []) ++ v.right

def View.position (v : View) : ℕ :=
  match v.current with | .leftEnd => 0 | _ => v.left.length + 1

def View.Valid (v : View) : Prop :=
  (v.current = .leftEnd → v.left = []) ∧ (v.current = .rightEnd → v.right = [])

def initial (w : Word) : View := ⟨[], .leftEnd, w⟩

def move (d : Move) (v : View) : View :=
  match d, v.current with
  | .stay, _ => v
  | .left, .leftEnd => v
  | .right, .rightEnd => v
  | .right, .leftEnd =>
    ⟨[], v.right.head?.elim .rightEnd .bit, v.right.tail⟩
  | .right, .bit b =>
    ⟨b :: v.left, v.right.head?.elim .rightEnd .bit, v.right.tail⟩
  | .left, .rightEnd =>
    ⟨v.left.tail, v.left.head?.elim .leftEnd .bit, []⟩
  | .left, .bit b =>
    ⟨v.left.tail, v.left.head?.elim .leftEnd .bit, b :: v.right⟩

lemma initial_valid (w : Word) : (initial w).Valid := by simp [initial, View.Valid]

@[simp] lemma initial_word (w : Word) : (initial w).word = w := by simp [initial, View.word]

@[simp] lemma initial_position (w : Word) : (initial w).position = 0 := rfl

lemma position_le (v : View) (hv : v.Valid) : v.position ≤ v.word.length + 1 := by
  cases v with
  | mk left current right =>
    cases current <;> simp_all [View.Valid, View.position, View.word]

lemma read_current (v : View) (hv : v.Valid) : readInput v.word v.position = v.current := by
  cases v with
  | mk left current right =>
    cases current with
    | leftEnd => rfl
    | bit b => simp [View.word, View.position, readInput, List.getElem?_append]
    | rightEnd => simp_all [View.Valid, View.word, View.position, readInput]

lemma move_valid (d : Move) (v : View) (hv : v.Valid) : (move d v).Valid := by
  cases v with
  | mk left current right =>
    cases d <;> cases current <;> cases left <;> cases right <;>
      simp_all [move, View.Valid]

lemma move_word (d : Move) (v : View) (hv : v.Valid) : (move d v).word = v.word := by
  cases v with
  | mk left current right =>
    cases d <;> cases current <;> cases left <;> cases right <;>
      simp_all [move, View.Valid, View.word, List.reverse_cons, List.append_assoc]

lemma move_position (d : Move) (v : View) (hv : v.Valid) :
    (move d v).position = min (d.apply v.position) (v.word.length + 1) := by
  cases v with
  | mk left current right =>
    cases d <;> cases current <;> cases left <;> cases right <;>
      simp_all [move, View.Valid, View.word, View.position, Move.apply] <;> omega

end Lax434930Proofs.InputTapeView
