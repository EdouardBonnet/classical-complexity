import Lax434930Proofs.SavitchProofs.InputRoutines
import Lax434930Proofs.SavitchProofs.BinaryDecrement

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.InputRoutines

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Command Exec Good assigned moved)
open StackRoutines (Control Code Data)
open StackMacros
open scoped Classical

noncomputable section

variable {K Γ σ : Type} [Inhabited Γ]

def advance : Macro K Γ σ := Macro.seq (Macro.move (fun _ => .right)) Macro.sample

def keepGoing (s : Control Γ σ) : Bool := !s.flag && decide (s.input ≠ .rightEnd)

def visitFromCode (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (BinaryCounter.decrement src aux bit readBit).code
    (.loop keepGoing (.seq advance.code (BinaryCounter.decrement src aux bit readBit).code))

def visited (w : Word) (d : Data (K := K) (Γ := Γ) (σ := σ)) (src : K) (bit : Bool → Γ)
    (k n : ℕ) : Data (K := K) (Γ := Γ) (σ := σ) :=
  let hit := d.inputHead + n ≤ w.length + 1
  let pos := min (d.inputHead + n) (w.length + 1)
  ⟨{d.state with
      value := none
      flag := decide hit
      input := readInput w pos}, pos,
    Function.update d.store src
      ((BinaryCounter.word k (if hit then 2 ^ k - 1 else n - (w.length + 1 - d.inputHead) - 1)).map bit)⟩

def afterAdvance (w : Word) (d : Data (K := K) (Γ := Γ) (σ := σ)) (src : K) (bit : Bool → Γ)
    (k n : ℕ) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none, flag := false, input := readInput w (d.inputHead + 1)}, d.inputHead + 1,
    Function.update d.store src ((BinaryCounter.word k n).map bit)⟩

lemma visited_advance (w : Word) (d : Data (K := K) (Γ := Γ) (σ := σ)) (src : K) (bit : Bool → Γ)
    (k n : ℕ) (hh : d.inputHead < w.length + 1) :
    visited w (afterAdvance w d src bit k n) src bit k n = visited w d src bit k (n + 1) := by
  have hsum : d.inputHead + 1 + n = d.inputHead + (n + 1) := by omega
  have hrem : n - (w.length - d.inputHead) - 1 =
      n + 1 - (w.length + 1 - d.inputHead) - 1 := by omega
  simp [visited, afterAdvance, hsum, hrem]

lemma visitFrom_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (k n : ℕ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hn : n < 2 ^ k) (hd : Good w bound d) (hi : d.state.input = readInput w d.inputHead)
    (hsrc : d.store src = (BinaryCounter.word k n).map bit) (ha : d.store aux = []) :
    Exec w bound (visitFromCode src aux bit readBit) d (visited w d src bit k n) := by
  induction n generalizing d with
  | zero =>
    let de : Data (K := K) (Γ := Γ) (σ := σ) :=
      ⟨{d.state with value := none, flag := true}, d.inputHead,
        Function.update d.store src ((BinaryCounter.word k (2 ^ k - 1)).map bit)⟩
    have hr : Exec w bound (BinaryCounter.decrement src aux bit readBit).code d de := by
      simpa [de] using BinaryCounter.decrement_exec w bound src aux hne bit readBit hbit k 0 hn d hd hsrc ha
    have hl := Exec.loop_false keepGoing (.seq advance.code (BinaryCounter.decrement src aux bit readBit).code)
      de hr.good.2 (by simp [keepGoing, de])
    have he : de = visited w d src bit k 0 := by
      simp [de, visited, hd.1, Nat.min_eq_left hd.1, ← hi]
    exact he ▸ Exec.seq hr hl
  | succ n ih =>
    let de : Data (K := K) (Γ := Γ) (σ := σ) :=
      ⟨{d.state with value := none, flag := false}, d.inputHead,
        Function.update d.store src ((BinaryCounter.word k n).map bit)⟩
    have hr : Exec w bound (BinaryCounter.decrement src aux bit readBit).code d de := by
      simpa [de] using BinaryCounter.decrement_exec w bound src aux hne bit readBit hbit k (n + 1) hn d hd hsrc ha
    by_cases hend : d.inputHead = w.length + 1
    · have hinput : d.state.input = .rightEnd := by rw [hi, read_right]; omega
      have hl := Exec.loop_false keepGoing (.seq advance.code (BinaryCounter.decrement src aux bit readBit).code)
        de hr.good.2 (by simp [keepGoing, de, hinput])
      have he : de = visited w d src bit k (n + 1) := by
        have hh : ¬ d.inputHead + (n + 1) ≤ w.length + 1 := by omega
        have hp : min (d.inputHead + (n + 1)) (w.length + 1) = d.inputHead := by
          rw [hend, Nat.min_eq_right (by omega)]
        simp [de, visited, hend]
        simpa [hend] using hi
      exact he ▸ Exec.seq hr hl
    · have hhead : d.inputHead < w.length + 1 := by have := hd.1; omega
      have hbound : d.inputHead + 1 ≤ w.length + 1 := by omega
      let dm := afterAdvance w d src bit k n
      have hm : Exec w bound advance.code de dm := by
        have hh := advance.correct w bound de hr.good.2 (by simp [advance, Macro.seq, Macro.move, Macro.sample])
        simpa [dm, afterAdvance, de, advance, Macro.seq, Macro.move, Macro.sample,
          assigned, moved, Move.apply, Nat.min_eq_left hbound,
          Nat.min_eq_left (show d.inputHead ≤ w.length by omega)] using hh
      have hnm : n < 2 ^ k := by omega
      have hinput : dm.state.input = readInput w dm.inputHead := rfl
      have hsource : dm.store src = (BinaryCounter.word k n).map bit := by simp [dm, afterAdvance]
      have haux : dm.store aux = [] := by simp [dm, afterAdvance, Ne.symm hne, ha]
      have ht := ih dm hnm hm.good.2 hinput hsource haux
      cases ht with
      | @seq _ _ _ dn _ hdec hloop =>
        have hl : Exec w bound
            (.loop keepGoing (.seq advance.code (BinaryCounter.decrement src aux bit readBit).code))
            de (visited w dm src bit k n) :=
          .loop_true (by simp [keepGoing, de, hi, read_right, Nat.not_le_of_gt hhead])
            (.seq hm hdec) hloop
        exact visited_advance w d src bit k n hhead ▸ Exec.seq hr hl

def visitFrom (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Macro K Γ σ where
  code := visitFromCode src aux bit readBit
  result w d := visited w d src bit (d.store src).length (BinaryCounter.value ((d.store src).map readBit))
  guard w _ d := src ≠ aux ∧ (∀ b, readBit (bit b) = b) ∧ d.store aux = [] ∧
    ((d.store src).map readBit).map bit = d.store src ∧ d.state.input = readInput w d.inputHead
  correct w bound d hd h := by
    have hx : BinaryCounter.word (d.store src).length (BinaryCounter.value ((d.store src).map readBit)) =
        (d.store src).map readBit := by
      simpa using BinaryCounter.word_of_value ((d.store src).map readBit)
    exact visitFrom_exec w bound src aux h.1 bit readBit h.2.1 _ _ d
      (by simpa using BinaryCounter.value_lt ((d.store src).map readBit)) hd h.2.2.2.2
      (by rw [hx]; exact h.2.2.2.1.symm) h.2.2.1

def visit (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Macro K Γ σ :=
  Macro.seq rewind (visitFrom src aux bit readBit)

def positionCheck (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) (desired : σ → InputSymbol) :
    Macro K Γ σ :=
  Macro.seq (visit src aux bit readBit)
    (Macro.assign (fun s => {s with flag := s.flag && decide (s.input = desired s.user)}))

lemma positionCheck_guard (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b) (desired : σ → InputSymbol)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (ha : d.store aux = [])
    (hsrc : ((d.store src).map readBit).map bit = d.store src) :
    (positionCheck src aux bit readBit desired).guard w bound d := by
  simp only [List.map_map] at hsrc
  simp [positionCheck, visit, visitFrom, rewind, rewound, Macro.seq, Macro.assign,
    hne, hbit, ha, hsrc, readInput]

lemma positionCheck_result (w : Word) (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool)
    (desired : σ → InputSymbol) (d : Data (K := K) (Γ := Γ) (σ := σ)) :
    ((positionCheck src aux bit readBit desired).result w d).state.flag = true ↔
      BinaryCounter.value ((d.store src).map readBit) ≤ w.length + 1 ∧
        readInput w (BinaryCounter.value ((d.store src).map readBit)) = desired d.state.user := by
  by_cases h : BinaryCounter.value ((d.store src).map readBit) ≤ w.length + 1
  · simp [positionCheck, visit, visitFrom, rewind, rewound, visited, Macro.seq, Macro.assign,
      assigned, h, Nat.min_eq_left h]
  · simp [positionCheck, visit, visitFrom, rewind, rewound, visited, Macro.seq, Macro.assign,
      assigned, h]

end

end Lax434930Proofs.SavitchProofs.InputRoutines
