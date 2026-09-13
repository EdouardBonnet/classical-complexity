import Lax434930Proofs.SavitchProofs.StackMacros

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.InputRoutines

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Command Exec Good assigned moved)
open StackRoutines (Control Code Data)
open StackMacros
open scoped Classical

noncomputable section

lemma read_left (w : Word) (i : ℕ) : readInput w i = .leftEnd ↔ i = 0 := by
  cases i with
  | zero => simp [readInput]
  | succ i => cases h : w[i]? <;> simp [readInput, h]

lemma read_right (w : Word) (i : ℕ) : readInput w i = .rightEnd ↔ w.length + 1 ≤ i := by
  cases i with
  | zero => simp [readInput]
  | succ i =>
    cases h : w[i]? with
    | none =>
      have hi : w.length ≤ i := List.getElem?_eq_none_iff.mp h
      simp [readInput, h, hi]
    | some b =>
      have hi : i < w.length := by
        by_contra hn
        have hh : w[i]? = none := List.getElem?_eq_none (by omega)
        simp [h] at hh
      simp [readInput, h, Nat.not_le_of_gt hi]

variable {K Γ σ : Type}

def rewindBody : Macro K Γ σ := Macro.seq (Macro.move (fun _ => .left)) Macro.sample

def rewindCode : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq Macro.sample.code (.loop (fun s => decide (s.input ≠ .leftEnd)) rewindBody.code)

def rewound (d : Data (K := K) (Γ := Γ) (σ := σ)) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with input := .leftEnd}, 0, d.store⟩

lemma rewind_loop (w : Word) (bound : ℕ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hd : Good w bound d) (hi : d.state.input = readInput w d.inputHead) :
    Exec w bound (.loop (fun s => decide (s.input ≠ .leftEnd)) rewindBody.code) d (rewound d) := by
  generalize hn : d.inputHead = n at *
  induction n generalizing d with
  | zero =>
    have hs : d.state.input = .leftEnd := by simpa [readInput] using hi
    have he : rewound d = d := by
      cases d with
      | mk state inputHead store =>
        dsimp [rewound]
        congr 1
        · cases state
          simp_all only [Control.mk.injEq, true_and]
        · exact hn.symm
    rw [he]
    exact .loop_false _ _ _ hd (by simp [hs])
  | succ n ih =>
    have hguard : (rewindBody (K := K) (Γ := Γ) (σ := σ)).guard w bound d := by
      simp [rewindBody, Macro.seq, Macro.move, Macro.sample]
    let de := rewindBody.result w d
    have hb : Exec w bound rewindBody.code d de := rewindBody.correct w bound d hd hguard
    have hbound : n ≤ w.length + 1 := by have hh := hd.1; omega
    have he : de.inputHead = n := by
      simp [de, rewindBody, Macro.seq, Macro.move, Macro.sample, assigned, moved,
        Move.apply, hn, Nat.min_eq_left hbound]
    have hs : de.state.input = readInput w n := by
      simp [de, rewindBody, Macro.seq, Macro.move, Macro.sample, assigned, moved,
        Move.apply, hn, Nat.min_eq_left hbound]
    have ht := ih de hb.good.2 he hs
    have hr : rewound de = rewound d := by
      simp [rewound, de, rewindBody, Macro.seq, Macro.move, Macro.sample, assigned, moved]
    exact hr ▸ Exec.loop_true (by simp [hi, read_left]) hb ht

def rewind : Macro K Γ σ where
  code := rewindCode
  result _ d := rewound d
  guard _ _ _ := True
  correct w bound d hd _ := by
    have hs := Macro.sample.correct w bound d hd trivial
    have hl := rewind_loop w bound _ hs.good.2 rfl
    simpa [rewindCode, rewound, Macro.sample, assigned] using Exec.seq hs hl

end

end Lax434930Proofs.SavitchProofs.InputRoutines
