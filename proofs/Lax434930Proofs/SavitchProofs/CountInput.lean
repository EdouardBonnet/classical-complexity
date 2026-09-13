import Lax434930Proofs.SavitchProofs.UnaryPolynomial
import Lax434930Proofs.SavitchProofs.InputRoutines

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.UnaryPolynomial

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Exec Good assigned moved pushed)
open StackMacros (Macro)
open scoped Classical

noncomputable section

def advance {m : ℕ} : Macro (Register m) Unit Unit :=
  Macro.seq (Macro.move (fun _ => .right)) Macro.sample

def countBody {m : ℕ} : Macro (Register m) Unit Unit :=
  Macro.seq (Macro.push .input (fun _ => ())) advance

def countCode (m : ℕ) : Code m :=
  .seq advance.code (.loop (fun s => decide (s.input ≠ .rightEnd)) countBody.code)

def counted {m : ℕ} (w : Word) (d : Data m) (remaining : ℕ) : Data m :=
  ⟨{d.state with input := .rightEnd}, w.length + 1,
    Function.update d.store .input (List.replicate remaining () ++ d.store .input)⟩

lemma count_loop {m : ℕ} (w : Word) (bound remaining : ℕ) (d : Data m)
    (hd : Good w bound d) (hi : d.inputHead + remaining = w.length + 1)
    (hs : d.state.input = readInput w d.inputHead)
    (hb : remaining + (d.store .input).length < bound) :
    Exec w bound (.loop (fun s => decide (s.input ≠ .rightEnd)) countBody.code)
      d (counted w d remaining) := by
  induction remaining generalizing d with
  | zero =>
    have hhead : d.inputHead = w.length + 1 := by omega
    have hs' : d.state.input = .rightEnd := by rw [hs]; exact (InputRoutines.read_right _ _).mpr (by omega)
    have he : counted w d 0 = d := by
      cases d with
      | mk state inputHead store =>
        dsimp [counted]
        congr 1
        · cases state
          simp_all
        · exact hhead.symm
        · simp
    rw [he]
    exact .loop_false _ _ _ hd (by simp [hs'])
  | succ remaining ih =>
    have hpos : d.inputHead < w.length + 1 := by omega
    have hg : (countBody (m := m)).guard w bound d := by
      simp only [countBody, advance, Macro.seq, Macro.push, Macro.move, Macro.sample]
      exact ⟨by omega, trivial, trivial⟩
    let de := countBody.result w d
    have he : Exec w bound countBody.code d de := countBody.correct w bound d hd hg
    have hhead : de.inputHead = d.inputHead + 1 := by
      simp [de, countBody, advance, Macro.seq, Macro.push, Macro.move, Macro.sample,
        pushed, moved, assigned, Move.apply, Nat.min_eq_left (by omega : d.inputHead ≤ w.length)]
    have hstore : de.store .input = () :: d.store .input := by
      simp [de, countBody, advance, Macro.seq, Macro.push, Macro.move, Macro.sample, pushed, moved, assigned]
    have hstate : de.state.input = readInput w de.inputHead := rfl
    have ht := ih de he.good.2 (by rw [hhead]; omega) hstate (by rw [hstore]; simp only [List.length_cons]; omega)
    have hresult : counted w de remaining = counted w d (remaining + 1) := by
      dsimp [counted, de, countBody, advance, Macro.seq, Macro.push, Macro.move, Macro.sample, pushed, moved, assigned]
      congr 1
      funext k
      by_cases hk : k = .input
      · subst k
        simp only [Function.update_self]
        rw [List.replicate_add]
        simp
      · simp [hk]
    exact hresult ▸ Exec.loop_true (by simp [hs, InputRoutines.read_right, Nat.not_le_of_gt hpos]) he ht

def initial (_m : ℕ) : StackRoutines.Control Unit Unit := ⟨(), none, false, .leftEnd, none⟩

def countResult (m : ℕ) (w : Word) : Data m :=
  ⟨{initial m with input := .rightEnd}, w.length + 1,
    Function.update (fun _ => []) .input (List.replicate w.length ())⟩

lemma count_exec (m : ℕ) (w : Word) (bound : ℕ) (hb : w.length < bound) :
    Exec w bound (countCode m) ⟨initial m, 0, fun _ => []⟩ (countResult m w) := by
  let d : Data m := ⟨initial m, 0, fun _ => []⟩
  have hd : Good w bound d := ⟨by simp [d], by intro k; simpa [d] using (show 0 < bound by omega)⟩
  have ha : Exec w bound advance.code d (advance.result w d) := advance.correct w bound d hd ⟨trivial, trivial⟩
  have hhead : (advance.result w d).inputHead = 1 := by
    simp [advance, Macro.seq, Macro.move, Macro.sample, moved, assigned, Move.apply, d]
  have hloop := count_loop w bound w.length (advance.result w d) ha.good.2 (by rw [hhead]; omega) rfl
    (by simpa [advance, Macro.seq, Macro.move, Macro.sample, moved, assigned, d] using hb)
  have he : counted w (advance.result w d) w.length = countResult m w := by
    simp [counted, countResult, advance, Macro.seq, Macro.move, Macro.sample, moved, assigned, d]
  exact he ▸ Exec.seq ha hloop

end

end Lax434930Proofs.SavitchProofs.UnaryPolynomial
