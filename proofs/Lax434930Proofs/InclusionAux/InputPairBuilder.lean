import Lax434930Proofs.SavitchProofs.InputRoutines
import Lax434930.Certificates

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.InputPairBuilder

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.Certificates
open Lax434930Proofs.SavitchProofs
open StackLanguage (Exec Good assigned pushed moved)
open StackRoutines (Control Data Code)
open StackMacros
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def encodedInput (bit : Bool → Γ) (xs : Word) : List Γ := xs.flatMap (fun b => [bit false, bit b])

lemma prefix_pair (bit : Bool → Γ) (xs ys : Word) :
    (pair xs ys).map bit = encodedInput bit xs ++ bit true :: ys.map bit := by
  induction xs <;> simp_all [pair, encodedInput]

def body (dst : K) (bit : Bool → Γ) : Macro K Γ σ :=
  Macro.seq (Macro.push dst (fun s => bit (match s.input with | .bit b => b | _ => false)))
    (Macro.seq (Macro.push dst (fun _ => bit false)) InputRoutines.rewindBody)

def result (dst : K) (bit : Bool → Γ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (xs : Word) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with input := .leftEnd}, 0, Function.update d.store dst (encodedInput bit xs ++ d.store dst)⟩

lemma loop_execution (dst : K) (bit : Bool → Γ) (w : Word) (bound i : ℕ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hi : d.inputHead = i) (hn : i ≤ w.length) (hs : d.state.input = readInput w i)
    (hb : 2 * i + (d.store dst).length < bound) :
    Exec w bound (.loop (fun s => decide (s.input ≠ .leftEnd)) (body dst bit).code)
      d (result dst bit d (w.take i)) := by
  induction i generalizing d with
  | zero =>
    have hinput : d.state.input = .leftEnd := by simpa [readInput] using hs
    have he : result dst bit d (w.take 0) = d := by
      cases d with
      | mk state inputHead store =>
        dsimp [result]
        congr 1
        · cases state; simp_all
        · exact hi.symm
        · simp [encodedInput]
    rw [he]
    exact Exec.loop_false _ _ _ hd (by simp [hinput])
  | succ i ih =>
    have hil : i < w.length := by omega
    have hinput : d.state.input = .bit w[i] := by
      simpa [readInput, List.getElem?_eq_getElem hil] using hs
    have hg : (body dst bit).guard w bound d := by
      simp only [body, Macro.seq, Macro.push, InputRoutines.rewindBody,
        Macro.move, Macro.sample, pushed, Function.update_self, List.length_cons]
      exact ⟨by omega, by omega, trivial, trivial⟩
    let de := (body dst bit).result w d
    have he : Exec w bound (body dst bit).code d de := (body dst bit).correct w bound d hd hg
    have hhead : de.inputHead = i := by
      simp [de, body, Macro.seq, Macro.push, InputRoutines.rewindBody, Macro.move,
        Macro.sample, assigned, pushed, moved, Move.apply, hi, Nat.min_eq_left (by omega : i ≤ w.length + 1)]
    have hstate : de.state.input = readInput w i := by
      change readInput w de.inputHead = readInput w i
      rw [hhead]
    have hstore : de.store dst = bit false :: bit w[i] :: d.store dst := by
      simp [de, body, Macro.seq, Macro.push, InputRoutines.rewindBody, Macro.move,
        Macro.sample, assigned, pushed, moved, hinput]
    have ht := ih de he.good.2 hhead (by omega) hstate (by
      rw [hstore]
      simp only [List.length_cons]
      omega)
    have hresult : result dst bit de (w.take i) = result dst bit d (w.take (i + 1)) := by
      dsimp [result, de, body, Macro.seq, Macro.push, InputRoutines.rewindBody,
        Macro.move, Macro.sample, assigned, pushed, moved]
      congr 1
      funext k
      by_cases hk : k = dst
      · subst k
        simp only [Function.update_self, hinput, List.take_succ_eq_append_getElem hil,
          encodedInput, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.cons_append, List.nil_append, List.append_assoc]
      · simp [hk]
    exact hresult ▸ Exec.loop_true (by simp [hinput]) he ht

def code (dst : K) (bit : Bool → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (Macro.push dst (fun _ => bit true)).code
    (.seq InputRoutines.rewindBody.code
      (.loop (fun s => decide (s.input ≠ .leftEnd)) (body dst bit).code))

def paired (dst : K) (bit : Bool → Γ) (w : Word) (d : Data (K := K) (Γ := Γ) (σ := σ)) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with input := .leftEnd}, 0,
    Function.update d.store dst (encodedInput bit w ++ bit true :: d.store dst)⟩

lemma execution (dst : K) (bit : Bool → Γ) (w : Word) (bound : ℕ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hi : d.inputHead = w.length + 1)
    (hb : 2 * w.length + 1 + (d.store dst).length < bound) :
    Exec w bound (code dst bit) d (paired dst bit w d) := by
  have hp := (Macro.push (σ := σ) dst (fun _ => bit true)).correct w bound d hd (by
    dsimp [Macro.push]
    omega)
  let dp := (Macro.push (σ := σ) dst (fun _ => bit true)).result w d
  have hr := (InputRoutines.rewindBody (K := K) (Γ := Γ) (σ := σ)).correct w bound dp hp.good.2
    ⟨trivial, trivial⟩
  let dr := InputRoutines.rewindBody.result w dp
  have hhead : dr.inputHead = w.length := by
    simp [dr, dp, InputRoutines.rewindBody, Macro.seq, Macro.move, Macro.sample,
      Macro.push, moved, assigned, pushed, Move.apply, hi]
  have hstate : dr.state.input = readInput w w.length := by
    change readInput w dr.inputHead = _
    rw [hhead]
  have hstore : dr.store dst = bit true :: d.store dst := by
    simp [dr, dp, InputRoutines.rewindBody, Macro.seq, Macro.move, Macro.sample,
      Macro.push, moved, assigned, pushed]
  have hl := loop_execution dst bit w bound w.length dr hr.good.2 hhead le_rfl hstate (by
    rw [hstore]
    simp only [List.length_cons]
    omega)
  have he : result dst bit dr (w.take w.length) = paired dst bit w d := by
    simp [result, paired, dr, dp, InputRoutines.rewindBody, Macro.seq, Macro.move,
      Macro.sample, Macro.push, moved, assigned, pushed]
  exact he ▸ Exec.seq hp (Exec.seq hr hl)

end

end Lax434930Proofs.InclusionAux.InputPairBuilder
