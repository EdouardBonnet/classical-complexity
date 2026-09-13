import Lax434930Proofs.SavitchProofs.QueryStages
import Lax434930Proofs.SavitchProofs.SearchExecution

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.GraphQuery

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open ConfigurationWords
open StackLanguage (Good Exec assigned)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine) (BΓ : Type)

local infixr:55 " ⋙ₘ " => Macro.seq

def prepare : GraphQuery.Macro M BΓ :=
  Macro.clear (key .aux) ⋙ₘ Macro.clear (key .reverse) ⋙ₘ
    Macro.assign (fun s => {s with user := {s.user with answer := true}})

def procedure : GraphQuery.Macro M BΓ :=
  prepare M BΓ ⋙ₘ copyDecode M BΓ .a .left ⋙ₘ copyDecode M BΓ .b .right ⋙ₘ
    checkWord M BΓ .left ⋙ₘ checkWord M BΓ .right ⋙ₘ automatonCode M BΓ (key .left) (key .right)

lemma procedure_correct (w : Word) (bound : ℕ) (d : Data M BΓ) (xs ys : List Bool)
    (ha : d.store (SearchProgram.key .a) = xs.map SearchProgram.bit)
    (hb : d.store (SearchProgram.key .b) = ys.map SearchProgram.bit)
    (hlen : xs.length = ys.length) (hbound : xs.length + 1 < bound) :
    (procedure M BΓ).guard w bound d ∧
      ((procedure M BΓ).result w d).state.user.phase = d.state.user.phase ∧
      (∀ r, ((procedure M BΓ).result w d).store (SearchProgram.key r) = d.store (SearchProgram.key r)) ∧
      ((procedure M BΓ).result w d).state.user.answer = EncodedGraph.query M w xs ys := by
  let d0 := (prepare M BΓ).result w d
  have g0 : (prepare M BΓ).guard w bound d := by simp [prepare, Macro.seq, Macro.clear, Macro.assign]
  have h0aux : d0.store (key .aux) = [] := by
    simp [d0, prepare, Macro.seq, Macro.clear, Macro.assign, assigned, StackRoutines.cleared, key]
  have h0rev : d0.store (key .reverse) = [] := by
    simp [d0, prepare, Macro.seq, Macro.clear, Macro.assign, assigned, StackRoutines.cleared]
  have h0main (r : SearchProgram.Register) : d0.store (SearchProgram.key r) = d.store (SearchProgram.key r) := by
    simp [d0, prepare, Macro.seq, Macro.clear, Macro.assign, assigned, StackRoutines.cleared, key, SearchProgram.key]
  have h0phase : d0.state.user.phase = d.state.user.phase := rfl
  have h0answer : d0.state.user.answer = true := rfl
  have h0a : d0.store (SearchProgram.key .a) = xs.map SearchProgram.bit := (h0main _).trans ha
  have h0b : d0.store (SearchProgram.key .b) = ys.map SearchProgram.bit := (h0main _).trans hb
  let d1 := (copyDecode M BΓ .a .left).result w d0
  have g1 := copyDecode_guard M BΓ w bound .a .left (by decide) (by decide) d0 xs h0a h0aux h0rev hbound
  have h1 := copyDecode_result M BΓ w .a .left (by decide) d0 xs h0a h0rev
  change d1 = _ at h1
  have h1aux : d1.store (key .aux) = [] := by rw [h1]; simpa [key] using h0aux
  have h1rev : d1.store (key .reverse) = [] := by rw [h1]; simpa [key] using h0rev
  have h1b : d1.store (SearchProgram.key .b) = ys.map SearchProgram.bit := by
    rw [h1]
    simpa [key, SearchProgram.key] using h0b
  let d2 := (copyDecode M BΓ .b .right).result w d1
  have g2 := copyDecode_guard M BΓ w bound .b .right (by decide) (by decide) d1 ys h1b h1aux h1rev (by omega)
  have h2 := copyDecode_result M BΓ w .b .right (by decide) d1 ys h1b h1rev
  change d2 = _ at h2
  let lx := FiniteCoding.decodeWord (Payload M) xs
  let ly := FiniteCoding.decodeWord (Payload M) ys
  have h2left : d2.store (key .left) = lx.map letter := by rw [h2, h1]; simp [key, lx]
  have h2right : d2.store (key .right) = ly.map letter := by rw [h2]; simp [ly]
  have h2aux : d2.store (key .aux) = [] := by rw [h2]; simpa [key] using h1aux
  have h2rev : d2.store (key .reverse) = [] := by rw [h2]; simpa [key] using h1rev
  have hlx : lx.length < bound := (FiniteCoding.decodeWord_length_le (Payload M) xs).trans_lt (by omega)
  have hly : ly.length < bound := (FiniteCoding.decodeWord_length_le (Payload M) ys).trans_lt (by omega)
  let d3 := (checkWord M BΓ .left).result w d2
  have g3 := checkWord_guard M BΓ w bound .left (by decide) (by decide) d2 lx h2left h2aux h2rev hlx
  have h3 := checkWord_result M BΓ w .left d2 lx h2left h2rev
  change d3.state.user.phase = _ ∧ d3.state.user.answer = _ ∧ (∀ k, k ≠ key .temporary → d3.store k = d2.store k) at h3
  have h3left : d3.store (key .left) = lx.map letter := (h3.2.2 _ (by decide)).trans h2left
  have h3right : d3.store (key .right) = ly.map letter := (h3.2.2 _ (by decide)).trans h2right
  have h3aux : d3.store (key .aux) = [] := (h3.2.2 _ (by decide)).trans h2aux
  have h3rev : d3.store (key .reverse) = [] := (h3.2.2 _ (by decide)).trans h2rev
  let d4 := (checkWord M BΓ .right).result w d3
  have g4 := checkWord_guard M BΓ w bound .right (by decide) (by decide) d3 ly h3right h3aux h3rev hly
  have h4 := checkWord_result M BΓ w .right d3 ly h3right h3rev
  change d4.state.user.phase = _ ∧ d4.state.user.answer = _ ∧ (∀ k, k ≠ key .temporary → d4.store k = d3.store k) at h4
  have h4left : d4.store (key .left) = lx.map letter := (h4.2.2 _ (by decide)).trans h3left
  have h4right : d4.store (key .right) = ly.map letter := (h4.2.2 _ (by decide)).trans h3right
  have g5 := automatonCode_guard M BΓ w bound (key .left) (key .right) (by decide) d4
  have h5 := automatonCode_result M BΓ w (key .left) (key .right) d4 lx ly h4left h4right
    (FiniteCoding.decodeWord_length_eq (Payload M) hlen)
  refine ⟨⟨g0, g1, g2, g3, g4, g5⟩, ?_, ?_, ?_⟩
  · change ((automatonCode M BΓ (key .left) (key .right)).result w d4).state.user.phase = _
    rw [h5]
    change d4.state.user.phase = _
    rw [h4.1, h3.1, h2, h1]
    exact h0phase
  · intro r
    change ((automatonCode M BΓ (key .left) (key .right)).result w d4).store (SearchProgram.key r) = _
    rw [h5]
    have hkeep : (Function.update (Function.update d4.store (key .left) []) (key .right) []) (SearchProgram.key r) =
        d4.store (SearchProgram.key r) := by simp [key, SearchProgram.key]
    change (Function.update (Function.update d4.store (key .left) []) (key .right) []) (SearchProgram.key r) = _
    rw [hkeep, h4.2.2 _ (by simp [key, SearchProgram.key]), h3.2.2 _ (by simp [key, SearchProgram.key]), h2, h1]
    simpa [key, SearchProgram.key] using h0main r
  · change ((automatonCode M BΓ (key .left) (key .right)).result w d4).state.user.answer = _
    rw [h5]
    change (d4.state.user.answer && decide (List.zip lx ly ∈ (PatternAutomata.machine (graphPatterns M)).accepts)) = _
    rw [h4.2.1, h3.2.1, h2, h1]
    change (((d0.state.user.answer && decide (ValidInput M w lx)) && decide (ValidInput M w ly)) && _) = _
    rw [h0answer]
    apply Bool.eq_iff_iff.mpr
    simp [EncodedGraph.query, lx, ly, and_assoc, and_comm, and_left_comm]

lemma query_correct : SearchProgram.QueryCorrect (procedure M BΓ) (EncodedGraph.graph M) := by
  intro w m a b stack d _ hfit
  have ha := hfit.2.1 .a
  have hb := hfit.2.1 .b
  simp only [SearchProgram.store, SearchProgram.word] at ha hb
  have hbound : (BinaryCounter.word m a.val).length + 1 < SearchProgram.budget m := by
    simp only [BinaryCounter.word_length, SearchProgram.budget]
    nlinarith
  obtain ⟨hg, hphase, hstore, hanswer⟩ := procedure_correct M BΓ w (SearchProgram.budget m) d
    (BinaryCounter.word m a.val) (BinaryCounter.word m b.val) ha hb (by simp) hbound
  refine ⟨hg, ⟨hphase.trans hfit.1, ?_, trivial⟩, hanswer⟩
  intro r
  exact (hstore r).trans (hfit.2.1 r)

end

end Lax434930Proofs.SavitchProofs.GraphQuery
