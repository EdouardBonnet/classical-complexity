import Lax434930Proofs.SpaceStackExecution

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SpaceToStack

open Lax434930.PolynomialTime Lax434930.SpaceMachines Turing Time

noncomputable section

attribute [local instance] Classical.propDecidable

lemma outputs (M : Machine) (A : Language) (hd : M.Deterministic) (hdec : M.Decides A)
    (s t : ℕ → ℕ) (hs : ∀ w, M.UsesSpace w (s w.length))
    (ht : ∀ w n c, M.Run w n c → n ≤ t w.length) (w : Word) :
    Within (machine M).step (t w.length + w.length + s w.length + 6)
      (initList (machine M) w) (haltList (machine M) [decide (w ∈ A)]) := by
  classical
  obtain ⟨n, c, hr, hc⟩ := ConfigurationTime.terminal_run (hdec w).1
  have hanswer : M.accept c.state = decide (w ∈ A) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      ((terminal_acceptance M hd w hr hc).symm.trans (hdec w).2)
  have h := halting_simulation M hd w (s w.length) (hs w) hr hc
  rw [hanswer] at h
  exact h.mono (by have := ht w n c hr; omega)

/-- A deterministic space-model decider becomes a stack decider with its proved time bound. -/
def timeComputer (M : Machine) (A : Language) (hd : M.Deterministic) (hdec : M.Decides A)
    (s t : ℕ → ℕ) (hs : ∀ w, M.UsesSpace w (s w.length))
    (ht : ∀ w n c, M.Run w n c → n ≤ t w.length) :
    TM2ComputableInTime id Computability.encodeBool (fun w => decide (w ∈ A)) where
  tm := machine M
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time n := t n + n + s n + 6
  outputsFun w := by
    simpa [Equiv.refl, Computability.encodeBool] using!
      (outputs M A hd hdec s t hs ht w).evals

/-- Polynomial bounds in the space-machine model give the unchanged stack-machine class P. -/
lemma polynomial_time_in_P (M : Machine) (A : Language) (hd : M.Deterministic)
    (hdec : M.Decides A) (s t : Polynomial ℕ) (hs : ∀ w, M.UsesSpace w (s.eval w.length))
    (ht : ∀ w n c, M.Run w n c → n ≤ t.eval w.length) : A ∈ P := by
  classical
  let C := timeComputer M A hd hdec s.eval t.eval hs ht
  refine ⟨fun w => decide (w ∈ A), by simp, ⟨{
    toTM2ComputableAux := C.toTM2ComputableAux
    time := t + Polynomial.X + s + 6
    outputsFun := fun w => ?_ }⟩⟩
  simpa [C, timeComputer] using! C.outputsFun w

end

end Lax434930Proofs.SpaceToStack
