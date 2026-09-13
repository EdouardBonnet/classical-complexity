import Lax434930Proofs.SavitchProofs.SearchSimulation

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.SearchProgram

open StackSearch StackMacros
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Good Exec)
open scoped Classical

noncomputable section

variable {β ε δ : Type}

lemma fits_running (m : ℕ) (s : State (2 ^ m)) (d : Data β ε δ) (hd : Fits m s d) :
    running d.state = true := by
  simp only [running, hd.1]
  cases s <;> rfl

lemma step_correct (query : Routine β ε δ) (G) (hq : QueryCorrect query G)
    (w : Word) (m : ℕ) (s t : State (2 ^ m))
    (ht : step (G w m) s = some t) (hs : s.Valid m)
    (d : Data β ε δ) (hg : Good w (budget m) d) (hd : Fits m s d) :
    (oneStep query).guard w (budget m) d ∧ Fits m t ((oneStep query).result w d) := by
  have hp := hd.1
  cases s with
  | call k a b stack =>
    cases k with
    | zero =>
      simp only [step, Option.some.injEq] at ht
      subst t
      simpa [oneStep, Macro.branch, hp, phase] using call_zero w m a b stack query G hq d hg hd
    | succ k =>
      simp only [step, Option.some.injEq] at ht
      subst t
      simpa [oneStep, Macro.branch, hp, phase] using call_successor w m k a b stack query d hd
  | scan k a b mid stack =>
    simpa [oneStep, Macro.branch, hp, phase] using scan_step w m k (G w m) a b mid stack t ht hs d hd
  | ret answer stack =>
    cases stack with
    | nil => simp [step] at ht
    | cons frame stack =>
      simpa [oneStep, Macro.branch, hp, phase] using return_step w m (G w m) answer frame stack t ht hs d hd

lemma terminal_correct (query : Routine β ε δ) (w : Word) (m : ℕ)
    (G : Lax434930Proofs.SavitchDefinitions.Reachability.Graph (2 ^ m)) (s : State (2 ^ m)) (ht : step G s = none)
    (d : Data β ε δ) (hd : Fits m s d) :
    (oneStep query).guard w (budget m) d ∧
      ((oneStep query).result w d).state.user.phase = .done ∧
      ((oneStep query).result w d).state.user.answer = s.value G := by
  obtain ⟨answer, rfl⟩ := (step_eq_none G s).mp ht
  simpa [oneStep, Macro.branch, hd.1, phase, State.value, unwind] using return_nil w m answer d hd

lemma search_execution (query : Routine β ε δ) (G) (hq : QueryCorrect query G)
    (w : Word) (m : ℕ) (s : State (2 ^ m)) (hs : s.Valid m)
    (d : Data β ε δ) (hg : Good w (budget m) d) (hd : Fits m s d) :
    ∃ e, Exec w (budget m) (search query) d e ∧ e.state.user.phase = .done ∧
      e.state.user.answer = s.value (G w m) := by
  induction s using (measure State.cost).wf.induction generalizing d with
  | h s ih =>
    cases ht : step (G w m) s with
    | none =>
      obtain ⟨hguard, hdone, hanswer⟩ := terminal_correct query w m (G w m) s ht d hd
      have he := (oneStep query).correct w (budget m) d hg hguard
      have hlast := Exec.loop_false running (oneStep query).code _ he.good.2
        (by simp [running, hdone])
      exact ⟨_, .loop_true (fits_running m s d hd) he hlast, hdone, hanswer⟩
    | some t =>
      obtain ⟨hguard, hfit⟩ := step_correct query G hq w m s t ht hs d hg hd
      have he := (oneStep query).correct w (budget m) d hg hguard
      obtain ⟨e, hrun, hdone, hanswer⟩ := ih t (cost_decreases (G w m) ht)
        (valid_preserved (G w m) hs ht) _ he.good.2 hfit
      exact ⟨e, .loop_true (fits_running m s d hd) he hrun, hdone,
        hanswer.trans (value_preserved (G w m) ht)⟩

lemma search_call (query : Routine β ε δ) (G) (hq : QueryCorrect query G)
    (w : Word) (m : ℕ) (a b : Fin (2 ^ m))
    (d : Data β ε δ) (hg : Good w (budget m) d) (hd : Fits m (.call m a b []) d) :
    ∃ e, Exec w (budget m) (search query) d e ∧ e.state.user.phase = .done ∧
      e.state.user.answer = Lax434930Proofs.SavitchDefinitions.Reachability.search (G w m) m a b := by
  exact search_execution query G hq w m (.call m a b []) (by simp [State.Valid, StackValid]) d hg hd

end

end Lax434930Proofs.SavitchProofs.SearchProgram
