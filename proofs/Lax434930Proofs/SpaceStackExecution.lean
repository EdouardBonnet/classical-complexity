import Lax434930Proofs.SpaceToStack
import Lax434930Proofs.ConfigurationTime
import Lax434930Proofs.SpacePaths
import Lax434930Proofs.Time

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SpaceToStack

open Lax434930.PolynomialTime Lax434930.SpaceMachines Turing Time

noncomputable section

lemma expand_state (M : Machine) (v : View M) : v.expand.state = v.state := rfl

lemma expand_input (M : Machine) (v : View M) : v.expand.inputHead = v.input.position := rfl

lemma expand_current (M : Machine) (v : View M) :
    v.expand.tape v.expand.workHead = v.current := WorkTapeView.current_scanned M v.work

lemma run_simulation (M : Machine) (hd : M.Deterministic) (w : Word) (s : ℕ)
    (hs : M.UsesSpace w s) {n : ℕ} {c : M.Config} (hr : M.Run w n c) :
    ∃ (v : View M) (r : Register M), v.input.Valid ∧ v.input.word = w ∧
      v.expand = c ∧ v.work.cells ≤ s ∧
      Run (machine M).step n (initList (machine M) w) (cfg v r) := by
  induction hr with
  | zero =>
    refine ⟨initial M w, (none, none), InputTapeView.initial_valid w,
      InputTapeView.initial_word w, initial_expand M w, ?_, ?_⟩
    · have hp := SpaceSemantics.space_positive hs
      change 1 ≤ s
      omega
    · rw [init_eq]
      exact .zero _
  | @succ n c d hr he ih =>
    obtain ⟨v, r, hv, hw, hc, hcells, ht⟩ := ih
    obtain ⟨a, ha, rfl⟩ := he
    have hchoice : choose M v.state v.input.current v.current = some a := by
      apply choose_action M hd _ _ _ a
      rw [← hc, ← hw] at ha
      simpa only [expand_state, expand_input, expand_current,
        InputTapeView.read_current _ hv] using ha
    have he : (apply M v a).expand = M.execute w c a := by
      rw [apply_expand M v a hv, hw, hc]
    have hcells' : (apply M v a).work.cells ≤ s := by
      rw [apply_work M v a hv]
      apply WorkTapeView.cells_preserved M v.input.word v.work a s hcells
      change (WorkTapeView.apply M v.input.word v.work a).expand.workHead < s
      rw [← apply_work M v a hv]
      change (apply M v a).expand.workHead < s
      rw [he]
      exact hs (n + 1) _ (.succ hr ⟨a, ha, rfl⟩)
    exact ⟨apply M v a, nextRegister v a r, InputTapeView.move_valid _ _ hv,
      (InputTapeView.move_word _ _ hv).trans hw, he, hcells',
      ht.trans (.one (action_step M v r a hv hchoice))⟩

lemma terminal_choice (M : Machine) (v : View M) (hv : v.input.Valid)
    (ht : M.Terminal v.input.word v.expand) :
    choose M v.state v.input.current v.current = none := by
  cases h : choose M v.state v.input.current v.current with
  | none => rfl
  | some a =>
    have ha := choose_mem M v.state v.input.current v.current a h
    exact (ht (M.execute v.input.word v.expand a) ⟨a, by
      simpa only [expand_state, expand_input, expand_current,
        InputTapeView.read_current _ hv] using ha, rfl⟩).elim

def clearCfg (M : Machine) (b : Bool) (k : Key) (r : Register M)
    (store : (k : Key) → List (Alphabet M k)) : (machine M).Cfg :=
  ⟨some (.clear b k), r, store⟩

lemma begin_clear (M : Machine) (v : View M) (r : Register M)
    (hc : choose M v.state v.input.current v.current = none) :
    (machine M).step (cfg v r) =
      some (clearCfg M (M.accept v.state) .inputLeft r (memory v)) := by
  simp [FinTM2.step, machine, code, cfg, clearCfg, TM2.step, TM2.stepAux, hc]

lemma clear_cons (M : Machine) (b : Bool) (k : Key) (hk : k ≠ .output)
    (r : Register M) (store : (k : Key) → List (Alphabet M k))
    (g : Alphabet M k) (xs : List (Alphabet M k)) :
    (machine M).step (clearCfg M b k r (Function.update store k (g :: xs))) =
      some (clearCfg M b k (some true, none) (Function.update store k xs)) := by
  cases k <;> simp_all [FinTM2.step, machine, code, clearCfg, TM2.step, TM2.stepAux]

lemma clear_nil (M : Machine) (b : Bool) (k : Key) (hk : k ≠ .output)
    (r : Register M) (store : (k : Key) → List (Alphabet M k)) :
    (machine M).step (clearCfg M b k r (Function.update store k [])) =
      some (clearCfg M b (nextKey k) (some false, none) (Function.update store k [])) := by
  cases k <;> simp_all [FinTM2.step, machine, code, clearCfg, TM2.step, TM2.stepAux, nextKey]

lemma clear_stack (M : Machine) (b : Bool) (k : Key) (hk : k ≠ .output)
    (store : (k : Key) → List (Alphabet M k)) (xs : List (Alphabet M k))
    (r : Register M) :
    Run (machine M).step (xs.length + 1)
      (clearCfg M b k r (Function.update store k xs))
      (clearCfg M b (nextKey k) (some false, none) (Function.update store k [])) := by
  induction xs generalizing r with
  | nil => exact .one (clear_nil M b k hk r store)
  | cons g xs ih =>
    exact .cons (clear_cons M b k hk r store g xs) (ih (some true, none))

lemma clear_stack_from (M : Machine) (b : Bool) (k : Key) (hk : k ≠ .output)
    (store : (k : Key) → List (Alphabet M k)) (r : Register M) :
    Run (machine M).step ((store k).length + 1) (clearCfg M b k r store)
      (clearCfg M b (nextKey k) (some false, none) (Function.update store k [])) := by
  simpa only [Function.update_eq_self] using clear_stack M b k hk store (store k) r

lemma clear_all (M : Machine) (v : View M) (b : Bool) (r : Register M) :
    Run (machine M).step
      (v.input.left.length + v.input.right.length + v.left.length + v.right.length + 5)
      (clearCfg M b .inputLeft r (memory v)) (haltList (machine M) [b]) := by
  let s₁ := Function.update (memory v) Key.inputLeft []
  let s₂ := Function.update s₁ Key.inputRight []
  let s₃ := Function.update s₂ Key.workLeft []
  let s₄ := Function.update s₃ Key.workRight []
  have h₁ := clear_stack_from M b .inputLeft (by decide) (memory v) r
  have h₂ := clear_stack_from M b .inputRight (by decide) s₁ (some false, none)
  have h₃ := clear_stack_from M b .workLeft (by decide) s₂ (some false, none)
  have h₄ := clear_stack_from M b .workRight (by decide) s₃ (some false, none)
  have h₅ : (machine M).step (clearCfg M b .output (some false, none) s₄) =
      some (haltList (machine M) [b]) := by
    simp [FinTM2.step, machine, code, clearCfg, TM2.step, TM2.stepAux, haltList]
    funext k
    cases k <;> simp [s₄, s₃, s₂, s₁, memory]
  have hall := h₁.trans (h₂.trans (h₃.trans (h₄.trans (.one h₅))))
  convert! hall using 1
  simp [s₁, s₂, s₃, s₄, memory]
  omega

lemma terminal_acceptance (M : Machine) (hd : M.Deterministic) (w : Word)
    {n : ℕ} {c : M.Config} (hr : M.Run w n c) (ht : M.Terminal w c) :
    M.Accepts w ↔ M.accept c.state = true := by
  constructor
  · rintro ⟨m, d, hd', htd, ha⟩
    have hcd := SpacePaths.terminal_path_unique hd (SpacePaths.run_path hr) ht
      (SpacePaths.run_path hd') htd
    simpa only [hcd] using ha
  · intro ha
    exact ⟨n, c, hr, ht, ha⟩

/-- Simulation includes clearing all work stacks and writing a singleton Boolean output. -/
lemma halting_simulation (M : Machine) (hd : M.Deterministic) (w : Word) (s : ℕ)
    (hs : M.UsesSpace w s) {n : ℕ} {c : M.Config} (hr : M.Run w n c)
    (hc : M.Terminal w c) :
    Within (machine M).step (n + w.length + s + 6)
      (initList (machine M) w) (haltList (machine M) [M.accept c.state]) := by
  obtain ⟨v, r, hv, hw, he, hcells, hrun⟩ := run_simulation M hd w s hs hr
  have hterminal : M.Terminal v.input.word v.expand := by simpa only [hw, he] using hc
  have hb := begin_clear M v r (terminal_choice M v hv hterminal)
  have hall := hrun.trans ((Run.one hb).trans (clear_all M v (M.accept v.state) r))
  have hinput : v.input.left.length + v.input.right.length ≤ w.length := by
    rw [← hw]
    cases hi : v.input.current <;> simp [InputTapeView.View.word, hi]
  have hstate : v.state = c.state := congrArg Configuration.state he
  refine ⟨n + (1 + (v.input.left.length + v.input.right.length + v.left.length + v.right.length + 5)), ?_, ?_⟩
  · dsimp [View.work, WorkTapeView.View.cells] at hcells
    omega
  · simpa only [hstate] using! hall

end

end Lax434930Proofs.SpaceToStack
