import Lax434930Proofs.StackToTape

set_option backward.isDefEq.respectTransparency false

/-! The existing stack-to-tape simulations with arbitrary, explicitly retained time bounds. -/

namespace Lax434930Proofs.GeneralTimeSimulation

open Turing Time Lax434930.PolynomialTime Lax434930.MachineModels

section Output

open TapeOutput
attribute [local instance] TapeOutput.initial
variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]
variable (M : TM0.Machine Γ Q) (read : Q → Γ → Bool)

theorem of_supported_time [Fintype Γ] (S : Finset Q) (hS : TM0.Supports M (S : Set Q))
    (input : Bool ↪ Γ) (hi : ∀ b, input b ≠ default) (t : ℕ → ℕ)
    (L : Lax434930.PolynomialTime.Language)
    (h : ∀ w : List Bool, ∃ c : TM0.Cfg Γ Q,
      Within (TM0.step M) (t w.length) (TM0.init (w.map input)) c ∧
      TM0.step M c = none ∧ (read c.q c.Tape.head = true ↔ w ∈ L)) :
    ∃ N : Lax434930.MachineModels.SingleTape, ∀ w : List Bool,
      ∃ c : TM0.Cfg N.Γ N.Q,
        Nonempty (StateTransition.EvalsToInTime (TM0.step N.transition)
          (TM0.init (w.map N.input)) (some c) (t w.length + 1)) ∧
        TM0.step N.transition c = none ∧ (N.accept c.q = true ↔ w ∈ L) := by
  classical
  let W := program M read
  let S' := labels S
  have hS' : TM0.Supports W (S' : Set (Sum Q Bool)) := supports M read hS
  letI := FiniteControl.initial W S' hS'
  let N : Lax434930.MachineModels.SingleTape :=
    { Γ := Γ
      Q := {q // q ∈ S'}
      input := input
      input_ne_blank := hi
      transition := FiniteControl.restrict W S' hS'
      accept := fun q ↦ q.val.elim (fun _ ↦ false) id }
  refine ⟨N, fun w ↦ ?_⟩
  obtain ⟨c, ⟨n, hn, hr⟩, hc, ha⟩ := h w
  have hrun := (run M read hr).trans (Run.one (finish M read c hc))
  obtain ⟨c', he, ht⟩ := FiniteControl.run W S' hS' hrun hS'.1
  refine ⟨c', ⟨Within.evals ⟨n + 1, ?_, ht⟩⟩, ?_, ?_⟩
  · simpa using Nat.add_le_add_right hn 1
  · apply FiniteControl.halted W S' hS'
    rw [he]
    exact halted M read _ _
  · have hq := congrArg TM0.Cfg.q he
    change c'.q.val = Sum.inr (read c.q c.Tape.head) at hq
    change (c'.q.val.elim (fun _ ↦ false) id = true) ↔ w ∈ L
    simpa only [hq, Sum.elim_inr, id_eq] using ha

end Output

open TM2to1 StackToTape

def bound (C D n t : ℕ) : ℕ :=
  (n + 1 + t * (1 + C * (2 * (n + t * C) + 2))) * D + 1

theorem finite_stack_time (L : Language) (f : Word → Bool)
    (M : TM2ComputableInTime id Computability.encodeBool f)
    (hf : ∀ w, f w = true ↔ w ∈ L) (hfinite : ∀ k, Finite (M.tm.Γ k)) :
    ∃ C D : ℕ, ∃ N : SingleTape, ∀ w : Word, ∃ c : TM0.Cfg N.Γ N.Q,
      Nonempty (StateTransition.EvalsToInTime (TM0.step N.transition)
        (TM0.init (w.map N.input)) (some c) (bound C D w.length (M.time w.length))) ∧
      TM0.step N.transition c = none ∧ (N.accept c.q = true ↔ w ∈ L) := by
  classical
  let tm := M.tm
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  letI : ∀ k, Fintype (tm.Γ k) := fun k ↦ @Fintype.ofFinite _ (hfinite k)
  let A := Γ' tm.K tm.Γ
  let Q := Λ' tm.K tm.Γ tm.Λ tm.σ
  let base : Q → TM1.Stmt A Q tm.σ := tr tm.m
  let Pgm := TapeInput.program tm.k₀ (TM2to1.Λ'.normal tm.main) base
  let S := trSupp tm.m Finset.univ
  have hS : TM1.Supports base S := tr_supports tm.m (supports_univ tm.m)
  have hm : TM2to1.Λ'.normal tm.main ∈ S := hS.1
  letI := TapeInput.startState Q
  let S' := TapeInput.labels S
  have hS' : TM1.Supports Pgm S' := TapeInput.program_supports tm.k₀ _ base hS hm
  let E := TM1to0.tr Pgm
  let ES := TM1to0.trStmts Pgm S'
  have hES : TM0.Supports E (ES : Set (TM1to0.Λ' Pgm)) := TM1to0.tr_supports Pgm hS'
  let C := StackTime.overhead tm
  let D := PostTime.overhead Pgm S'
  let bound : ℕ → ℕ := fun n =>
    (n + 1 + M.time n * (1 + C * (2 * (n + M.time n * C) + 2))) * D
  let input : Bool ↪ A :=
    { toFun := fun b ↦ TapeInput.letter tm.k₀ (M.inputAlphabet.symm b)
      inj' := by
        intro a b h
        have he := congrArg (fun z : A ↦ z.2 tm.k₀) h
        simp only [TapeInput.letter, Function.update_self] at he
        exact M.inputAlphabet.symm.injective (Option.some.inj he) }
  have hi : ∀ b, input b ≠ default := by
    intro b he
    have h := congrArg (fun z : A ↦ z.2 tm.k₀) he
    have hs : (input b).2 tm.k₀ = some (M.inputAlphabet.symm b) := by
      simp [input, TapeInput.letter]
    have hn : (default : A).2 tm.k₀ = none := rfl
    have bad : some (M.inputAlphabet.symm b) = none := hs.symm.trans (h.trans hn)
    contradiction
  let read : TM1to0.Λ' Pgm → A → Bool :=
    fun _ a ↦ ((a.2 tm.k₁).map M.outputAlphabet).getD false
  refine ⟨C, D, ?_⟩
  apply of_supported_time E read ES hES input hi bound L
  intro w
  let u := w.map M.inputAlphabet.symm
  have hu : u.length = w.length := List.length_map _
  have hsrc : Run tm.step (M.outputsFun w).steps
      (initList tm u) (haltList tm [M.outputAlphabet.symm (f w)]) :=
    Run.of_iterate (M.outputsFun w).evals_in_steps
  obtain ⟨c, hc, ⟨t, ht, hrun⟩⟩ := StackTime.run tm.m (StackTime.work_le_overhead tm)
    (StackTime.init_bound tm u) hsrc (input_relation tm u)
  have hout := output_relation tm _ c hc
  have hmirror := TapeInput.run base Pgm Sum.inr (fun _ ↦ rfl) hrun
  have hprep := TapeInput.prepare tm.k₀ (TM2to1.Λ'.normal tm.main) base tm.initialState u
  have hmrun : Within (TM1.step Pgm)
      (w.length + 1 + M.time w.length * (1 + C * (2 * (w.length + M.time w.length * C) + 2)))
      (TM1.init (w.map input)) (TapeInput.cfg Sum.inr c) := by
    obtain ⟨r, hr, hprepare⟩ := hprep
    have hall := hprepare.trans hmirror
    refine ⟨r + t, ?_, ?_⟩
    · have hn := (M.outputsFun w).steps_le_m
      rw [hu] at hr ht
      apply Nat.add_le_add hr
      apply ht.trans
      gcongr <;> exact hn
    · simpa only [u, input, List.map_map] using! hall
  obtain ⟨r, hr, hmacro⟩ := hmrun
  have hstart : (TM1.init (w.map input) : TM1.Cfg A (Sum Bool Q) tm.σ).l ∈
      Finset.insertNone S' := Finset.some_mem_insertNone.mpr hS'.1
  have helem := PostTime.run Pgm hS' hstart hmacro
  refine ⟨TM1to0.trCfg Pgm (TapeInput.cfg Sum.inr c), ?_, ?_, ?_⟩
  · apply helem.mono
    change r * D ≤ bound w.length
    simpa [bound] using Nat.mul_le_mul_right D hr
  · rcases c with ⟨l, v, T⟩
    have hl : l = none := hout.1
    obtain rfl := hl
    rfl
  · change (((c.Tape.head.2 tm.k₁).map M.outputAlphabet).getD false = true) ↔ w ∈ L
    simpa only [hout.2, Option.map_some, Equiv.apply_symm_apply, Option.getD_some] using hf w

end Lax434930Proofs.GeneralTimeSimulation
