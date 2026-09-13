import Lax434930Proofs.SavitchProofs.StackLanguage
import Lax434930Proofs.SavitchDefinitions.SpaceConstructibility

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ParkMachine

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open MachinePaths
open scoped Classical

noncomputable section

def liftAction (M : Machine) (a : Action M.Γ M.Q) : Action M.Γ (Option M.Q) :=
  ⟨some a.state, a.write, a.inputMove, a.workMove⟩

def machine (M : Machine) (marked : M.Γ → Bool) : Machine where
  Γ := M.Γ
  Q := Option M.Q
  blank := M.blank
  start := some M.start
  transition q i g := match q with
    | some q => if M.transition q i g = ∅ then {⟨none, g, .stay, .stay⟩}
        else (M.transition q i g).image (liftAction M)
    | none => if marked g then {⟨none, g, .stay, .right⟩} else ∅
  accept _ := false

def lift (M : Machine) (marked : M.Γ → Bool) (c : M.Config) : (machine M marked).Config :=
  ⟨some c.state, c.inputHead, c.workHead, c.tape⟩

lemma deterministic (M : Machine) (marked : M.Γ → Bool) (hd : M.Deterministic) :
    (machine M marked).Deterministic := by
  intro q i g a ha b hb
  cases q with
  | none =>
    cases h : marked g with
    | false => exact (Finset.notMem_empty a (by simpa only [machine, h, Bool.false_eq_true, reduceIte] using ha)).elim
    | true =>
      have ha' := Finset.mem_singleton.mp (by simpa only [machine, h, reduceIte] using ha)
      have hb' := Finset.mem_singleton.mp (by simpa only [machine, h, reduceIte] using hb)
      exact ha'.trans hb'.symm
  | some q =>
    by_cases h : M.transition q i g = ∅
    · have ha' := Finset.mem_singleton.mp (by simpa only [machine, h, reduceIte] using ha)
      have hb' := Finset.mem_singleton.mp (by simpa only [machine, h, reduceIte] using hb)
      exact ha'.trans hb'.symm
    · have ha' : a ∈ (M.transition q i g).image (liftAction M) := by simpa only [machine, h, reduceIte] using ha
      have hb' : b ∈ (M.transition q i g).image (liftAction M) := by simpa only [machine, h, reduceIte] using hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb'
      rw [hd q i g x hx y hy]

lemma lift_step (M : Machine) (marked : M.Γ → Bool) (w : Word) {c d : M.Config}
    (h : M.Step w c d) : (machine M marked).Step w (lift M marked c) (lift M marked d) := by
  obtain ⟨a, ha, rfl⟩ := h
  have hn : M.transition c.state (readInput w c.inputHead) (c.tape c.workHead) ≠ ∅ := by
    intro he
    simp [he] at ha
  refine ⟨liftAction M a, ?_, ?_⟩
  · simp only [machine, lift, hn, reduceIte]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · simp [lift, Machine.execute, liftAction, machine]

lemma lift_trace (M : Machine) (marked : M.Γ → Bool) (w : Word) (bound : ℕ)
    {c d : M.Config} (h : Trace M w bound c d) :
    Trace (machine M marked) w bound (lift M marked c) (lift M marked d) := by
  obtain ⟨hc, n, hn⟩ := h
  refine ⟨hc, n, ?_⟩
  induction hn with
  | nil => exact .nil _
  | cons he _ ih => exact .cons ⟨lift_step M marked w he.1, he.2⟩ (ih he.2.2)

def position (M : Machine) (marked : M.Γ → Bool) (c : M.Config) (i : ℕ) :
    (machine M marked).Config := ⟨none, c.inputHead, i, c.tape⟩

lemma enter (M : Machine) (marked : M.Γ → Bool) (w : Word) (c : M.Config)
    (hi : c.inputHead ≤ w.length + 1) (ht : M.Terminal w c) :
    (machine M marked).Step w (lift M marked c) (position M marked c c.workHead) := by
  have he : M.transition c.state (readInput w c.inputHead) (c.tape c.workHead) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact ht _ ⟨a, ha, rfl⟩
  refine ⟨⟨none, c.tape c.workHead, .stay, .stay⟩, ?_, ?_⟩
  · simpa only [machine, lift, he, reduceIte] using Finset.mem_singleton_self
      (⟨none, c.tape c.workHead, .stay, .stay⟩ : Action M.Γ (Option M.Q))
  · simp [position, lift, Machine.execute, machine, Move.apply, Nat.min_eq_left hi]

lemma scan (M : Machine) (marked : M.Γ → Bool) (w : Word) (c : M.Config)
    (hi : c.inputHead ≤ w.length + 1) (stop bound : ℕ) (hb : stop < bound)
    (hm : ∀ i < stop, marked (c.tape i) = true) :
    Trace (machine M marked) w bound (position M marked c 0) (position M marked c stop) := by
  induction stop with
  | zero => exact Trace.refl hb
  | succ stop ih =>
    have hp := ih (by omega) (fun i hi => hm i (by omega))
    have hs : (machine M marked).Step w (position M marked c stop)
        (position M marked c (stop + 1)) := by
      refine ⟨⟨none, c.tape stop, .stay, .right⟩, ?_, ?_⟩
      · simpa only [machine, position, hm stop (by omega), reduceIte] using Finset.mem_singleton_self
          (⟨none, c.tape stop, .stay, .right⟩ : Action M.Γ (Option M.Q))
      · simp [position, Machine.execute, machine, Move.apply, Nat.min_eq_left hi]
    exact hp.trans (Trace.single hs (by change stop < bound; omega) hb)

lemma stop_terminal (M : Machine) (marked : M.Γ → Bool) (w : Word) (c : M.Config)
    (stop : ℕ) (hm : marked (c.tape stop) = false) :
    (machine M marked).Terminal w (position M marked c stop) := by
  rintro d ⟨a, ha, _⟩
  exact Finset.notMem_empty a (by simpa only [machine, position, hm, Bool.false_eq_true, reduceIte] using ha)

lemma execution (M : Machine) (marked : M.Γ → Bool) (hd : M.Deterministic)
    (w : Word) (bound : ℕ) (c : M.Config) (stop : ℕ)
    (hi : c.inputHead ≤ w.length + 1) (hh : c.workHead = 0)
    (hb : stop < bound) (htrace : Trace M w bound M.initial c)
    (ht : M.Terminal w c) (hm : ∀ i < stop, marked (c.tape i) = true)
    (he : marked (c.tape stop) = false) :
    (machine M marked).HaltsOn w ∧ (machine M marked).UsesSpace w bound ∧
      ∃ t z, (machine M marked).Run w t z ∧ (machine M marked).Terminal w z ∧
        z.workHead = stop := by
  have hp := lift_trace M marked w bound htrace
  have hc : c.workHead < bound := by rw [hh]; omega
  have hstart := Trace.single (enter M marked w c hi ht) hc hc
  rw [hh] at hstart
  have hfull := (hp.trans hstart).trans (scan M marked w c hi stop bound hb hm)
  have hterminal := stop_terminal M marked w c stop he
  have hdec := trace_decider (deterministic M marked hd) hfull hterminal
  refine ⟨hdec.1, hdec.2.1, ?_⟩
  obtain ⟨_, n, hn⟩ := hfull
  refine ⟨n, position M marked c stop, ?_, hterminal, rfl⟩
  simpa [lift, Machine.initial, machine] using
    (hn.map (fun _ _ h => h.1)).run (Machine.Run.zero (M := machine M marked) (w := w))

variable {K Γ σ : Type} [Fintype K] [Fintype Γ] [Fintype σ]

def stackMachine (code : StackLanguage.Command K Γ σ) (initial : σ) (output : K) : Machine :=
  machine (StackLanguage.machine code initial (fun _ => false)) (fun g => (g.2 output).isSome)

lemma stack_execution (code : StackLanguage.Command K Γ σ) (initial : σ) (output : K)
    (w : Word) (bound : ℕ) (hb : 0 < bound) (e : StackLanguage.Data K Γ σ)
    (h : StackLanguage.Exec w bound code ⟨initial, 0, fun _ => []⟩ e) :
    (stackMachine code initial output).HaltsOn w ∧
      (stackMachine code initial output).UsesSpace w bound ∧
      ∃ t z, (stackMachine code initial output).Run w t z ∧
        (stackMachine code initial output).Terminal w z ∧ z.workHead = (e.store output).length := by
  obtain ⟨_, hg, q, hq, n, hn⟩ := StackLanguage.compile_execution h
  let B := StackLanguage.compile code
  let P := B.decider initial (fun _ => false)
  let c := StackMachine.encode P (B.point q e)
  have hp : MachinePaths.Path (StackMachine.SafeStep P w bound) n P.initial (B.point q e) := hn
  have htrace := (Trace.single (StackMachine.init_step P w) hb hb).trans
    (StackMachine.path_trace P w bound hb hp)
  have ht : P.step w (B.point q e) = none := by
    have hh := B.done_halt q e.state hq (readInput w e.inputHead)
    simp [P, StackLanguage.Block.decider, StackMachine.Program.step, StackLanguage.Block.point, hh]
  apply execution (StackMachine.compile P) (fun g => (g.2 output).isSome)
    (StackMachine.deterministic P) w bound c (e.store output).length hg.1 rfl (hg.2 output) htrace
    (StackMachine.halted_terminal P w (B.point q e) ht)
  · intro i hi
    have hir : i < (e.store output).reverse.length := by simpa using hi
    simp [c, StackMachine.encode, StackMachine.located, StackMachine.tape,
      StackLanguage.Block.point, List.getElem?_eq_getElem hir]
  · simp [c, StackMachine.encode, StackMachine.located, StackMachine.tape, StackLanguage.Block.point]

end

end Lax434930Proofs.SavitchProofs.ParkMachine
