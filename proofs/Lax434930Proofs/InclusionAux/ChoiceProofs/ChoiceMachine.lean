import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceComposition

set_option backward.isDefEq.respectTransparency false

/-! A terminating structured program defines a nondeterministic space decider. -/

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths NondeterministicStack
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def Block.decider (B : Block K Γ σ) (initial : σ) (answer : σ → Bool) :
    Program K Γ B.State where
  start := B.entry initial
  code := B.code
  accept q := match B.done q with
    | none => false
    | some s => answer s

def machine [Fintype K] [Fintype Γ] [Fintype σ]
    (c : Command K Γ σ) (initial : σ) (answer : σ → Bool) : Machine :=
  NondeterministicStack.compile ((compile c).decider initial answer)

lemma machine_total [Fintype K] [Fintype Γ] [Fintype σ]
    (c : Command K Γ σ) (initial : σ) (answer : σ → Bool) (w : Word) (bound : ℕ)
    (hb : 0 < bound) (ht : Total w bound c ⟨initial, 0, fun _ => []⟩) :
    (machine c initial answer).HaltsOn w ∧ (machine c initial answer).UsesSpace w bound ∧
      ((machine c initial answer).Accepts w ↔
        ∃ e, Exec w bound c ⟨initial, 0, fun _ => []⟩ e ∧ answer e.state = true) := by
  let B := compile c
  let P := B.decider initial answer
  let post (a : StackMachine.Config K Γ B.State) : Prop :=
    ∃ e, B.done a.state = some e.state ∧ B.point a.state e = a ∧ Good w bound e ∧
      Exec w bound c ⟨initial, 0, fun _ => []⟩ e
  have hc := compile_total ht initial
  have htree : Tree P w bound post P.initial := by
    change Tree (B.program initial) w bound post (B.point (B.entry initial) ⟨initial, 0, fun _ => []⟩) at hc
    exact Tree.change_program (A := B.program initial) (B := P) rfl hc
  have hh := compile_halting P w bound hb htree (by
    rintro a ⟨e, he, _, _, _⟩
    exact B.done_halt a.state e.state he _)
  refine ⟨hh.1, hh.2.1, ?_⟩
  constructor
  · intro h
    obtain ⟨a, ⟨e, he, _, _, hex⟩, ha⟩ := hh.2.2 h
    exact ⟨e, hex, by simpa [P, Block.decider, he] using ha⟩
  · rintro ⟨e, he, ha⟩
    obtain ⟨_, _, q, hq, n, hn⟩ := compile_execution he
    apply compile_accepting P w bound hb hn
    · exact B.done_halt q e.state hq _
    · simpa [P, B, Block.decider, Block.point, hq] using ha

lemma nspace_of_execution [Fintype K] [Fintype Γ] [Fintype σ]
    (c : Command K Γ σ) (initial : σ) (answer : σ → Bool) (bound : ℕ → ℕ)
    (hb : ∀ n, 0 < bound n) (A : Language)
    (ht : ∀ w, Total w (bound w.length) c ⟨initial, 0, fun _ => []⟩)
    (hc : ∀ w, (∃ e, Exec w (bound w.length) c ⟨initial, 0, fun _ => []⟩ e ∧
      answer e.state = true) ↔ w ∈ A) : A ∈ Lax434930.SpaceBounds.NSPACE bound := by
  refine ⟨machine c initial answer, ?_, ?_⟩
  · intro w
    have hh := machine_total c initial answer w (bound w.length) (hb _) (ht w)
    exact ⟨hh.1, hh.2.2.trans (hc w)⟩
  · intro w
    exact (machine_total c initial answer w (bound w.length) (hb _) (ht w)).2.1

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
