import Lax434930Proofs.SavitchProofs.MachinePaths

set_option backward.isDefEq.respectTransparency false

/-! Finite computation trees for machines with nondeterministic transitions. -/

namespace Lax434930Proofs.InclusionAux.ChoiceProofs

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs.MachinePaths
open scoped Classical

noncomputable section

inductive ExecutionTree (M : Machine) (w : Word) (bound : ℕ)
    (post : M.Config → Prop) : M.Config → Prop
  | leaf {c} : c.workHead < bound → post c → ExecutionTree M w bound post c
  | branch {c} : c.workHead < bound →
      (M.transition c.state (readInput w c.inputHead) (c.tape c.workHead)).Nonempty →
      (∀ a ∈ M.transition c.state (readInput w c.inputHead) (c.tape c.workHead),
        ExecutionTree M w bound post (M.execute w c a)) → ExecutionTree M w bound post c

namespace ExecutionTree

variable {M : Machine} {w : Word} {bound : ℕ} {P Q : M.Config → Prop} {c : M.Config}

lemma good (h : ExecutionTree M w bound P c) : c.workHead < bound := by
  cases h <;> assumption

lemma bind (h : ExecutionTree M w bound P c)
    (hpost : ∀ d, P d → ExecutionTree M w bound Q d) : ExecutionTree M w bound Q c := by
  induction h with
  | leaf _ hp => exact hpost _ hp
  | branch hg hn _ ih => exact .branch hg hn (fun a ha => ih a ha)

lemma mono (h : ExecutionTree M w bound P c) (hpost : ∀ d, P d → Q d) :
    ExecutionTree M w bound Q c := by
  induction h with
  | leaf hg hp => exact .leaf hg (hpost _ hp)
  | branch hg hn _ ih => exact .branch hg hn (fun a ha => ih a ha)

lemma next {d : M.Config} (hc : c.workHead < bound) (he : M.Step w c d)
    (hunique : ∀ e, M.Step w c e → e = d) (hd : ExecutionTree M w bound P d) :
    ExecutionTree M w bound P c := by
  obtain ⟨a, ha, hstep⟩ := he
  refine .branch hc ⟨a, ha⟩ ?_
  intro b hb
  have hh := hunique _ ⟨b, hb, rfl⟩
  exact hh.symm ▸ hd

lemma bounded (h : ExecutionTree M w bound P c)
    (ht : ∀ d, P d → M.Terminal w d) :
    ∃ t, ∀ n d, Path (M.Step w) n c d →
      n ≤ t ∧ d.workHead < bound ∧ (M.Terminal w d → P d) := by
  induction h with
  | leaf hg hp =>
    refine ⟨0, ?_⟩
    intro n d hr
    cases hr with
    | nil => exact ⟨le_rfl, hg, fun _ => hp⟩
    | cons he _ => exact (ht _ hp _ he).elim
  | @branch c hg hn hs ih =>
    let actions := M.transition c.state (readInput w c.inputHead) (c.tape c.workHead)
    let height (a : {a // a ∈ actions}) : ℕ := (ih a.val a.property).choose
    let t := actions.attach.sup height
    refine ⟨t + 1, ?_⟩
    intro n d hr
    cases hr with
    | nil =>
      refine ⟨by omega, hg, ?_⟩
      intro hd
      obtain ⟨a, ha⟩ := hn
      exact (hd _ ⟨a, ha, rfl⟩).elim
    | @cons n _ e _ he hr =>
      obtain ⟨a, ha, rfl⟩ := he
      have hh := (ih a ha).choose_spec n d hr
      have hm : height ⟨a, ha⟩ ≤ t := Finset.le_sup (f := height) (Finset.mem_attach _ _)
      exact ⟨by dsimp [height] at hm; omega, hh.2⟩

lemma halts (h : ExecutionTree M w bound P M.initial)
    (ht : ∀ d, P d → M.Terminal w d) :
    M.HaltsOn w ∧ M.UsesSpace w bound ∧
      ∀ n d, M.Run w n d → M.Terminal w d → P d := by
  obtain ⟨t, ht'⟩ := h.bounded ht
  exact ⟨⟨t, fun n d hr => (ht' n d (run_path hr)).1⟩,
    (fun n d hr => (ht' n d (run_path hr)).2.1),
    fun n d hr => (ht' n d (run_path hr)).2.2⟩

lemma has_leaf (h : ExecutionTree M w bound P c) :
    ∃ n d, Path (M.Step w) n c d ∧ P d := by
  induction h with
  | leaf _ hp => exact ⟨0, _, .nil _, hp⟩
  | branch _ hn _ ih =>
    obtain ⟨a, ha⟩ := hn
    obtain ⟨n, d, hr, hp⟩ := ih a ha
    exact ⟨n + 1, d, .cons ⟨a, ha, rfl⟩ hr, hp⟩

end ExecutionTree

end

end Lax434930Proofs.InclusionAux.ChoiceProofs
