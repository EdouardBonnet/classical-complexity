import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoicePaths

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths NondeterministicStack
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

lemma Block.lift_tree (A B : Block K Γ σ) (f : A.State → B.State)
    (hc : ∀ q i, A.done q = none → B.code (f q) i = mapInstruction f (A.code q i))
    (w : Word) (bound : ℕ) (s t : σ)
    {post : StackMachine.Config K Γ A.State → Prop}
    {next : StackMachine.Config K Γ B.State → Prop}
    {c : StackMachine.Config K Γ A.State}
    (h : Tree (A.program s) w bound post c)
    (hl : ∀ d, post d → Tree (B.program t) w bound next (mapConfig f d)) :
    Tree (B.program t) w bound next (mapConfig f c) := by
  induction h with
  | leaf _ hp => exact hl _ hp
  | @branch c succ hg hs _ ih =>
    have hd : A.done c.state = none := by
      cases he : A.done c.state with
      | none => rfl
      | some v =>
        have hh := A.done_halt c.state v he (readInput w c.inputHead)
        have hf := hs false
        simp [Block.program, StackMachine.Program.step, Program.resolve, Instruction.resolve, hh] at hf
    exact .branch (fun b => mapConfig f (succ b)) hg
      (fun b => map_step (A.program s) (B.program t) f w c (succ b)
        (hc c.state (readInput w c.inputHead) hd) b (hs b)) ih

lemma Block.jump_tree (B : Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    (d : Data K Γ σ) (q q' : B.State) (hd : Good w bound d)
    (hc : B.code q (readInput w d.inputHead) = .move .stay q')
    {post : StackMachine.Config K Γ B.State → Prop}
    (ht : Tree (B.program s) w bound post (B.point q' d)) :
    Tree (B.program s) w bound post (B.point q d) := by
  apply Tree.branch (c := B.point q d) (fun _ => B.point q' d) hd ?_ (fun _ => ht)
  intro b
  simp [Block.program, Block.point, StackMachine.Program.step, Program.resolve,
    Instruction.resolve, hc, Move.apply, Nat.min_eq_left hd.1]

lemma Block.change_start (B : Block K Γ σ) (w : Word) (bound : ℕ) (s t : σ)
    {post : StackMachine.Config K Γ B.State → Prop} {c : StackMachine.Config K Γ B.State}
    (h : Tree (B.program s) w bound post c) : Tree (B.program t) w bound post c := by
  induction h with
  | leaf hg hp => exact .leaf hg hp
  | branch succ hg hs _ ih => exact .branch succ hg hs ih

lemma Block.completes_mono (B : Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    {d : Data K Γ σ} {post next : Data K Γ σ → Prop}
    (h : B.Completes w bound s d post) (hp : ∀ e, post e → next e) :
    B.Completes w bound s d next := by
  exact h.mono (by
    rintro c ⟨e, he, hpoint, hg, hpost⟩
    exact ⟨e, he, hpoint, hg, hp e hpost⟩)

lemma embed_path_tree (B : StackLanguage.Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    {n : ℕ} {c d : StackMachine.Config K Γ B.State}
    (h : Path (StackMachine.SafeStep (B.program s) w bound) n c d)
    {post : StackMachine.Config K Γ B.State → Prop}
    (ht : Tree ((embed B).program s) w bound post d) :
    Tree ((embed B).program s) w bound post c := by
  induction h with
  | nil => exact ht
  | @cons n c d e he _ ih =>
    apply Tree.branch (fun _ => d) he.2.1 ?_ (fun _ => ih ht)
    intro b
    change (StackMachine.Program.mk (B.entry s)
      (fun q i => (embedInstruction (B.code q i)).resolve b)
      (fun q => (B.done q).isSome)).step w c = some d
    simpa only [resolve_embed] using! he.1

lemma embed_completes (B : StackLanguage.Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    {d e : Data K Γ σ} (h : B.Runs w bound d e) :
    (embed B).Completes w bound s d (fun f => f = e) := by
  obtain ⟨hd, he, q, hq, n, hn⟩ := h
  apply Block.change_start _ w bound d.state s
  apply embed_path_tree B w bound d.state hn
  exact .leaf he ⟨e, hq, rfl, he, rfl⟩

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
