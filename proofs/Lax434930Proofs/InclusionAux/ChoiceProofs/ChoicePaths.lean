import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceBlocks

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths NondeterministicStack
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

lemma Block.lift_path (A B : Block K Γ σ) (f : A.State → B.State)
    (hc : ∀ q i, A.done q = none → B.code (f q) i = mapInstruction f (A.code q i))
    (w : Word) (bound : ℕ) (s t : σ) {n : ℕ} {a b : StackMachine.Config K Γ A.State}
    (h : Path (SafeStep (A.program s) w bound) n a b) :
    Path (SafeStep (B.program t) w bound) n (mapConfig f a) (mapConfig f b) := by
  induction h with
  | nil => exact .nil _
  | @cons n a b c he hrest ih =>
    have hd : A.done a.state = none := by
      cases ha : A.done a.state with
      | none => rfl
      | some v =>
        have hhalt := A.done_halt a.state v ha (readInput w a.inputHead)
        obtain ⟨b, hs⟩ := he.1
        simp [Block.program, StackMachine.Program.step, Program.resolve, Instruction.resolve, hhalt] at hs
    obtain ⟨choice, hb⟩ := he.1
    have hs := map_step (A.program s) (B.program t) f w a b
      (hc a.state (readInput w a.inputHead) hd) choice hb
    exact .cons ⟨⟨choice, hs⟩, he.2.1, he.2.2⟩ ih

lemma Block.jump (B : Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    (d : Data K Γ σ) (q q' : B.State) (hd : Good w bound d)
    (hc : B.code q (readInput w d.inputHead) = .move .stay q') :
    Path (SafeStep (B.program s) w bound) 1 (B.point q d) (B.point q' d) := by
  refine .cons (b := B.point q' d) ⟨⟨false, ?_⟩, hd, hd⟩ (.nil _)
  simp [Block.program, Block.point, StackMachine.Program.step, Program.resolve, Instruction.resolve, hc, Move.apply, Nat.min_eq_left hd.1]

lemma atomic_runs [Fintype σ] (op : σ → InputSymbol → Instruction K Γ σ)
    (w : Word) (bound : ℕ) (d e : Data K Γ σ) (hd : Good w bound d) (he : Good w bound e)
    (b : Bool) (hs : ((Program.mk d.state op (fun _ => false)).resolve b).step w d = some e) :
    (atomic op).Runs w bound d e := by
  refine ⟨hd, he, (true, e.state), rfl, 1, ?_⟩
  refine .cons (b := (atomic op).point (true, e.state) e) ⟨⟨b, ?_⟩, hd, he⟩ (.nil _)
  cases hop : op d.state (readInput w d.inputHead) <;>
    simp [StackMachine.Program.step, Program.resolve, Instruction.resolve, hop] at hs
  all_goals subst e; simp [Block.program, Block.point, atomic, StackMachine.Program.step, Program.resolve, Instruction.resolve, mapInstruction, hop,
    Function.comp_def]

lemma sequence_runs (A B : Block K Γ σ) (w : Word) (bound : ℕ) {d e f : Data K Γ σ}
    (ha : A.Runs w bound d e) (hb : B.Runs w bound e f) :
    (sequence A B).Runs w bound d f := by
  obtain ⟨hd, he, qa, hqa, na, hna⟩ := ha
  obtain ⟨_, hf, qb, hqb, nb, hnb⟩ := hb
  have hleft := Block.lift_path A (sequence A B) Sum.inl
    (by intro q i hq; simp [sequence, hq]) w bound d.state d.state hna
  have hright := Block.lift_path B (sequence A B) Sum.inr
    (by intro q i _; rfl) w bound e.state d.state hnb
  have hjoin := Block.jump (sequence A B) w bound d.state e (.inl qa) (.inr (B.entry e.state))
    he (by simp [sequence, hqa])
  exact ⟨hd, hf, .inr qb, hqb, na + 1 + nb, (hleft.append hjoin).append hright⟩

lemma branch_true_runs [Fintype σ] (test : σ → Bool) (A B : Block K Γ σ)
    (w : Word) (bound : ℕ) {d e : Data K Γ σ}
    (hp : test d.state = true) (h : A.Runs w bound d e) :
    (branch test A B).Runs w bound d e := by
  obtain ⟨hd, he, q, hq, n, hn⟩ := h
  have hlift := Block.lift_path A (branch test A B) (Sum.inr ∘ Sum.inl)
    (by intro q i _; rfl) w bound d.state d.state hn
  have hstart := Block.jump (branch test A B) w bound d.state d (.inl d.state)
    (.inr (.inl (A.entry d.state))) hd (by simp [branch, hp])
  exact ⟨hd, he, .inr (.inl q), hq, 1 + n, hstart.append hlift⟩

lemma branch_false_runs [Fintype σ] (test : σ → Bool) (A B : Block K Γ σ)
    (w : Word) (bound : ℕ) {d e : Data K Γ σ}
    (hp : test d.state = false) (h : B.Runs w bound d e) :
    (branch test A B).Runs w bound d e := by
  obtain ⟨hd, he, q, hq, n, hn⟩ := h
  have hlift := Block.lift_path B (branch test A B) (Sum.inr ∘ Sum.inr)
    (by intro q i _; rfl) w bound d.state d.state hn
  have hstart := Block.jump (branch test A B) w bound d.state d (.inl d.state)
    (.inr (.inr (B.entry d.state))) hd (by simp [branch, hp])
  exact ⟨hd, he, .inr (.inr q), hq, 1 + n, hstart.append hlift⟩

lemma loop_false_runs [Fintype σ] (test : σ → Bool) (B : Block K Γ σ)
    (w : Word) (bound : ℕ) (d : Data K Γ σ) (hd : Good w bound d)
    (hp : test d.state = false) : (loop test B).Runs w bound d d := by
  exact ⟨hd, hd, .inl d.state, by simp [loop, hp], 0, .nil _⟩

lemma loop_true_runs [Fintype σ] (test : σ → Bool) (B : Block K Γ σ)
    (w : Word) (bound : ℕ) {d e f : Data K Γ σ} (hp : test d.state = true)
    (hbody : B.Runs w bound d e) (hrest : (loop test B).Runs w bound e f) :
    (loop test B).Runs w bound d f := by
  obtain ⟨hd, he, q, hq, n, hn⟩ := hbody
  obtain ⟨_, hf, qf, hqf, nf, hnf⟩ := hrest
  have hlift := Block.lift_path B (loop test B) Sum.inr
    (by intro q i hq; simp [loop, hq]) w bound d.state d.state hn
  have hstart := Block.jump (loop test B) w bound d.state d (.inl d.state)
    (.inr (B.entry d.state)) hd (by simp [loop, hp])
  have hback := Block.jump (loop test B) w bound d.state e (.inr q)
    (.inl e.state) he (by simp [loop, hq])
  exact ⟨hd, hf, qf, hqf, ((1 + n) + 1) + nf,
    ((hstart.append hlift).append hback).append hnf⟩

lemma embed_runs (B : StackLanguage.Block K Γ σ) (w : Word) (bound : ℕ)
    {d e : Data K Γ σ} (h : B.Runs w bound d e) : (embed B).Runs w bound d e := by
  obtain ⟨hd, he, q, hq, n, hn⟩ := h
  refine ⟨hd, he, q, hq, n, hn.map ?_⟩
  intro c f hf
  refine ⟨⟨false, ?_⟩, hf.2⟩
  change (StackMachine.Program.mk (B.entry d.state)
    (fun q i => (embedInstruction (B.code q i)).resolve false)
    (fun q => (B.done q).isSome)).step w c = some f
  simpa only [resolve_embed] using! hf.1

lemma compile_execution [Fintype σ] {w : Word} {bound : ℕ} {c : Command K Γ σ}
    {d e : Data K Γ σ} (h : Exec w bound c d e) : (compile c).Runs w bound d e := by
  induction h with
  | det he => exact embed_runs _ _ _ (StackLanguage.compile_execution he)
  | choose d f b hd =>
    apply atomic_runs _ _ _ d (assigned d (f d.state b)) hd hd b
    simp [StackMachine.Program.step, Program.resolve, Instruction.resolve, assigned,
      StackLanguage.assigned, Move.apply, Nat.min_eq_left hd.1]
  | seq _ _ ih₁ ih₂ => exact sequence_runs _ _ _ _ ih₁ ih₂
  | branch_true hp _ ih => exact branch_true_runs _ _ _ _ _ hp ih
  | branch_false hp _ ih => exact branch_false_runs _ _ _ _ _ hp ih
  | loop_false test body d hd hp => exact loop_false_runs test (compile body) _ _ d hd hp
  | loop_true hp _ _ ih₁ ih₂ => exact loop_true_runs _ _ _ _ hp ih₁ ih₂

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
