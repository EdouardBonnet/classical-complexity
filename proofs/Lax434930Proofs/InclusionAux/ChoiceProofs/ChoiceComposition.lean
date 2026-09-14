import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceTrees

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths NondeterministicStack
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

lemma choose_completes [Fintype σ] (f : σ → Bool → σ) (w : Word) (bound : ℕ) (s : σ)
    (d : Data K Γ σ) (hd : Good w bound d) (post : Data K Γ σ → Prop)
    (hp : ∀ b, post (assigned d (f d.state b))) :
    (atomic (fun s _ => .choose (f s))).Completes w bound s d post := by
  let B := atomic (K := K) (Γ := Γ) (fun s _ => .choose (f s))
  apply Tree.branch (c := B.point (B.entry d.state) d)
    (fun b => B.point (true, f d.state b) (assigned d (f d.state b))) hd
  · intro b
    simp [B, atomic, Block.program, Block.point, StackMachine.Program.step, Program.resolve,
      Instruction.resolve, mapInstruction, Function.comp_def, assigned, StackLanguage.assigned,
      Move.apply, Nat.min_eq_left hd.1]
  · intro b
    exact .leaf hd ⟨assigned d (f d.state b), rfl, rfl, hd, hp b⟩

lemma sequence_completes (A B : Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    {d : Data K Γ σ} {post next : Data K Γ σ → Prop}
    (ha : A.Completes w bound s d post)
    (hb : ∀ e, post e → B.Completes w bound s e next) :
    (sequence A B).Completes w bound s d next := by
  apply Block.lift_tree A (sequence A B) Sum.inl
    (by intro q i hq; simp [sequence, hq]) w bound s s ha
  rintro c ⟨e, hq, hpoint, he, hp⟩
  have hr : Tree ((sequence A B).program s) w bound
      (fun c => ∃ f, (sequence A B).done c.state = some f.state ∧
        (sequence A B).point c.state f = c ∧ Good w bound f ∧ next f)
      ((sequence A B).point (.inr (B.entry e.state)) e) := by
    apply Block.lift_tree B (sequence A B) Sum.inr (by intro q i _; rfl)
      w bound s s (hb e hp)
    rintro c' ⟨f, hq', hpoint', hf, hp'⟩
    exact .leaf (by rw [← hpoint']; exact hf)
      ⟨f, hq', congrArg (mapConfig Sum.inr) hpoint', hf, hp'⟩
  have hj := Block.jump_tree (sequence A B) w bound s e (.inl c.state) (.inr (B.entry e.state))
    he (by simp [sequence, hq]) hr
  exact congrArg (mapConfig Sum.inl) hpoint ▸ hj

lemma branch_true_completes [Fintype σ] (test : σ → Bool) (A B : Block K Γ σ)
    (w : Word) (bound : ℕ) (s : σ) {d : Data K Γ σ} {post : Data K Γ σ → Prop}
    (hd : Good w bound d) (hp : test d.state = true) (h : A.Completes w bound s d post) :
    (branch test A B).Completes w bound s d post := by
  apply Block.jump_tree (branch test A B) w bound s d (.inl d.state)
    (.inr (.inl (A.entry d.state))) hd (by simp [branch, hp])
  apply Block.lift_tree A (branch test A B) (Sum.inr ∘ Sum.inl)
    (by intro q i _; rfl) w bound s s h
  rintro c ⟨e, hq, hpoint, he, hp'⟩
  exact .leaf (by rw [← hpoint]; exact he)
    ⟨e, hq, congrArg (mapConfig (Sum.inr ∘ Sum.inl)) hpoint, he, hp'⟩

lemma branch_false_completes [Fintype σ] (test : σ → Bool) (A B : Block K Γ σ)
    (w : Word) (bound : ℕ) (s : σ) {d : Data K Γ σ} {post : Data K Γ σ → Prop}
    (hd : Good w bound d) (hp : test d.state = false) (h : B.Completes w bound s d post) :
    (branch test A B).Completes w bound s d post := by
  apply Block.jump_tree (branch test A B) w bound s d (.inl d.state)
    (.inr (.inr (B.entry d.state))) hd (by simp [branch, hp])
  apply Block.lift_tree B (branch test A B) (Sum.inr ∘ Sum.inr)
    (by intro q i _; rfl) w bound s s h
  rintro c ⟨e, hq, hpoint, he, hp'⟩
  exact .leaf (by rw [← hpoint]; exact he)
    ⟨e, hq, congrArg (mapConfig (Sum.inr ∘ Sum.inr)) hpoint, he, hp'⟩

lemma loop_false_completes [Fintype σ] (test : σ → Bool) (B : Block K Γ σ)
    (w : Word) (bound : ℕ) (s : σ) (d : Data K Γ σ) (post : Data K Γ σ → Prop)
    (hd : Good w bound d) (hp : test d.state = false) (he : post d) :
    (loop test B).Completes w bound s d post := by
  exact .leaf hd ⟨d, by simp [loop, Block.point, hp], rfl, hd, he⟩

lemma loop_true_completes [Fintype σ] (test : σ → Bool) (B : Block K Γ σ)
    (w : Word) (bound : ℕ) (s : σ) {d : Data K Γ σ} {post next : Data K Γ σ → Prop}
    (hd : Good w bound d) (hp : test d.state = true)
    (hbody : B.Completes w bound s d post)
    (hrest : ∀ e, post e → (loop test B).Completes w bound s e next) :
    (loop test B).Completes w bound s d next := by
  apply Block.jump_tree (loop test B) w bound s d (.inl d.state) (.inr (B.entry d.state))
    hd (by simp [loop, hp])
  apply Block.lift_tree B (loop test B) Sum.inr
    (by intro q i hq; simp [loop, hq]) w bound s s hbody
  rintro c ⟨e, hq, hpoint, he, hp'⟩
  have hj := Block.jump_tree (loop test B) w bound s e (.inr c.state) (.inl e.state)
    he (by simp [loop, hq]) (hrest e hp')
  exact congrArg (mapConfig Sum.inr) hpoint ▸ hj

lemma compile_total [Fintype σ] {w : Word} {bound : ℕ} {c : Command K Γ σ}
    {d : Data K Γ σ} (h : Total w bound c d) (s : σ) :
    (compile c).Completes w bound s d (Exec w bound c d) := by
  induction h with
  | det he =>
    apply Block.completes_mono _ w bound s (embed_completes _ w bound s (StackLanguage.compile_execution he))
    intro f hf
    subst f
    exact .det he
  | choose d f hd => exact choose_completes f w bound s d hd _ (fun b => .choose d f b hd)
  | seq ha hb ih₁ ih₂ =>
    apply sequence_completes _ _ w bound s ih₁
    intro e he
    exact Block.completes_mono _ w bound s (ih₂ e he) (fun f hf => .seq he hf)
  | branch_true hp ha ih =>
    apply branch_true_completes _ _ _ w bound s ha.good hp
    exact Block.completes_mono _ w bound s ih (fun e he => .branch_true hp he)
  | branch_false hp ha ih =>
    apply branch_false_completes _ _ _ w bound s ha.good hp
    exact Block.completes_mono _ w bound s ih (fun e he => .branch_false hp he)
  | loop_false test body d hd hp =>
    exact loop_false_completes test _ w bound s d _ hd hp (.loop_false test body d hd hp)
  | loop_true hp ha hb ih₁ ih₂ =>
    apply loop_true_completes _ _ w bound s ha.good hp ih₁
    intro e he
    exact Block.completes_mono _ w bound s (ih₂ e he) (fun f hf => .loop_true hp he hf)

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
