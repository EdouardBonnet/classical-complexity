import Lax434930Proofs.SavitchProofs.StackLanguage

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ProgramComposition

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open MachinePaths StackMachine
open StackLanguage (mapConfig mapInstruction)
open scoped Classical

noncomputable section

variable {K Γ Q R : Type}

def join (P : Program K Γ Q) (S : Program K Γ R) : Program K Γ (Q ⊕ R) where
  start := .inl P.start
  code q i := match q with
    | .inl q => match P.code q i with
        | .halt => .move .stay (.inr S.start)
        | instruction => mapInstruction Sum.inl instruction
    | .inr q => mapInstruction Sum.inr (S.code q i)
  accept q := match q with
    | .inl _ => false
    | .inr q => S.accept q

lemma join_left (P : Program K Γ Q) (S : Program K Γ R) (q : Q) (i : InputSymbol)
    (h : P.code q i ≠ .halt) :
    (join P S).code (.inl q) i = mapInstruction Sum.inl (P.code q i) := by
  cases he : P.code q i <;> simp_all [join]

lemma lift_path (P : Program K Γ Q) (S : Program K Γ R) (f : Q → R)
    (hc : ∀ q i, P.code q i ≠ .halt → S.code (f q) i = mapInstruction f (P.code q i))
    (w : Word) (bound : ℕ) {n : ℕ} {a b : Config K Γ Q}
    (h : Path (SafeStep P w bound) n a b) :
    Path (SafeStep S w bound) n (mapConfig f a) (mapConfig f b) := by
  induction h with
  | nil => exact .nil _
  | @cons n a b c he _ ih =>
    have hn : P.code a.state (readInput w a.inputHead) ≠ .halt := by
      intro hh
      have hs := he.1
      simp [Program.step, hh] at hs
    exact .cons ⟨StackLanguage.map_step P S f w a b (hc _ _ hn) he.1, he.2.1, he.2.2⟩ ih

lemma path_mono (P : Program K Γ Q) (w : Word) {a b : Config K Γ Q} {n small big : ℕ}
    (hbound : small ≤ big) (h : Path (SafeStep P w small) n a b) : Path (SafeStep P w big) n a b := by
  apply h.map
  intro c d he
  exact ⟨he.1, ⟨he.2.1.1, fun k => (he.2.1.2 k).trans_le hbound⟩,
    ⟨he.2.2.1, fun k => (he.2.2.2 k).trans_le hbound⟩⟩

lemma path_good (P : Program K Γ Q) (w : Word) {a b : Config K Γ Q} {n bound : ℕ}
    (h : Path (SafeStep P w bound) n a b) (ha : Good w bound a) : Good w bound b := by
  induction h with
  | nil => exact ha
  | cons he _ ih => exact ih he.2.2

lemma step_none (P : Program K Γ Q) (w : Word) (c : Config K Γ Q) :
    P.step w c = none ↔ P.code c.state (readInput w c.inputHead) = .halt := by
  cases he : P.code c.state (readInput w c.inputHead) <;> simp [Program.step, he]

variable {σ : Type} [Fintype K] [Fintype Γ] [Fintype Q] [Fintype σ]

def machine (P : Program K Γ Q) (c : StackLanguage.Command K Γ σ) (initial : σ) (answer : σ → Bool) : Machine :=
  StackMachine.compile (join P ((StackLanguage.compile c).decider initial answer))

lemma execution (P : Program K Γ Q) (c : StackLanguage.Command K Γ σ) (initial : σ) (answer : σ → Bool)
    (w : Word) (bound : ℕ) (hb : 0 < bound) (p : Config K Γ Q) (e : StackLanguage.Data K Γ σ)
    (hp : ∃ n, Path (SafeStep P w bound) n P.initial p) (ht : P.step w p = none)
    (hc : StackLanguage.Exec w bound c ⟨initial, p.inputHead, p.store⟩ e) :
    (machine P c initial answer).HaltsOn w ∧ (machine P c initial answer).UsesSpace w bound ∧
      ((machine P c initial answer).Accepts w ↔ answer e.state = true) := by
  let B := StackLanguage.compile c
  let S := B.decider initial answer
  let T := join P S
  let d : StackLanguage.Data K Γ σ := ⟨initial, p.inputHead, p.store⟩
  obtain ⟨hd, _, q, hq, n, hn⟩ := StackLanguage.compile_execution hc
  obtain ⟨np, hp⟩ := hp
  have hl : Path (SafeStep T w bound) np T.initial (mapConfig Sum.inl p) :=
    lift_path P T Sum.inl (join_left P S) w bound hp
  have hr : Path (SafeStep T w bound) n
      (mapConfig Sum.inr (B.point (B.entry initial) d)) (mapConfig Sum.inr (B.point q e)) :=
    lift_path (B.program initial) T Sum.inr (by intros; rfl) w bound hn
  have hj : Path (SafeStep T w bound) 1 (mapConfig Sum.inl p)
      (mapConfig Sum.inr (B.point (B.entry initial) d)) := by
    refine .cons (b := mapConfig Sum.inr (B.point (B.entry initial) d)) ⟨?_, hd, hd⟩ (.nil _)
    have hhalt := (step_none P w p).mp ht
    simp [T, join, Program.step, mapConfig, hhalt, S, StackLanguage.Block.decider,
      StackLanguage.Block.point, d, Move.apply, Nat.min_eq_left hd.1]
  have hfull : ∃ nt, Path (SafeStep T w bound) nt T.initial (mapConfig Sum.inr (B.point q e)) :=
    ⟨np + 1 + n, (hl.append hj).append hr⟩
  have hstop : T.step w (mapConfig Sum.inr (B.point q e)) = none := by
    have hhalt := B.done_halt q e.state hq (readInput w e.inputHead)
    simp [T, join, Program.step, mapConfig, S, StackLanguage.Block.decider,
      StackLanguage.Block.point, hhalt, mapInstruction]
  have hresult := StackMachine.compile_correct T w bound _ hb hfull hstop
  simpa [machine, T, S, B, join, mapConfig, StackLanguage.Block.point, StackLanguage.Block.decider, hq] using hresult

end

end Lax434930Proofs.SavitchProofs.ProgramComposition
