import Lax434930Proofs.InclusionAux.ChoiceProofs.StackMicrocode

set_option backward.isDefEq.respectTransparency false

/-! The stack compiler preserves finite computation trees and accepting paths. -/

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths
open scoped Classical

noncomputable section

variable {K Γ Q : Type}

def Program.initial (P : Program K Γ Q) : StackMachine.Config K Γ Q :=
  ⟨P.start, 0, fun _ => []⟩

def Program.Step (P : Program K Γ Q) (w : Word)
    (c d : StackMachine.Config K Γ Q) : Prop :=
  ∃ b, (P.resolve b).step w c = some d

inductive Tree (P : Program K Γ Q) (w : Word) (bound : ℕ)
    (post : StackMachine.Config K Γ Q → Prop) : StackMachine.Config K Γ Q → Prop
  | leaf {c} : StackMachine.Good w bound c → post c → Tree P w bound post c
  | branch {c} (next : Bool → StackMachine.Config K Γ Q) : StackMachine.Good w bound c →
      (∀ b, (P.resolve b).step w c = some (next b)) →
      (∀ b, Tree P w bound post (next b)) →
      Tree P w bound post c

lemma Tree.good {P : Program K Γ Q} {w : Word} {bound : ℕ}
    {post : StackMachine.Config K Γ Q → Prop} {c : StackMachine.Config K Γ Q}
    (h : Tree P w bound post c) : StackMachine.Good w bound c := by
  cases h <;> assumption

lemma Tree.bind {P : Program K Γ Q} {w : Word} {bound : ℕ}
    {post next : StackMachine.Config K Γ Q → Prop} {c : StackMachine.Config K Γ Q}
    (h : Tree P w bound post c)
    (hn : ∀ d, post d → Tree P w bound next d) : Tree P w bound next c := by
  induction h with
  | leaf _ hp => exact hn _ hp
  | branch next hg hs _ ih => exact Tree.branch next hg hs ih

lemma Tree.mono {P : Program K Γ Q} {w : Word} {bound : ℕ}
    {post next : StackMachine.Config K Γ Q → Prop} {c : StackMachine.Config K Γ Q}
    (h : Tree P w bound post c) (hn : ∀ d, post d → next d) : Tree P w bound next c := by
  induction h with
  | leaf hg hp => exact .leaf hg (hn _ hp)
  | branch succ hg hs _ ih => exact .branch succ hg hs ih

lemma Tree.change_program {A B : Program K Γ Q} (hc : A.code = B.code)
    {w : Word} {bound : ℕ} {post : StackMachine.Config K Γ Q → Prop}
    {c : StackMachine.Config K Γ Q} (h : Tree A w bound post c) : Tree B w bound post c := by
  induction h with
  | leaf hg hp => exact .leaf hg hp
  | branch next hg hs _ ih =>
    apply Tree.branch next hg ?_ ih
    intro b
    simpa only [StackMachine.Program.step, Program.resolve, ← hc] using hs b

variable [Fintype K] [Fintype Γ] [Fintype Q]
variable (P : Program K Γ Q) (w : Word) (bound : ℕ)

lemma instruction_tree (post : (compile P).Config → Prop)
    (c : StackMachine.Config K Γ Q) (hb : 0 < bound) (hc : StackMachine.Good w bound c)
    (ht : ∀ b, ∃ d, (P.resolve b).step w c = some d ∧
      ExecutionTree (compile P) w bound post (encode P d)) :
    ExecutionTree (compile P) w bound post (encode P c) := by
  rcases c with ⟨q, inputHead, store⟩
  rcases hc with ⟨hi, hs⟩
  cases he : P.code q (readInput w inputHead) with
  | halt =>
    obtain ⟨d, hd, _⟩ := ht false
    simp [StackMachine.Program.step, Program.resolve, Instruction.resolve, he] at hd
  | move direction next =>
    obtain ⟨d, hd, htd⟩ := ht false
    simp only [StackMachine.Program.step, Program.resolve, Instruction.resolve, he,
      Option.some.injEq] at hd
    subst d
    exact move_tree P w bound post q next direction inputHead store hb he htd
  | push k g next =>
    obtain ⟨d, hd, htd⟩ := ht false
    simp only [StackMachine.Program.step, Program.resolve, Instruction.resolve, he,
      Option.some.injEq] at hd
    subst d
    exact push_tree P w bound post q next inputHead store k g hi (hs k) he htd
  | pop k next =>
    obtain ⟨d, hd, htd⟩ := ht false
    simp only [StackMachine.Program.step, Program.resolve, Instruction.resolve, he,
      Option.some.injEq] at hd
    subst d
    exact pop_tree P w bound post q next inputHead store k hi (hs k) he htd
  | choose next =>
    apply choose_tree P w bound post q next inputHead store hi hb he
    intro b
    obtain ⟨d, hd, htd⟩ := ht b
    simp only [StackMachine.Program.step, Program.resolve, Instruction.resolve, he,
      Option.some.injEq, Move.apply, Nat.min_eq_left hi] at hd
    subst d
    exact htd

lemma compile_tree {post : StackMachine.Config K Γ Q → Prop}
    {c : StackMachine.Config K Γ Q} (hb : 0 < bound) (h : Tree P w bound post c) :
    ExecutionTree (compile P) w bound (fun d => ∃ e, post e ∧ encode P e = d) (encode P c) := by
  induction h with
  | leaf hg hp => exact .leaf hb ⟨_, hp, rfl⟩
  | branch next hg hs _ ih =>
    apply instruction_tree P w bound _ _ hb hg
    intro b
    exact ⟨next b, hs b, ih b⟩

lemma init_tree (post : (compile P).Config → Prop) (hb : 0 < bound)
    (ht : ExecutionTree (compile P) w bound post (encode P P.initial)) :
    ExecutionTree (compile P) w bound post (compile P).initial := by
  apply local_next P w bound post _
    ⟨.dispatch P.start, (true, fun _ => none), .stay, .stay⟩ hb (by intro b; rfl)
  convert ht using 1
  simp only [encode, Program.initial, located, StackMachine.located, Machine.execute,
    Machine.initial, compile, Move.apply, Nat.min_eq_left (by omega : 0 ≤ w.length + 1)]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [StackMachine.tape, Function.update_apply, hi]

def SafeStep (c d : StackMachine.Config K Γ Q) : Prop :=
  P.Step w c d ∧ StackMachine.Good w bound c ∧ StackMachine.Good w bound d

lemma step_trace {c d : StackMachine.Config K Γ Q} (hb : 0 < bound)
    (hg : StackMachine.Good w bound c) (h : P.Step w c d) :
    Trace (compile P) w bound (encode P c) (encode P d) := by
  obtain ⟨b, hb'⟩ := h
  exact resolved_trace P b w bound (StackMachine.step_trace (P.resolve b) w bound hb hg hb')

lemma path_trace {n : ℕ} {c d : StackMachine.Config K Γ Q} (hb : 0 < bound)
    (h : Path (SafeStep P w bound) n c d) :
    Trace (compile P) w bound (encode P c) (encode P d) := by
  induction h with
  | nil => exact Trace.refl hb
  | cons he _ ih => exact (step_trace P w bound hb he.2.1 he.1).trans ih

lemma compile_halting {post : StackMachine.Config K Γ Q → Prop} (hb : 0 < bound)
    (h : Tree P w bound post P.initial)
    (ht : ∀ c, post c → P.code c.state (readInput w c.inputHead) = .halt) :
    (compile P).HaltsOn w ∧ (compile P).UsesSpace w bound ∧
      ((compile P).Accepts w → ∃ c, post c ∧ P.accept c.state = true) := by
  have hh := (init_tree P w bound _ hb (compile_tree P w bound hb h)).halts (by
    rintro d ⟨c, hc, rfl⟩
    exact terminal P w c (ht c hc))
  refine ⟨hh.1, hh.2.1, ?_⟩
  rintro ⟨n, d, hr, hd, ha⟩
  obtain ⟨c, hc, rfl⟩ := hh.2.2 n d hr hd
  exact ⟨c, hc, ha⟩

lemma compile_accepting {n : ℕ} {c : StackMachine.Config K Γ Q} (hb : 0 < bound)
    (h : Path (SafeStep P w bound) n P.initial c)
    (ht : P.code c.state (readInput w c.inputHead) = .halt)
    (ha : P.accept c.state = true) : (compile P).Accepts w := by
  have hi := resolved_step P false w (StackMachine.init_step (P.resolve false) w)
  have hh := (Trace.single hi hb hb).trans (path_trace P w bound hb h)
  obtain ⟨_, t, hr⟩ := hh
  refine ⟨t, encode P c, ?_, terminal P w c ht, ha⟩
  simpa using (hr.map (fun _ _ he => he.1)).run (Machine.Run.zero (M := compile P) (w := w))

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack
