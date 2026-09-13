import Lax434930Proofs.SavitchProofs.StackMachine
import Lax434930.SpaceBounds

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open MachinePaths StackMachine
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

inductive Command (K Γ σ : Type) where
  | skip
  | assign (update : σ → σ)
  | input (update : σ → InputSymbol → σ)
  | move (direction : σ → Move)
  | push (stack : σ → K) (symbol : σ → Γ)
  | pop (stack : σ → K) (update : σ → Option Γ → σ)
  | seq (first second : Command K Γ σ)
  | branch (test : σ → Bool) (yes no : Command K Γ σ)
  | loop (test : σ → Bool) (body : Command K Γ σ)

abbrev Data (K Γ σ : Type) := StackMachine.Config K Γ σ

def Good (w : Word) (bound : ℕ) (d : Data K Γ σ) : Prop :=
  StackMachine.Good w bound d

def assigned (d : Data K Γ σ) (s : σ) : Data K Γ σ := ⟨s, d.inputHead, d.store⟩

def moved (w : Word) (d : Data K Γ σ) (direction : Move) : Data K Γ σ :=
  ⟨d.state, min (direction.apply d.inputHead) (w.length + 1), d.store⟩

def pushed (d : Data K Γ σ) (k : K) (g : Γ) : Data K Γ σ :=
  ⟨d.state, d.inputHead, Function.update d.store k (g :: d.store k)⟩

def popped (d : Data K Γ σ) (k : K) (f : σ → Option Γ → σ) : Data K Γ σ :=
  ⟨f d.state (d.store k).head?, d.inputHead, Function.update d.store k (d.store k).tail⟩

inductive Exec (w : Word) (bound : ℕ) : Command K Γ σ → Data K Γ σ → Data K Γ σ → Prop
  | skip (d) (hd : Good w bound d) : Exec w bound .skip d d
  | assign (d) (f : σ → σ) (hd : Good w bound d) :
      Exec w bound (.assign f) d (assigned d (f d.state))
  | input (d) (f : σ → InputSymbol → σ) (hd : Good w bound d) :
      Exec w bound (.input f) d (assigned d (f d.state (readInput w d.inputHead)))
  | move (d) (f : σ → Move) (hd : Good w bound d) :
      Exec w bound (.move f) d (moved w d (f d.state))
  | push (d) (k : σ → K) (g : σ → Γ) (hd : Good w bound d)
      (he : Good w bound (pushed d (k d.state) (g d.state))) :
      Exec w bound (.push k g) d (pushed d (k d.state) (g d.state))
  | pop (d) (k : σ → K) (f : σ → Option Γ → σ) (hd : Good w bound d) :
      Exec w bound (.pop k f) d (popped d (k d.state) f)
  | seq {c₁ c₂ : Command K Γ σ} {d e f : Data K Γ σ} :
      Exec w bound c₁ d e → Exec w bound c₂ e f → Exec w bound (.seq c₁ c₂) d f
  | branch_true {test yes no} {d e : Data K Γ σ} :
      test d.state = true → Exec w bound yes d e → Exec w bound (.branch test yes no) d e
  | branch_false {test yes no} {d e : Data K Γ σ} :
      test d.state = false → Exec w bound no d e → Exec w bound (.branch test yes no) d e
  | loop_false (test : σ → Bool) (body) (d : Data K Γ σ) (hd : Good w bound d) :
      test d.state = false → Exec w bound (.loop test body) d d
  | loop_true {test body} {d e f : Data K Γ σ} :
      test d.state = true → Exec w bound body d e → Exec w bound (.loop test body) e f →
        Exec w bound (.loop test body) d f

lemma Exec.good {w : Word} {bound : ℕ} {c : Command K Γ σ} {d e : Data K Γ σ}
    (h : Exec w bound c d e) : Good w bound d ∧ Good w bound e := by
  induction h with
  | skip _ hd => exact ⟨hd, hd⟩
  | assign _ _ hd => exact ⟨hd, hd⟩
  | input _ _ hd => exact ⟨hd, hd⟩
  | move _ _ hd => exact ⟨hd, min_le_right _ _, hd.2⟩
  | push _ _ _ hd he => exact ⟨hd, he⟩
  | pop d k f hd =>
    refine ⟨hd, hd.1, ?_⟩
    intro j
    by_cases hj : j = k d.state
    · simp [popped, hj]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (hd.2 (k d.state))
    · simpa [popped, Function.update_of_ne hj] using hd.2 j
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | branch_true _ _ ih => exact ih
  | branch_false _ _ ih => exact ih
  | loop_false _ _ _ hd _ => exact ⟨hd, hd⟩
  | loop_true _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

def mapInstruction {Q R : Type} (f : Q → R) : Instruction K Γ Q → Instruction K Γ R
  | .move d q => .move d (f q)
  | .push k g q => .push k g (f q)
  | .pop k next => .pop k (f ∘ next)
  | .halt => .halt

def mapConfig {Q R : Type} (f : Q → R) (c : StackMachine.Config K Γ Q) :
    StackMachine.Config K Γ R := ⟨f c.state, c.inputHead, c.store⟩

lemma map_step {Q R : Type} (A : Program K Γ Q) (B : Program K Γ R)
    (f : Q → R) (w : Word) (c d : StackMachine.Config K Γ Q)
    (hc : B.code (f c.state) (readInput w c.inputHead) =
      mapInstruction f (A.code c.state (readInput w c.inputHead)))
    (hs : A.step w c = some d) : B.step w (mapConfig f c) = some (mapConfig f d) := by
  cases he : A.code c.state (readInput w c.inputHead) <;>
    simp [Program.step, he] at hs
  all_goals subst d; simp [Program.step, mapConfig, hc, he, mapInstruction, Function.comp_def]

structure Block (K Γ σ : Type) where
  State : Type
  [finite : Fintype State]
  entry : σ → State
  done : State → Option σ
  code : State → InputSymbol → Instruction K Γ State
  done_halt : ∀ q s, done q = some s → ∀ i, code q i = .halt

attribute [instance] Block.finite

def Block.program (B : Block K Γ σ) (s : σ) : Program K Γ B.State where
  start := B.entry s
  code := B.code
  accept q := (B.done q).isSome

def atomic [Fintype σ] (op : σ → InputSymbol → Instruction K Γ σ) : Block K Γ σ where
  State := Bool × σ
  entry s := (false, s)
  done q := if q.1 then some q.2 else none
  code q i := if q.1 then .halt else mapInstruction (fun s => (true, s)) (op q.2 i)
  done_halt := by
    intro q s hs i
    cases q with
    | mk b t => cases b <;> simp_all

def sequence (A B : Block K Γ σ) : Block K Γ σ where
  State := A.State ⊕ B.State
  entry s := .inl (A.entry s)
  done q := match q with
    | .inl _ => none
    | .inr q => B.done q
  code q i := match q with
    | .inl q => match A.done q with
        | some s => .move .stay (.inr (B.entry s))
        | none => mapInstruction Sum.inl (A.code q i)
    | .inr q => mapInstruction Sum.inr (B.code q i)
  done_halt := by
    intro q s hs i
    cases q with
    | inl q => simp at hs
    | inr q => simp [B.done_halt q s hs i, mapInstruction]

def branch [Fintype σ] (test : σ → Bool) (A B : Block K Γ σ) : Block K Γ σ where
  State := σ ⊕ (A.State ⊕ B.State)
  entry := Sum.inl
  done q := match q with
    | .inl _ => none
    | .inr (.inl q) => A.done q
    | .inr (.inr q) => B.done q
  code q i := match q with
    | .inl s => .move .stay (if test s then .inr (.inl (A.entry s)) else .inr (.inr (B.entry s)))
    | .inr (.inl q) => mapInstruction (Sum.inr ∘ Sum.inl) (A.code q i)
    | .inr (.inr q) => mapInstruction (Sum.inr ∘ Sum.inr) (B.code q i)
  done_halt := by
    intro q s hs i
    cases q with
    | inl q => simp at hs
    | inr q => cases q with
      | inl q => simp [A.done_halt q s hs i, mapInstruction]
      | inr q => simp [B.done_halt q s hs i, mapInstruction]

def loop [Fintype σ] (test : σ → Bool) (B : Block K Γ σ) : Block K Γ σ where
  State := σ ⊕ B.State
  entry := Sum.inl
  done q := match q with
    | .inl s => if test s then none else some s
    | .inr _ => none
  code q i := match q with
    | .inl s => if test s then .move .stay (.inr (B.entry s)) else .halt
    | .inr q => match B.done q with
        | some s => .move .stay (.inl s)
        | none => mapInstruction Sum.inr (B.code q i)
  done_halt := by
    intro q s hs i
    cases q with
    | inl t => cases h : test t <;> simp_all
    | inr q => simp at hs

def compile [Fintype σ] : Command K Γ σ → Block K Γ σ
  | .skip => atomic (fun s _ => .move .stay s)
  | .assign f => atomic (fun s _ => .move .stay (f s))
  | .input f => atomic (fun s i => .move .stay (f s i))
  | .move f => atomic (fun s _ => .move (f s) s)
  | .push k g => atomic (fun s _ => .push (k s) (g s) s)
  | .pop k f => atomic (fun s _ => .pop (k s) (f s))
  | .seq first second => sequence (compile first) (compile second)
  | .branch test yes no => branch test (compile yes) (compile no)
  | .loop test body => loop test (compile body)

def Block.point (B : Block K Γ σ) (q : B.State) (d : Data K Γ σ) :
    StackMachine.Config K Γ B.State := ⟨q, d.inputHead, d.store⟩

def Block.Runs (B : Block K Γ σ) (w : Word) (bound : ℕ) (d e : Data K Γ σ) : Prop :=
  Good w bound d ∧ Good w bound e ∧ ∃ q, B.done q = some e.state ∧
    ∃ n, Path (SafeStep (B.program d.state) w bound) n
      (B.point (B.entry d.state) d) (B.point q e)

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
        have hs := he.1
        simp [Block.program, Program.step, hhalt] at hs
    have hs := map_step (A.program s) (B.program t) f w a b
      (hc a.state (readInput w a.inputHead) hd) he.1
    exact .cons ⟨hs, he.2.1, he.2.2⟩ ih

lemma Block.jump (B : Block K Γ σ) (w : Word) (bound : ℕ) (s : σ)
    (d : Data K Γ σ) (q q' : B.State) (hd : Good w bound d)
    (hc : B.code q (readInput w d.inputHead) = .move .stay q') :
    Path (SafeStep (B.program s) w bound) 1 (B.point q d) (B.point q' d) := by
  refine .cons (b := B.point q' d) ⟨?_, hd, hd⟩ (.nil _)
  simp [Block.program, Block.point, Program.step, hc, Move.apply, Nat.min_eq_left hd.1]

lemma atomic_runs [Fintype σ] (op : σ → InputSymbol → Instruction K Γ σ)
    (w : Word) (bound : ℕ) (d e : Data K Γ σ) (hd : Good w bound d) (he : Good w bound e)
    (hs : (Program.mk d.state op (fun _ => false)).step w d = some e) :
    (atomic op).Runs w bound d e := by
  refine ⟨hd, he, (true, e.state), rfl, 1, ?_⟩
  refine .cons (b := (atomic op).point (true, e.state) e) ⟨?_, hd, he⟩ (.nil _)
  cases hop : op d.state (readInput w d.inputHead) <;>
    simp [Program.step, hop] at hs
  all_goals subst e; simp [Block.program, Block.point, atomic, Program.step, mapInstruction, hop,
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

lemma compile_execution [Fintype σ] {w : Word} {bound : ℕ} {c : Command K Γ σ}
    {d e : Data K Γ σ} (h : Exec w bound c d e) : (compile c).Runs w bound d e := by
  induction h with
  | skip d hd =>
    apply atomic_runs _ _ _ _ _ hd hd
    simp [Program.step, Move.apply, Nat.min_eq_left hd.1]
  | assign d f hd =>
    apply atomic_runs _ _ _ d (assigned d (f d.state)) hd hd
    simp [Program.step, assigned, Move.apply, Nat.min_eq_left hd.1]
  | input d f hd =>
    apply atomic_runs _ _ _ d (assigned d (f d.state (readInput w d.inputHead))) hd hd
    simp [Program.step, assigned, Move.apply, Nat.min_eq_left hd.1]
  | move d f hd =>
    apply atomic_runs _ _ _ d (moved w d (f d.state)) hd ⟨min_le_right _ _, hd.2⟩
    rfl
  | push d k g hd he =>
    apply atomic_runs _ _ _ _ _ hd he
    rfl
  | pop d k f hd =>
    apply atomic_runs _ _ _ _ _ hd ((Exec.pop d k f hd).good.2)
    rfl
  | seq _ _ ih₁ ih₂ => exact sequence_runs _ _ _ _ ih₁ ih₂
  | branch_true hp _ ih => exact branch_true_runs _ _ _ _ _ hp ih
  | branch_false hp _ ih => exact branch_false_runs _ _ _ _ _ hp ih
  | loop_false test body d hd hp => exact loop_false_runs test (compile body) _ _ d hd hp
  | loop_true hp _ _ ih₁ ih₂ => exact loop_true_runs _ _ _ _ hp ih₁ ih₂

def Block.decider (B : Block K Γ σ) (initial : σ) (answer : σ → Bool) :
    Program K Γ B.State where
  start := B.entry initial
  code := B.code
  accept q := match B.done q with
    | none => false
    | some s => answer s

def machine [Fintype K] [Fintype Γ] [Fintype σ]
    (c : Command K Γ σ) (initial : σ) (answer : σ → Bool) : Machine :=
  StackMachine.compile ((compile c).decider initial answer)

lemma machine_execution [Fintype K] [Fintype Γ] [Fintype σ]
    (c : Command K Γ σ) (initial : σ) (answer : σ → Bool) (w : Word) (bound : ℕ)
    (hb : 0 < bound) (e : Data K Γ σ)
    (h : Exec w bound c ⟨initial, 0, fun _ => []⟩ e) :
    (machine c initial answer).HaltsOn w ∧ (machine c initial answer).UsesSpace w bound ∧
      ((machine c initial answer).Accepts w ↔ answer e.state = true) := by
  obtain ⟨_, _, q, hq, n, hn⟩ := compile_execution h
  let B := compile c
  let P := B.decider initial answer
  have hp : ∃ n, Path (SafeStep P w bound) n P.initial (B.point q e) := ⟨n, hn⟩
  have ht : P.step w (B.point q e) = none := by
    have hhalt := B.done_halt q e.state hq (readInput w e.inputHead)
    simp [P, Block.decider, Program.step, Block.point, hhalt]
  have hr := StackMachine.compile_correct P w bound (B.point q e) hb hp ht
  simpa [P, B, machine, Block.decider, Block.point, hq] using hr

lemma dspace_of_execution [Fintype K] [Fintype Γ] [Fintype σ]
    (c : Command K Γ σ) (initial : σ) (answer : σ → Bool) (bound : ℕ → ℕ)
    (hb : ∀ n, 0 < bound n) (A : Language)
    (h : ∀ w, ∃ e, Exec w (bound w.length) c ⟨initial, 0, fun _ => []⟩ e ∧
      (answer e.state = true ↔ w ∈ A)) : A ∈ Lax434930.SpaceBounds.DSPACE bound := by
  refine ⟨machine c initial answer, StackMachine.deterministic _, ?_, ?_⟩
  · intro w
    obtain ⟨e, he, ha⟩ := h w
    have hm := machine_execution c initial answer w (bound w.length) (hb _) e he
    exact ⟨hm.1, hm.2.2.trans ha⟩
  · intro w
    obtain ⟨e, he, _⟩ := h w
    exact (machine_execution c initial answer w (bound w.length) (hb _) e he).2.1

end

end Lax434930Proofs.SavitchProofs.StackLanguage
