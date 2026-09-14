import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths NondeterministicStack
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def mapInstruction {Q R : Type} (f : Q → R) : Instruction K Γ Q → Instruction K Γ R
  | .move d q => .move d (f q)
  | .push k g q => .push k g (f q)
  | .pop k next => .pop k (f ∘ next)
  | .choose next => .choose (f ∘ next)
  | .halt => .halt

def mapConfig {Q R : Type} (f : Q → R) (c : StackMachine.Config K Γ Q) :
    StackMachine.Config K Γ R := ⟨f c.state, c.inputHead, c.store⟩

lemma map_step {Q R : Type} (A : Program K Γ Q) (B : Program K Γ R)
    (f : Q → R) (w : Word) (c d : StackMachine.Config K Γ Q)
    (hc : B.code (f c.state) (readInput w c.inputHead) =
      mapInstruction f (A.code c.state (readInput w c.inputHead)))
    (b : Bool) (hs : (A.resolve b).step w c = some d) :
    (B.resolve b).step w (mapConfig f c) = some (mapConfig f d) := by
  cases he : A.code c.state (readInput w c.inputHead) <;>
    simp [StackMachine.Program.step, Program.resolve, Instruction.resolve, he] at hs
  all_goals subst d; simp [StackMachine.Program.step, Program.resolve, Instruction.resolve, mapConfig, hc, he, mapInstruction, Function.comp_def]

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

def embedInstruction {Q : Type} : StackMachine.Instruction K Γ Q → Instruction K Γ Q
  | .move d q => .move d q
  | .push k g q => .push k g q
  | .pop k next => .pop k next
  | .halt => .halt

lemma resolve_embed {Q : Type} (b : Bool) (i : StackMachine.Instruction K Γ Q) :
    (embedInstruction i).resolve b = i := by
  cases i <;> rfl

def embed (B : StackLanguage.Block K Γ σ) : Block K Γ σ where
  State := B.State
  entry := B.entry
  done := B.done
  code q i := embedInstruction (B.code q i)
  done_halt := by intro q s hs i; rw [B.done_halt q s hs i]; rfl

def compile [Fintype σ] : Command K Γ σ → Block K Γ σ
  | .det c => embed (StackLanguage.compile c)
  | .choose f => atomic (fun s _ => .choose (f s))
  | .seq a b => sequence (compile a) (compile b)
  | .branch test a b => branch test (compile a) (compile b)
  | .loop test body => loop test (compile body)

def Block.point (B : Block K Γ σ) (q : B.State) (d : Data K Γ σ) :
    StackMachine.Config K Γ B.State := ⟨q, d.inputHead, d.store⟩

def Block.Runs (B : Block K Γ σ) (w : Word) (bound : ℕ) (d e : Data K Γ σ) : Prop :=
  Good w bound d ∧ Good w bound e ∧ ∃ q, B.done q = some e.state ∧
    ∃ n, Path (SafeStep (B.program d.state) w bound) n
      (B.point (B.entry d.state) d) (B.point q e)

def Block.Completes (B : Block K Γ σ) (w : Word) (bound : ℕ)
    (s : σ) (d : Data K Γ σ) (post : Data K Γ σ → Prop) : Prop :=
  Tree (B.program s) w bound
    (fun c => ∃ e, B.done c.state = some e.state ∧ B.point c.state e = c ∧ Good w bound e ∧ post e)
    (B.point (B.entry d.state) d)

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
