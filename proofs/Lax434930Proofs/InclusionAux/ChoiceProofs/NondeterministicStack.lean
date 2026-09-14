import Lax434930Proofs.InclusionAux.ChoiceProofs.ExecutionTree
import Lax434930Proofs.SavitchProofs.StackMachine

set_option backward.isDefEq.respectTransparency false

/-! Finite stack programs with a local Boolean choice instruction. -/

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths
open scoped Classical

noncomputable section

inductive Instruction (K Γ Q : Type) where
  | move (direction : Move) (next : Q)
  | push (stack : K) (symbol : Γ) (next : Q)
  | pop (stack : K) (next : Option Γ → Q)
  | choose (next : Bool → Q)
  | halt

def Instruction.resolve {K Γ Q : Type} (b : Bool) : Instruction K Γ Q → StackMachine.Instruction K Γ Q
  | .move d q => .move d q
  | .push k g q => .push k g q
  | .pop k q => .pop k q
  | .choose q => .move .stay (q b)
  | .halt => .halt

structure Program (K Γ Q : Type) where
  start : Q
  code : Q → InputSymbol → Instruction K Γ Q
  accept : Q → Bool

def Program.resolve {K Γ Q : Type} (P : Program K Γ Q) (b : Bool) : StackMachine.Program K Γ Q :=
  ⟨P.start, fun q i => (P.code q i).resolve b, P.accept⟩

variable {K Γ Q : Type}

def transition (P : Program K Γ Q) (q : StackMachine.Control K Γ Q) (i : InputSymbol)
    (g : StackMachine.Alphabet K Γ) : Finset (Action (StackMachine.Alphabet K Γ) (StackMachine.Control K Γ Q)) :=
  match StackMachine.action (P.resolve false) q i g, StackMachine.action (P.resolve true) q i g with
  | none, none => ∅
  | some a, none | none, some a => {a}
  | some a, some b => {a, b}

lemma mem_transition (P : Program K Γ Q) (q : StackMachine.Control K Γ Q) (i : InputSymbol)
    (g : StackMachine.Alphabet K Γ) (a : Action (StackMachine.Alphabet K Γ) (StackMachine.Control K Γ Q)) :
    a ∈ transition P q i g ↔
      StackMachine.action (P.resolve false) q i g = some a ∨
      StackMachine.action (P.resolve true) q i g = some a := by
  cases h₀ : StackMachine.action (P.resolve false) q i g <;>
    cases h₁ : StackMachine.action (P.resolve true) q i g <;> simp [transition, h₀, h₁, eq_comm]

variable [Fintype K] [Fintype Γ] [Fintype Q]

def compile (P : Program K Γ Q) : Machine where
  Γ := StackMachine.Alphabet K Γ
  Q := StackMachine.Control K Γ Q
  blank := (false, fun _ => none)
  start := .init
  transition := transition P
  accept q := match q with
    | .dispatch q => P.accept q
    | _ => false

lemma step_of_action (P : Program K Γ Q) (b : Bool) (w : Word) (c : (compile P).Config)
    (a : Action (StackMachine.Alphabet K Γ) (StackMachine.Control K Γ Q))
    (h : StackMachine.action (P.resolve b) c.state (readInput w c.inputHead) (c.tape c.workHead) = some a) :
    (compile P).Step w c ((compile P).execute w c a) := by
  refine ⟨a, ?_, rfl⟩
  apply (mem_transition P _ _ _ a).mpr
  cases b
  · exact Or.inl h
  · exact Or.inr h

lemma resolved_step (P : Program K Γ Q) (b : Bool) (w : Word)
    {c d : (StackMachine.compile (P.resolve b)).Config}
    (h : (StackMachine.compile (P.resolve b)).Step w c d) : (compile P).Step w c d := by
  obtain ⟨a, ha, rfl⟩ := h
  have hact : StackMachine.action (P.resolve b) c.state (readInput w c.inputHead) (c.tape c.workHead) = some a := by
    cases hh : StackMachine.action (P.resolve b) c.state (readInput w c.inputHead) (c.tape c.workHead) with
    | none => exact (Finset.notMem_empty a (by simpa only [StackMachine.compile, hh] using ha)).elim
    | some x =>
      have hx : a = x := Finset.mem_singleton.mp (by simpa only [StackMachine.compile, hh] using ha)
      exact congrArg some hx.symm
  exact step_of_action P b w c a hact

lemma resolved_trace (P : Program K Γ Q) (b : Bool) (w : Word) (bound : ℕ)
    {c d : (StackMachine.compile (P.resolve b)).Config}
    (h : Trace (StackMachine.compile (P.resolve b)) w bound c d) : Trace (compile P) w bound c d := by
  obtain ⟨hc, n, hn⟩ := h
  exact ⟨hc, n, hn.map (fun _ _ he => ⟨resolved_step P b w he.1, he.2⟩)⟩

def located (P : Program K Γ Q) (q : StackMachine.Control K Γ Q) (inputHead workHead : ℕ)
    (store : K → List Γ) : (compile P).Config :=
  StackMachine.located (P.resolve false) q inputHead workHead store

def encode (P : Program K Γ Q) (c : StackMachine.Config K Γ Q) : (compile P).Config :=
  located P (.dispatch c.state) c.inputHead 0 c.store

lemma local_next (P : Program K Γ Q) (w : Word) (bound : ℕ) (post : (compile P).Config → Prop)
    (c : (compile P).Config) (a : Action (StackMachine.Alphabet K Γ) (StackMachine.Control K Γ Q))
    (hc : c.workHead < bound)
    (ha : ∀ b, StackMachine.action (P.resolve b) c.state (readInput w c.inputHead) (c.tape c.workHead) = some a)
    (ht : ExecutionTree (compile P) w bound post ((compile P).execute w c a)) :
    ExecutionTree (compile P) w bound post c := by
  apply ExecutionTree.next hc (step_of_action P false w c a (ha false)) ?_ ht
  intro d hd
  obtain ⟨a', ha', rfl⟩ := hd
  rcases (mem_transition P _ _ _ _).mp ha' with h | h
  · have he : a' = a := Option.some.inj (h.symm.trans (ha false))
    rw [he]
  · have he : a' = a := Option.some.inj (h.symm.trans (ha true))
    rw [he]

lemma terminal (P : Program K Γ Q) (w : Word) (c : StackMachine.Config K Γ Q)
    (hc : P.code c.state (readInput w c.inputHead) = .halt) :
    (compile P).Terminal w (encode P c) := by
  rintro d ⟨a, ha, _⟩
  have hm := (mem_transition P _ _ _ a).mp ha
  simp [encode, located, StackMachine.located, StackMachine.action, Program.resolve, hc,
    Instruction.resolve] at hm

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack
