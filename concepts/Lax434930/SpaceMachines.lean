import Lax434930.PolynomialTime
import Mathlib.Data.Finset.Basic

/-!
---
title: Finite Turing machines with a read-only input tape
type: definition
---
A machine has finitely many control states, a finite work alphabet with a
blank symbol, a read-only binary input tape between distinct endmarkers,
and one initially blank, semi-infinite work tape. Both heads start at
position zero, which is the input's left endmarker and the work tape's
leftmost cell. One transition reads the two scanned symbols, writes one
work symbol, changes state, and moves each head by at most one cell.
An outward move at a tape boundary leaves that head in place.

The finite transition table gives a finite set of possible actions for
each state and pair of scanned symbols. A deterministic machine has at
most one action in every such set. A configuration with no successor is
terminal, and its control state supplies an accept/reject bit. Acceptance
means that some computation branch reaches an accepting terminal
configuration. A decider has a finite bound on the lengths of all branches
for each input, and accepts exactly the strings in its language. This
bound need not be computable or satisfy any specified time bound.

Only the work tape is charged as space. Bounding its head below $s$ at
every reachable configuration bounds every visited cell to the prefix
$0,\ldots,s-1$, including blank cells and cells later erased. The input
head is confined to $|x|+2$ positions and cannot act as an unbounded free
counter. The transition table sees neither head position nor the input
length; it sees only the control state and scanned symbols.
-/

namespace Lax434930.SpaceMachines

open PolynomialTime

/-- The input alphabet, with two distinct endmarkers. -/
inductive InputSymbol
  | leftEnd
  | bit (value : Bool)
  | rightEnd
  deriving DecidableEq, Fintype

/-- An elementary head movement, including staying in place. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Fintype

/-- Move a head on a semi-infinite tape, keeping it at zero on a leftward exit. -/
def Move.apply : Move → ℕ → ℕ
  | .left, i => i - 1
  | .stay, i => i
  | .right, i => i + 1

/-- Read the immutable input at a head position, including its endmarkers. -/
def readInput (w : Word) : ℕ → InputSymbol
  | 0 => .leftEnd
  | i + 1 => match w[i]? with
    | some b => .bit b
    | none => .rightEnd

/-- One local transition: change state, write a work symbol, and move the heads. -/
structure Action (Γ Q : Type) where
  state : Q
  write : Γ
  inputMove : Move
  workMove : Move

/-- The complete finite description of a possibly nondeterministic machine. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  blank : Γ
  start : Q
  transition : Q → InputSymbol → Γ → Finset (Action Γ Q)
  accept : Q → Bool

attribute [instance] Machine.alphabet Machine.control

/-- The two head positions, control state, and work-tape contents. -/
structure Configuration (Γ Q : Type) where
  state : Q
  inputHead : ℕ
  workHead : ℕ
  tape : ℕ → Γ

/-- Configurations for a fixed machine. Only reachable configurations are used. -/
abbrev Machine.Config (M : Machine) := Configuration M.Γ M.Q

/-- The work tape is blank; the input is supplied separately to the step relation. -/
def Machine.initial (M : Machine) : M.Config :=
  ⟨M.start, 0, 0, fun _ => M.blank⟩

/-- Execute one action. The input head is clipped to the two endmarkers. -/
def Machine.execute (M : Machine) (w : Word) (c : M.Config)
    (a : Action M.Γ M.Q) : M.Config :=
  ⟨a.state, min (a.inputMove.apply c.inputHead) (w.length + 1),
    a.workMove.apply c.workHead, Function.update c.tape c.workHead a.write⟩

/-- One legal transition consults only the state and the two scanned symbols. -/
def Machine.Step (M : Machine) (w : Word) (c d : M.Config) : Prop :=
  ∃ a ∈ M.transition c.state (readInput w c.inputHead) (c.tape c.workHead),
    d = M.execute w c a

/-- A computation prefix consisting of exactly the indicated number of transitions. -/
inductive Machine.Run (M : Machine) (w : Word) : ℕ → M.Config → Prop
  | zero : M.Run w 0 M.initial
  | succ {n : ℕ} {c d : M.Config} :
      M.Run w n c → M.Step w c d → M.Run w (n + 1) d

/-- No choice of action is available at a terminal configuration. -/
def Machine.Terminal (M : Machine) (w : Word) (c : M.Config) : Prop :=
  ∀ d : M.Config, ¬ M.Step w c d

/-- All computation branches on this input have bounded finite length. -/
def Machine.HaltsOn (M : Machine) (w : Word) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (c : M.Config), M.Run w n c → n ≤ t

/-- Existential acceptance at a terminal configuration. -/
def Machine.Accepts (M : Machine) (w : Word) : Prop :=
  ∃ (n : ℕ) (c : M.Config), M.Run w n c ∧ M.Terminal w c ∧ M.accept c.state = true

/-- A decider halts on every branch and accepts exactly its language. -/
def Machine.Decides (M : Machine) (A : Language) : Prop :=
  ∀ w : Word, M.HaltsOn w ∧ (M.Accepts w ↔ w ∈ A)

/-- The transition table has at most one action for each local observation. -/
def Machine.Deterministic (M : Machine) : Prop :=
  ∀ (q : M.Q) (i : InputSymbol) (b : M.Γ),
    ∀ a ∈ M.transition q i b, ∀ a' ∈ M.transition q i b, a = a'

/-- Every branch stays within the first `s` work cells, whether blank or nonblank. -/
def Machine.UsesSpace (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∀ (n : ℕ) (c : M.Config), M.Run w n c → c.workHead < s

end Lax434930.SpaceMachines
