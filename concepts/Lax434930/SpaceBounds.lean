import Lax434930.SpaceMachines
import Mathlib.Data.Nat.Log

/-!
---
title: Deterministic and nondeterministic space bounds
type: definition
---
For a function $s:\mathbb{N}\to\mathbb{N}$, the classes DSPACE and NSPACE
below use the exact bound $s(n)$ on the number of work cells visited.
There is one machine for all inputs, it halts on every branch, and every
reachable configuration on an input of length $n$ respects the bound.
DSPACE additionally requires deterministic transitions. Constant factors
are quantified explicitly when the classical space classes are defined.
We use $\lfloor\log_2(n+2)\rfloor$ as a positive logarithmic bound, so
empty inputs are included without a special case.
-/

namespace Lax434930.SpaceBounds

open PolynomialTime SpaceMachines

/-- Deterministic deciders using at most `s n` work cells on inputs of length `n`. -/
def DSPACE (s : ℕ → ℕ) : Set Language :=
  {A | ∃ M : Machine, M.Deterministic ∧ M.Decides A ∧
    ∀ w : Word, M.UsesSpace w (s w.length)}

/-- Nondeterministic deciders using at most `s n` work cells on every branch. -/
def NSPACE (s : ℕ → ℕ) : Set Language :=
  {A | ∃ M : Machine, M.Decides A ∧ ∀ w : Word, M.UsesSpace w (s w.length)}

/-- An integer logarithm that is positive even at input length zero. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 (n + 2)

end Lax434930.SpaceBounds
