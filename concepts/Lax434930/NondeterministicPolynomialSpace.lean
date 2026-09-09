import Lax434930.SpaceBounds

/-!
---
title: The complexity class NPSPACE
type: definition
---
A binary language belongs to $\mathrm{NPSPACE}$ if one nondeterministic
Turing machine decides membership using at most $p(n)$ work cells on
every branch on inputs of length $n$, for some polynomial
$p\in\mathbb{N}[X]$. All branches halt; at least one accepts precisely
when the input belongs to the language. The input tape is read-only and
excluded from work space.
-/

namespace Lax434930.NondeterministicPolynomialSpace

open PolynomialTime SpaceBounds

/-- Nondeterministic polynomial work space. -/
def NPSPACE : Set Language :=
  {A | ∃ p : Polynomial ℕ, A ∈ NSPACE p.eval}

end Lax434930.NondeterministicPolynomialSpace
