import Lax434930.SpaceBounds

/-!
---
title: The complexity class PSPACE
type: definition
---
A binary language belongs to $\mathrm{PSPACE}$ if one deterministic Turing
machine decides membership using at most $p(n)$ work cells on inputs of
length $n$, for some polynomial $p\in\mathbb{N}[X]$. The input tape is
read-only and excluded from work space, and the machine always halts.
-/

namespace Lax434930.PolynomialSpace

open PolynomialTime SpaceBounds

/-- Deterministic polynomial work space. -/
def PSPACE : Set Language :=
  {A | ∃ p : Polynomial ℕ, A ∈ DSPACE p.eval}

end Lax434930.PolynomialSpace
