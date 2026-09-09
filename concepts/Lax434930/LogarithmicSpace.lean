import Lax434930.SpaceBounds

/-!
---
title: The complexity class L
type: definition
---
A binary language belongs to $\mathrm{L}$ if a deterministic Turing machine
decides membership using $O(\log n)$ work space and a separate read-only
input tape. Precisely, some positive constant $c$ bounds work space by
$c\lfloor\log_2(n+2)\rfloor$ on every input of length $n$.
-/

namespace Lax434930.LogarithmicSpace

open PolynomialTime SpaceBounds

/-- Deterministic logarithmic work space. -/
def L : Set Language :=
  {A | ∃ c : ℕ, 0 < c ∧ A ∈ DSPACE (fun n => c * logSpace n)}

end Lax434930.LogarithmicSpace
