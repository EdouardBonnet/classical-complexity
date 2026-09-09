import Lax434930.SpaceBounds

/-!
---
title: The complexity class NL
type: definition
---
A binary language belongs to $\mathrm{NL}$ if a nondeterministic Turing
machine decides membership using $O(\log n)$ work space and a separate
read-only input tape. Every branch halts and respects the space bound;
membership means that at least one branch accepts. The bound is
$c\lfloor\log_2(n+2)\rfloor$ for one positive constant $c$.
-/

namespace Lax434930.NondeterministicLogarithmicSpace

open PolynomialTime SpaceBounds

/-- Nondeterministic logarithmic work space. -/
def NL : Set Language :=
  {A | ∃ c : ℕ, 0 < c ∧ A ∈ NSPACE (fun n => c * logSpace n)}

end Lax434930.NondeterministicLogarithmicSpace
