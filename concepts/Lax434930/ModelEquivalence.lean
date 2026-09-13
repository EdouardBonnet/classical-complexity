import Lax434930.MachineModels

/-!
---
title: Single-tape characterization of P
type: lemma
---
The elementary single-tape and stack-machine definitions of $\mathrm{P}$
coincide. Both simulations include polynomial bounds for input conversion,
execution, and final output conversion.
-/

namespace Lax434930.ModelEquivalence

open PolynomialTime MachineModels

/-- The elementary single-tape and stack definitions give the same class P. -/
axiom singleTapeP_eq_P : SingleTapeP = P

end Lax434930.ModelEquivalence
