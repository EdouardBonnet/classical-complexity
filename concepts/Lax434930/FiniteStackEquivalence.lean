import Lax434930.MachineModels

/-!
---
title: Finite stack alphabets suffice
type: lemma
---
Requiring every work-stack alphabet to be finite leaves $\mathrm{P}$ unchanged.
-/

namespace Lax434930.FiniteStackEquivalence

open PolynomialTime MachineModels

/-- Requiring all work alphabets to be finite does not change P. -/
axiom finiteStackP_eq_P : FiniteStackP = P

end Lax434930.FiniteStackEquivalence
