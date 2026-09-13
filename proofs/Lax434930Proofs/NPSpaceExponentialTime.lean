import Lax434930.BasicProperties
import Lax434930Proofs.SpaceExponentialTime

namespace Lax434930Proofs

open Lax434930.PolynomialSpace Lax434930.NondeterministicPolynomialSpace
open Lax434930.ExponentialTime

/--
---
conclusion: Lax434930.BasicProperties.NPSPACE_subset_EXPTIME
assumptions:
  - Lax434930.BasicProperties.PSPACE_eq_NPSPACE
---
Apply the proved Savitch simulation, bound the deterministic machine's run
length by its configuration count, and use the time-bounded stack and tape simulations.
-/
theorem NPSPACE_subset_EXPTIME : NPSPACE ⊆ EXPTIME := by
  intro A h
  apply SpaceExponentialTime.PSPACE_subset_EXPTIME
  rw [Lax434930.BasicProperties.PSPACE_eq_NPSPACE]
  exact h

end Lax434930Proofs
