import Lax434930.BasicProperties
import Lax434930Proofs.InclusionAux.NPPolynomialSpace

namespace Lax434930Proofs

open Lax434930.NondeterministicPolynomialTime Lax434930.PolynomialSpace

/--
---
conclusion: Lax434930.BasicProperties.NP_subset_PSPACE
assumptions:
  - Lax434930.PolynomialSpaceEquality.PSPACE_eq_NPSPACE
---
A finite nondeterministic machine guesses a bounded certificate and runs
the original polynomial-time verifier within polynomial work space.
The proved equality of deterministic and nondeterministic polynomial
space then gives the inclusion.
-/
theorem NP_subset_PSPACE : NP ⊆ PSPACE := by
  rw [Lax434930.PolynomialSpaceEquality.PSPACE_eq_NPSPACE]
  exact InclusionAux.NP_subset_NPSPACE

end Lax434930Proofs
