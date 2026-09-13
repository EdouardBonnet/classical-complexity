import Lax434930.BasicProperties
import Lax434930Proofs.SavitchProofs.Savitch

namespace Lax434930Proofs

open Lax434930.PolynomialSpace Lax434930.NondeterministicPolynomialSpace

/--
---
conclusion: Lax434930.BasicProperties.PSPACE_eq_NPSPACE
assumptions:
---
Deterministic machines are special cases of nondeterministic machines.
Conversely, apply the proved Savitch simulation to the constructible bound
$p(n)+n+2$. Its squared space bound is still polynomial.
-/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE :=
  SavitchProofs.polynomial_space

end Lax434930Proofs
