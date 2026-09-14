import Lax434930.BasicProperties
import Lax434930Proofs.InclusionAux.ConfigurationSearch

namespace Lax434930Proofs

open Lax434930.NondeterministicLogarithmicSpace Lax434930.PolynomialTime

/--
---
conclusion: Lax434930.BasicProperties.NL_subset_P
---
A finite deterministic stack machine computes reachability in a polynomial-size
encoding of the original logarithmic-space machine's configurations.
The checked compiler gives polynomial running time and the original acceptance
definition gives the characteristic function.
-/
theorem NL_subset_P : NL ⊆ P := InclusionAux.NL_subset_P

end Lax434930Proofs
