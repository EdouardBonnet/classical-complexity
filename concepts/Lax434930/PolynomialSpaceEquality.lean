import Lax434930.PolynomialSpace
import Lax434930.NondeterministicPolynomialSpace

/-!
---
title: Savitch's theorem
type: theorem
---
The polynomial-space form of Savitch's theorem is
$\mathrm{PSPACE}=\mathrm{NPSPACE}$.
-/

namespace Lax434930.PolynomialSpaceEquality

open PolynomialSpace NondeterministicPolynomialSpace

axiom PSPACE_eq_NPSPACE : PSPACE = NPSPACE

end Lax434930.PolynomialSpaceEquality
