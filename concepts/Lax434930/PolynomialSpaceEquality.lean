import Lax434930.PolynomialSpace
import Lax434930.NondeterministicPolynomialSpace

/-!
---
title: Deterministic and nondeterministic polynomial space coincide
type: lemma
---
Savitch's simulation gives
$\mathrm{PSPACE}=\mathrm{NPSPACE}$.
-/

namespace Lax434930.PolynomialSpaceEquality

open PolynomialSpace NondeterministicPolynomialSpace

axiom PSPACE_eq_NPSPACE : PSPACE = NPSPACE

end Lax434930.PolynomialSpaceEquality
