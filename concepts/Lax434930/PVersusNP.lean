import Lax434930.PolynomialTime
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: P versus NP
type: open question
---
The P versus NP problem asks whether every language with polynomially
bounded, polynomial-time verifiable certificates can also be decided in
deterministic polynomial time. We state the conjectured separation
$\mathrm{P} \ne \mathrm{NP}$ as an open question.
-/

namespace Lax434930.PVersusNP

open PolynomialTime NondeterministicPolynomialTime

/-- The conjectured separation of P and NP, left as an open question. -/
axiom P_ne_NP : P ≠ NP

end Lax434930.PVersusNP
