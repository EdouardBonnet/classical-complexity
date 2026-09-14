import Lax434930.LogarithmicSpace
import Lax434930.NondeterministicLogarithmicSpace
import Lax434930.PolynomialSpace
import Lax434930.NondeterministicPolynomialSpace
import Lax434930.ComplementClasses
import Lax434930.ExponentialTime
import Lax434930.PolynomialSpaceEquality

/-!
---
title: The inclusion chain of complexity classes
type: theorem
---
The classical classes satisfy
$\mathrm{L}\subseteq\mathrm{NL}\subseteq\mathrm{P}\subseteq\mathrm{NP}
\subseteq\mathrm{PSPACE}=\mathrm{NPSPACE}\subseteq\mathrm{EXPTIME}$.
-/

namespace Lax434930.BasicProperties

open PolynomialTime LogarithmicSpace NondeterministicLogarithmicSpace
open NondeterministicPolynomialTime PolynomialSpace NondeterministicPolynomialSpace
open ExponentialTime

axiom L_subset_NL : L ⊆ NL

axiom NL_subset_P : NL ⊆ P

axiom P_subset_NP : P ⊆ NP

axiom NP_subset_PSPACE : NP ⊆ PSPACE

axiom NPSPACE_subset_EXPTIME : NPSPACE ⊆ EXPTIME

end Lax434930.BasicProperties
