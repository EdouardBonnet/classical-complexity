import Lax434930.LogarithmicSpace
import Lax434930.NondeterministicLogarithmicSpace
import Lax434930.PolynomialSpace
import Lax434930.NondeterministicPolynomialSpace
import Lax434930.ComplementClasses
import Lax434930.ExponentialTime

/-!
---
title: Elementary properties of the complexity classes
type: theorem
---
Deterministic space is contained in nondeterministic space, both for
logarithmic and polynomial bounds. Logarithmic space is contained in
polynomial space, in both settings. Polynomial time is contained in
exponential time. Applying the class operation co twice recovers the
original class, and a language belongs to coNP exactly when every
polynomially bounded certificate is rejected by a suitable P verifier.
-/

namespace Lax434930.BasicProperties

open PolynomialTime LogarithmicSpace NondeterministicLogarithmicSpace
open PolynomialSpace NondeterministicPolynomialSpace ComplementClasses
open ExponentialTime Certificates

axiom L_subset_NL : L ⊆ NL

axiom PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE

axiom L_subset_PSPACE : L ⊆ PSPACE

axiom NL_subset_NPSPACE : NL ⊆ NPSPACE

axiom P_subset_EXPTIME : P ⊆ EXPTIME

axiom co_co (C : Set Language) : co (co C) = C

/-- Universal certificate characterization, with the same explicit encoding as NP. -/
axiom mem_coNP_iff (A : Language) : A ∈ coNP ↔
  ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∀ y : Word, y.length ≤ p.eval x.length → pair x y ∉ V

end Lax434930.BasicProperties
