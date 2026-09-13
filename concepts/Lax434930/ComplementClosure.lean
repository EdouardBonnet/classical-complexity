import Lax434930.PolynomialTime

/-!
---
title: P is closed under complement
type: lemma
---
If a language of binary strings belongs to $\mathrm{P}$, then its complement
also belongs to $\mathrm{P}$. The complement is taken in the set of all finite
binary strings.
-/

namespace Lax434930.ComplementClosure

open Lax434930.PolynomialTime

/-- The complement of a polynomial-time decidable language is polynomial-time decidable. -/
axiom closed_under_complement (L : Language) : L ∈ P → Lᶜ ∈ P

end Lax434930.ComplementClosure
