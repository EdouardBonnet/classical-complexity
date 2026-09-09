import Lax554803.PolynomialTime

/-!
---
title: The complexity class P
type: definition
---
A binary language belongs to $\mathrm{P}$ if a deterministic Turing machine
decides membership in polynomial time. We reuse the definition of lax-554803
without modification: input is an ordinary binary string, output is one
Boolean, and one machine and one polynomial work for all inputs.
-/

namespace Lax434930.PolynomialTime

/-- A finite binary string, as in lax-554803. -/
abbrev Word := Lax554803.PolynomialTime.Word

/-- A language of finite binary strings, as in lax-554803. -/
abbrev Language := Lax554803.PolynomialTime.Language

/-- Deterministic polynomial time, exactly as defined in lax-554803. -/
abbrev P : Set Language := Lax554803.PolynomialTime.P

end Lax434930.PolynomialTime
