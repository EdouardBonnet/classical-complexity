import Lax434930.NondeterministicLogarithmicSpace
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: The complexity classes coNL and coNP
type: definition
---
For a class $\mathcal C$ of binary languages, $\mathrm{co}\mathcal C$
consists of languages whose complements belong to $\mathcal C$.
Complements are taken among all finite binary strings. In particular,
$A\in\mathrm{coNL}$ means $\overline A\in\mathrm{NL}$, and
$A\in\mathrm{coNP}$ means $\overline A\in\mathrm{NP}$.
This operation complements each language; it does not take the set-theoretic
complement of the class of languages.
-/

namespace Lax434930.ComplementClasses

open PolynomialTime NondeterministicLogarithmicSpace NondeterministicPolynomialTime

/-- The class of languages whose complements belong to the given class. -/
def co (C : Set Language) : Set Language := {A | Aᶜ ∈ C}

/-- Complements of languages in NL. -/
def coNL : Set Language := co NL

/-- Complements of languages in NP. -/
def coNP : Set Language := co NP

end Lax434930.ComplementClasses
