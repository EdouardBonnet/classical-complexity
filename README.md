# Classical Complexity Classes

Lax submission `lax-434930`, defining **L, NL, P, NP, coNL, coNP, PSPACE,
NPSPACE, and EXPTIME** as sets of languages of finite binary strings.

The submission builds on [lax-554803](https://laxarchive.org/lax-554803/),
at source commit `289e82d4351fe8c710add0dcbffd0290f016994e` of
[EdouardBonnet/p-complement](https://github.com/EdouardBonnet/p-complement).
It uses Lean `v4.30.0` and mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

| Class | Definition | Concept |
| --- | --- | --- |
| P | The exact P definition from lax-554803 | [PolynomialTime](concepts/Lax434930/PolynomialTime.lean) |
| NP | Polynomially bounded binary certificates, checked by a verifier language in P | [NondeterministicPolynomialTime](concepts/Lax434930/NondeterministicPolynomialTime.lean) |
| coNP | Languages whose complements are in NP | [ComplementClasses](concepts/Lax434930/ComplementClasses.lean) |
| L | Deterministic logarithmic work space | [LogarithmicSpace](concepts/Lax434930/LogarithmicSpace.lean) |
| NL | Nondeterministic logarithmic work space | [NondeterministicLogarithmicSpace](concepts/Lax434930/NondeterministicLogarithmicSpace.lean) |
| coNL | Languages whose complements are in NL | [ComplementClasses](concepts/Lax434930/ComplementClasses.lean) |
| PSPACE | Deterministic polynomial work space | [PolynomialSpace](concepts/Lax434930/PolynomialSpace.lean) |
| NPSPACE | Nondeterministic polynomial work space | [NondeterministicPolynomialSpace](concepts/Lax434930/NondeterministicPolynomialSpace.lean) |
| EXPTIME | Deterministic time bounded by 2 to a polynomial in input length | [ExponentialTime](concepts/Lax434930/ExponentialTime.lean) |

NP uses the standard certificate definition. Its
[pair encoding](concepts/Lax434930/Certificates.lean) doubles each bit of the
input into a two-bit block, adds a delimiter, then appends the certificate.
We prove that decoding recovers both strings, the encoding is injective,
and its length is `2 * input.length + certificate.length + 1`.

The [space machine](concepts/Lax434930/SpaceMachines.lean) has finite control,
a finite work alphabet, a read-only input tape confined between endmarkers,
and one semi-infinite work tape. Its transition table reads only the control
state and scanned symbols. Every branch must halt, and space counts every
work cell visited on every branch, including cells that are blank or later
erased. The logarithmic bound is a constant times `Nat.log 2 (n + 2)`, which
is positive for the empty input.

EXPTIME uses the elementary single-tape machines already defined by
lax-554803. This lets the proof of P ⊆ EXPTIME use that submission's proved
single-tape characterization of P. P itself is an abbreviation for the
original class, so there is no new equivalence obligation for it.

The [basic properties](concepts/Lax434930/BasicProperties.lean) prove
L ⊆ NL, L ⊆ PSPACE, NL ⊆ NPSPACE, PSPACE ⊆ NPSPACE, P ⊆ EXPTIME,
`co (co C) = C`, and the universal-certificate characterization of coNP.
All ten statements in these concepts have proofs. Only P ⊆ EXPTIME uses an
external statement, the proved single-tape characterization from lax-554803.
The remaining proofs have no statement assumptions.

The [P versus NP question](concepts/Lax434930/PVersusNP.lean) states
`P ≠ NP` as the axiom `Lax434930.PVersusNP.P_ne_NP`. It is the submission's
only open statement and is not used by any proof.

The [semantic audit](AUDIT.md) explains the definitions and their scope.
[SpaceSemantics.lean](proofs/Lax434930Proofs/SpaceSemantics.lean) also checks
the input-head bound, blank unvisited work cells, deterministic successor
uniqueness, exclusion of infinite paths, and constant-language deciders.

Run the archive checks with kernel replay from this directory:

```sh
lax build . --replay
```

For incremental proof development:

```sh
cd proofs
lake build
```

The definitions follow the usual conventions explained in
[Jonathan Katz's complexity notes, Lecture 1](https://www.cs.umd.edu/~jkatz/complexity/f05/lecture1.pdf),
particularly the read-only input tape and the certificate definition of NP.
