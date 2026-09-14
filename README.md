# Classical Complexity Classes

Lax submission [lax-434930](https://laxarchive.org/lax-434930/), defining **L, NL, P, NP, coNL, coNP, PSPACE,
NPSPACE, and EXPTIME** as sets of languages of finite binary strings.

This submission includes the definition of P, finite machine models, and their
proved equivalences from [lax-554803](https://laxarchive.org/lax-554803/).
It depends only on Mathlib and uses Lean `v4.33.0` with Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

| Class | Definition | Concept |
| --- | --- | --- |
| P | Deterministic polynomial-time stack machines | [PolynomialTime](concepts/Lax434930/PolynomialTime.lean) |
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

EXPTIME uses the elementary single-tape machines defined in this submission.
The proof of P ⊆ EXPTIME uses the proved single-tape characterization of P.
The definition of P is unchanged from the original stack-machine definition.

The [inclusion statements](concepts/Lax434930/BasicProperties.lean) are
L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE ⊆ EXPTIME.
All five adjacent inclusions and the polynomial-space equality are proved.
The [polynomial-space equality](concepts/Lax434930/PolynomialSpaceEquality.lean)
has its own concept and checked proof. The proof network for NPSPACE ⊆ EXPTIME
explicitly points to that equality.
The three certificate-encoding statements and the four incorporated results
about P are proved. All completed proofs use only local statements or Mathlib.
Redundant containments and the elementary complementation identities remain
internal lemmas instead of separately exposed results.

The [P versus NP question](concepts/Lax434930/PVersusNP.lean) states
`P ≠ NP` as the axiom `Lax434930.PVersusNP.P_ne_NP`. It is the submission's
only open question. No proof uses the open question.

The [annotated companion](paper/main.tex) reproduces the class definition text
and links statements and proof summaries to their formal counterparts.

The proof of NPSPACE ⊆ EXPTIME reuses the complete Savitch proof from
[lax-307052](https://laxarchive.org/lax-307052/), source commit
`1062714795609fb441d35a663d6d21fa2fba3a72`. Its auxiliary definitions and
proofs are included locally with attribution; references to its concept
axioms are replaced by the corresponding proved declarations. They depend
on the class definitions, not on the inclusion being proved. This avoids
an archive dependency back to the separate Savitch submission.

The NP ⊆ PSPACE proof constructs a finite nondeterministic certificate
verifier, proves a polynomial bound on every branch's work space, and
uses the local polynomial-space equality. Its nondeterministic stack
compiler and bounded bit generator come from
[lax-733996](https://laxarchive.org/lax-733996/), source commit
`fae3750ccee617c7f97680c6f1ceef3996b3f47e`. These helper proofs are included
locally under the source Apache-2.0 license, with namespace and Mathlib
4.33.0 compatibility edits. They import no statements from that submission.

The NL ⊆ P proof constructs a finite deterministic stack machine for
reachability in a polynomial-size encoding of the original space machine's
configurations. Its bounded loops, tape comparisons, and table updates have
checked polynomial time bounds. The stack compiler and arithmetic routines
reuse closed helpers from [lax-429075](https://laxarchive.org/lax-429075/),
source commit `3481a9cc2e2693124717e398f443f8053629d730`, and
[lax-979537](https://laxarchive.org/lax-979537/), source commit
`82ef67e68fab884dc4cff117a1b871567bdaaafd`. These Apache-2.0 helpers are
included locally with namespace and Mathlib 4.33.0 compatibility edits.
No theorem or concept axiom from either entry is imported.

The [semantic audit](AUDIT.md) explains the definitions and their scope.
[SpaceSemantics.lean](proofs/Lax434930Proofs/SpaceSemantics.lean) also checks
the input-head bound, blank unvisited work cells, deterministic successor
uniqueness, exclusion of infinite paths, and constant-language deciders.

Run the archive checks with kernel replay from this directory:

```sh
lax build . --replay
```

To build the proof package:

```sh
cd proofs
lake build
```

The definitions follow the usual conventions explained in
[Jonathan Katz's complexity notes, Lecture 1](https://www.cs.umd.edu/~jkatz/complexity/f05/lecture1.pdf),
particularly the read-only input tape and the certificate definition of NP.
