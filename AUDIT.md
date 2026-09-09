# Formalization audit

## Languages and quantifier order

Every class is a `Set Language`, where `Language = Set (List Bool)`, with
exactly the same binary strings as lax-554803. Complements are relative to
all finite binary strings. Every machine and resource polynomial or
constant is chosen before the universally quantified input. None of these
choices may depend on the particular input.

## P, NP, coNP, and EXPTIME

P is definitionally identical to `Lax554803.PolynomialTime.P`. Its
finite-alphabet and single-tape characterizations remain the results of
the dependency. No old proof code is copied or required as a Lake package.

NP is defined by a verifier language in that exact P. Membership requires a
binary certificate whose length is at most `p.eval input.length`. The
verifier's running time is polynomial in the length of the encoded pair.
Encoding is explicit, injective, and has linear length; these claims have
kernel-checked proofs. The explicit certificate length bound is essential:
bounding verification time only in the combined length without bounding
the certificate would define a different class.

The encoding replaces each input bit `b` by `[false, b]`, then appends
`true :: certificate`. A decoder reads two-bit blocks until the first
delimiter. The empty input and empty certificate are supported. Malformed
encodings impose no condition on the verifier language, which is standard
for defining a relation by an encoding.

`co C` means `{ A | Aᶜ ∈ C }`, so coNL and coNP complement the member
languages. In particular, they are not the set complements of NL and NP.
The coNP characterization is proved by negating NP's existential
certificate condition. It retains the same verifier and certificate bound.

EXPTIME uses lax-554803's finite elementary deterministic single-tape
machine and the bound `2 ^ p.eval input.length`. The exponent may have any
fixed polynomial degree: this is EXPTIME/EXP, rather than the smaller E
class with a linear exponent. Acceptance requires reaching a terminal
configuration and reading its Boolean answer. Input is encoded exactly as
in the dependency's single-tape P. The inclusion P ⊆ EXPTIME first invokes
the dependency's proved characterization, then enlarges `p(n)` to
`2 ^ p(n)` without changing the execution certificate.

## Finite local space machines

`Machine.Γ` and `Machine.Q` carry `Fintype` instances. The start state and
blank symbol are fixed data. The input alphabet has four symbols: two
bits and two distinct endmarkers. The transition table has type

```text
Q → InputSymbol → Γ → Finset (Action Γ Q)
```

Thus its domain and range are finite. It cannot inspect the entire input,
work tape, head positions, or input length. There is no oracle, auxiliary
unbounded register, or input-dependent control. Each action writes a
single work symbol and moves each head left, right, or not at all.

The input head starts at the left endmarker, with bits in their original
order at positions 1 through n and the right endmarker at n+1. Clamping a
move to this interval prevents using an unbounded input-head position as
free storage. `inputHead_le` proves this invariant for every run, including
the empty input. Leftward moves at the work tape's position zero remain
at zero. A machine can reserve and mark that cell using its finite work
alphabet.

The work tape is represented mathematically by a function `ℕ → Γ`, but
it is initially the constant blank function and only changes at the
scanned cell. The function representation therefore supplies no hidden
infinite data. `unvisited_tail_blank` proves that every cell beyond a
space bound remains blank at every reachable configuration. The bound
`workHead_le_time` independently checks that the head cannot jump.

The determinism predicate requires at most one action for every local
observation. `deterministic_step` proves that a deterministic machine has
at most one successor configuration. A state may have different actions
for different scanned symbols, as for ordinary Turing machines.

## Acceptance, halting, and space

`Run M w n c` means exactly n legal transitions from the fixed initial
configuration. Runs stop at arbitrary prefixes, not only terminal or
accepting configurations. `Terminal` means that no action gives a
successor. Acceptance requires a reachable terminal configuration with
an accepting control label; a machine with an accepting label that keeps
running has not yet accepted.

For each input, `HaltsOn` requires a finite upper bound on the lengths of
all computation prefixes. On finitely branching computation trees this
is equivalent to all branches halting. No polynomial time bound is
imposed on space deciders. `not_infinite_path` formally verifies that
this condition excludes infinite computation paths. A single accepting
branch cannot hide a nonhalting branch.

`UsesSpace M w s` bounds the work-head position below s at every reachable
configuration on every branch. Since the tape is semi-infinite, starts
at zero, and the head moves by at most one, its visited cells form a
prefix. This definition therefore counts scanned blank cells and cells
later erased, not just current nonblank symbols. Rejecting branches and
unfinished prefixes are included. The initial cell is counted, as
checked by `space_positive`.

The generic DSPACE and NSPACE definitions use exact bounds. The named
logarithmic classes quantify a positive multiplicative constant and use
`floor(log₂(n+2))`; this grows as log n and is at least one, even for n=0.
The polynomial classes quantify a polynomial over the naturals, allowing
constant factors and additive constants. The constant-machine examples
prove that both the empty language and the universal language belong to
L, checking that the definitions are nonvacuous and handle empty inputs.

## Proof scope

The ten annotated proof obligations cover three encoding properties and
seven elementary class properties. The only statement assumption is
`Lax554803.ModelEquivalence.singleTapeP_eq_P`, used by P ⊆ EXPTIME; it is
proved by lax-554803. Every other annotated proof declares an empty
statement-assumption list, checked by the Lax inspector. Definitions do
not use any concept statements.

The three machine-based space definitions beyond L share the same space
machine semantics. NP deliberately uses its standard verifier definition,
and EXPTIME uses the existing single-tape model. Equivalence of these
alternative standard machine presentations, Savitch's theorem, and the
Immerman–Szelepcsényi theorem are outside the proved statements of this
submission. In particular, NPSPACE and coNL are defined by their own
criteria, not identified with PSPACE and NL by an unproved axiom.
