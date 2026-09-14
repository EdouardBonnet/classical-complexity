# Mathlib 4.33.0 resubmission status

The class definitions and certificate encoding retain their mathematical
meaning. P's original definition and its supporting machine equivalences and
proofs are incorporated locally. No archive dependency remains.

The intended visible results are L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE ⊆ EXPTIME. Redundant containments and elementary complementation
identities remain internal proof lemmas, not exposed results.

The following requested statements do not yet have formal proofs in this
checkout:

- NL ⊆ P: polynomial-time configuration-graph reachability and its machine implementation.
- NP ⊆ PSPACE: polynomial-space certificate enumeration and verifier simulation.

P ⊆ NP has a new proof using a linear-time certificate-pair projection and
polynomial-time machine composition. Its Lean proof passes. A direct axiom check of this theorem lists
only propext, Classical.choice, and Quot.sound. The class definitions and
certificate encoding match their original declarations after the namespace
change needed to incorporate P.
P ≠ NP remains an explicitly open question and is not used by any proof.

Do not publish as a closed proof network until these two obligations are
proved, unless the user explicitly authorizes a draft with open proof obligations.

Validation: `lax build --replay` passes, including kernel replay and
statement inspection. The closure audit reports
11 of 14 statements closed. The two inclusion obligations and the P versus
NP open question remain. The equality and its use by NPSPACE ⊆ EXPTIME
form a closed, acyclic proof network. The equality has its own concept
to prevent a cycle caused by grouping distinct statements in the display.
Replay, the closure audit, and the browser check all pass for that grouping
(19 concepts, 11 proofs); the rendered graph no longer reports a cycle.
The prescribed audits for the three existing complexity results pass.

Static validation accepts all 35 annotations. Direct PDF compilation
produces five pages, and reflow extraction places all 35 starts inside the
matching paragraphs. Abstract references link to the exact statement
annotations. The installed latexmk is too old for automatic paper compilation;
the PDFs were checked using pdflatex and the reflow using lualatex.
See paper/README.md for the annotation package's effect on page breaks.

PSPACE = NPSPACE is exposed with a proof that has no statement assumptions.
It reuses the Savitch implementation, replacing each former concept axiom
by its checked proof. NPSPACE ⊆ EXPTIME cites this proved equality.
New lemmas bound all halting branches by the finite
configuration count. A concrete stack machine simulates each source
transition in one stack step and clears its stacks before output. The
existing tape simulations retain arbitrary time bounds. All class
definitions remain unchanged.
