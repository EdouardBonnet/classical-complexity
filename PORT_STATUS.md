# Mathlib 4.33.0 resubmission status

The class definitions and certificate encoding retain their mathematical
meaning. P's original definition and its supporting machine equivalences and
proofs are incorporated locally. No archive dependency remains.

The intended visible results are L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE ⊆ EXPTIME. Redundant containments and elementary complementation
identities remain internal proof lemmas, not exposed results.

The following requested statement does not yet have a formal proof in this
checkout:

- NL ⊆ P: polynomial-time configuration-graph reachability and its machine implementation.

P ⊆ NP has a new proof using a linear-time certificate-pair projection and
polynomial-time machine composition. Its Lean proof passes. A direct axiom check of this theorem lists
only propext, Classical.choice, and Quot.sound. The class definitions and
certificate encoding match their original declarations after the namespace
change needed to incorporate P.
P ≠ NP remains an explicitly open question and is not used by any proof.

NP ⊆ PSPACE now has a complete proof: a finite nondeterministic machine
generates bounded certificates and simulates the original verifier within
polynomial space; the local Savitch equality gives deterministic polynomial
space. Direct axiom checks of NP ⊆ NPSPACE and its composition with the
actual Savitch proof list only propext, Classical.choice, and Quot.sound.

Do not publish as a closed proof network until NL ⊆ P is proved, unless
the user explicitly authorizes a draft with that proof obligation open.

Validation: `lax build --replay` passes, including kernel replay and
statement inspection. The closure audit reports
12 of 14 statements closed. The NL ⊆ P obligation and the P versus
NP open question remain. The equality and its use by NPSPACE ⊆ EXPTIME
form a closed, acyclic proof network. The equality has its own concept
to prevent a cycle caused by grouping distinct statements in the display.
Replay, the closure audit, and the browser check all pass for that grouping
(19 concepts, 12 proofs); the rendered graph has no cycle.
The prescribed audits for the three existing complexity results pass.

Static validation accepts all 37 annotations. Direct PDF compilation
produces five pages, and reflow extraction places all 37 starts inside the
matching paragraphs. Abstract references link to the exact statement
annotations. The installed latexmk is too old for automatic paper compilation;
the PDFs were checked using pdflatex and the reflow using lualatex.
See paper/README.md for the annotation package's effect on page breaks.

PSPACE = NPSPACE is exposed with a proof that has no statement assumptions.
It reuses the Savitch implementation, replacing each former concept axiom
by its checked proof. Both NP ⊆ PSPACE and NPSPACE ⊆ EXPTIME cite this proved equality.
New lemmas bound all halting branches by the finite
configuration count. A concrete stack machine simulates each source
transition in one stack step and clears its stacks before output. The
existing tape simulations retain arbitrary time bounds. All class
definitions remain unchanged.
