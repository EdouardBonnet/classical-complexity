# Mathlib 4.33.0 resubmission status

The full chain is proved:
L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE ⊆ EXPTIME.
The class definitions and certificate encoding are unchanged. P's original
definition and its supporting machine equivalences and proofs are included
locally. No archive dependency remains. Redundant containments and elementary
complementation identities remain internal lemmas.

The local Savitch proof gives PSPACE = NPSPACE without statement assumptions.
NP ⊆ PSPACE and NPSPACE ⊆ EXPTIME explicitly cite this proved equality.
Its separate concept keeps the displayed proof network acyclic.

NL ⊆ P has a concrete polynomial-time configuration-graph search machine.
NP ⊆ PSPACE has a concrete nondeterministic certificate-verification machine
with a polynomial bound on every branch's work space. The class definitions
are the same models used by both constructions. Direct axiom checks of the
new implementations list only `propext`, `Classical.choice`, and `Quot.sound`.

`lax build --replay` passes compilation, kernel replay, and statement
inspection: 19 concepts and 13 proofs. The closure audit reports all 13
results closed. Its only open entry is the explicitly labelled P ≠ NP
question, which no proof uses. The prescribed audits of the existing
Savitch, Immerman–Szelepcsényi, and Cook–Levin submissions pass.

Static validation accepts all 40 annotations. The marked and unmarked PDFs
each have five pages and identical body text. Reflow extraction places all
annotation starts inside their matching paragraphs, and abstract references
target the exact statement annotations. Direct pdflatex and lualatex checks
were used because the installed latexmk 4.76 is older than the archive CLI's
required 4.77. See [paper/README.md](paper/README.md).
