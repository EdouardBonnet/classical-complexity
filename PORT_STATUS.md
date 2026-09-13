# Mathlib 4.33.0 resubmission status

The class definitions and certificate encoding retain their mathematical
meaning. P's original definition and its supporting machine equivalences and
proofs are incorporated locally. No archive dependency remains.

The intended visible results are L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ NPSPACE ⊆ EXPTIME. Redundant containments and elementary complementation
identities remain internal proof lemmas, not exposed results.

The following requested statements do not yet have formal proofs in this
checkout:

- NL ⊆ P: polynomial-time configuration-graph reachability and its machine implementation.
- NP ⊆ PSPACE: polynomial-space certificate enumeration and verifier simulation.
- NPSPACE ⊆ EXPTIME: a time-bounded deterministic search of bounded configurations.

P ⊆ NP has a new proof using a linear-time certificate-pair projection and
polynomial-time machine composition. The full Lean build passes. A direct axiom check of this new theorem lists
only propext, Classical.choice, and Quot.sound. The class definitions and
certificate encoding match their original declarations after the namespace
change needed to incorporate P.
P ≠ NP remains an explicitly open question and is not used by any proof.

Do not publish as a closed proof network until these three obligations are
proved, unless the user explicitly authorizes a draft with open proof obligations.

Validation: `lax build --replay` compiled both packages and replayed the
kernel proofs successfully. The closure audit reports 10 of 14 statements
closed: the three inclusion obligations and the explicitly open P versus NP
question remain. The prescribed audits for the three existing complexity
results also pass.

The annotated companion compiles to four pages. Static validation accepts
all 33 annotations, and reflow extraction places each annotation start in
the matching paragraph. Abstract references link to the exact statement
annotations. See paper/README.md for the PDF spacing limitation.
