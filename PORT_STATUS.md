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

P ⊆ NP has a new proof using a linear-time certificate-pair projection and
polynomial-time machine composition. The full Lean build passes. A direct axiom check of this new theorem lists
only propext, Classical.choice, and Quot.sound. The class definitions and
certificate encoding match their original declarations after the namespace
change needed to incorporate P.
P ≠ NP remains an explicitly open question and is not used by any proof.

Do not publish as a closed proof network until these two obligations are
proved, unless the user explicitly authorizes a draft with open proof obligations.

Validation: the Lean build and direct axiom checks pass for the new
NPSPACE inclusion. The archive replay was interrupted and must be rerun;
the existing build report predates this proof. The prescribed audits for
the three existing complexity results pass.

Static validation accepts all 35 annotations. The revised PDF and reflow
extraction still need checking after the added NPSPACE proof. Abstract
references link to the exact statement annotations. See paper/README.md
for the previously observed PDF spacing limitation.

NPSPACE ⊆ EXPTIME now has a direct proof with no concept-axiom assumptions.
It reuses the Savitch implementation, replacing each former concept axiom
by its checked proof. New lemmas bound all halting branches by the finite
configuration count. A concrete stack machine simulates each source
transition in one stack step and clears its stacks before output. The
existing tape simulations retain arbitrary time bounds. All class
definitions remain unchanged.
