This companion was written for the integrated Mathlib 4.33.0 submission.
There was no pre-existing paper in this repository. The definition paragraphs
are copied from the concept layer without mathematical changes. Proof
paragraphs summarize the corresponding checked Lean proofs. Each annotation
links a definition, a statement, or a proof to its matching formal item.

Statement markers start inside their theorem environments, after the heading.
Proof markers start inside proof environments and end after the explicit QED
marker. Static validation accepts all 40 annotations, and reflow extraction
places every start inside its matching paragraph. This includes the exposed
NL ⊆ P statement and proof at annotations 30 and 31,
NP ⊆ PSPACE at annotations 34 and 35, and
PSPACE = NPSPACE at annotations 36 and 37.
The complete chain is the main theorem; its supporting statements are lemmas.

The marked and unmarked PDFs each have five pages and exactly the same
2,241 body words. The marker package can change vertical spacing and page
breaks; the body-text comparison checks that annotations preserve the text.
Page-number positions were excluded from the body-text comparison.
Direct pdflatex and lualatex checks were used because the installed latexmk
4.76 is older than the archive CLI's required 4.77.
