This companion was written for the integrated Mathlib 4.33.0 submission.
There was no pre-existing paper in this repository. The definition paragraphs
are copied from the concept layer without mathematical changes. Proof
paragraphs summarize the corresponding checked Lean proofs. Each annotation
links a definition, a statement, or a proof to its matching formal item.

Statement markers start inside their theorem environments, after the heading.
Proof markers start inside proof environments and end after the explicit QED
marker. Static validation accepts all 35 annotations, and reflow extraction
places every start inside its matching paragraph. This includes the exposed
PSPACE = NPSPACE statement and its proof, at annotations 31 and 32.

The marked and unmarked PDFs each have five pages and exactly the same
1,973 body words. Their vertical spacing differs: the marker package shifts
the start of the NPSPACE ⊆ EXPTIME proof from page four to page five.
Page-number positions were excluded from the body-text comparison.
Direct pdflatex and lualatex checks were used because the installed latexmk
4.76 is older than the archive CLI's required 4.77.
