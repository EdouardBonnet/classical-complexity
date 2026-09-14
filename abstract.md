We formalize the classical complexity classes $\mathrm{L}$, $\mathrm{NL}$,
$\mathrm{P}$, $\mathrm{NP}$, $\mathrm{coNL}$, $\mathrm{coNP}$,
$\mathrm{PSPACE}$, $\mathrm{NPSPACE}$, and $\mathrm{EXPTIME}$ for languages
of finite binary strings. P uses deterministic stack machines, identity
encoding of binary inputs, and singleton Boolean outputs.
NP uses polynomially bounded certificates and polynomial-time verification.
We prove [equivalence with finite single-tape machines](paper.html#m21)
and [closure under complement](paper.html#m23). EXPTIME uses these single-tape machines. The space
classes use finite Turing machines with a bounded, read-only input tape and a
separate work tape, whose space is bounded on every computation branch.
The displayed inclusions are
$\mathrm{L}\subseteq\mathrm{NL}\subseteq\mathrm{P}\subseteq\mathrm{NP}
\subseteq\mathrm{PSPACE}=\mathrm{NPSPACE}\subseteq\mathrm{EXPTIME}$.
The current proofs establish [$\mathrm{L}\subseteq\mathrm{NL}$](paper.html#m27),
[$\mathrm{P}\subseteq\mathrm{NP}$](paper.html#m29),
[$\mathrm{NP}\subseteq\mathrm{PSPACE}$](paper.html#m31),
[$\mathrm{PSPACE}=\mathrm{NPSPACE}$](paper.html#m33), and
[$\mathrm{NPSPACE}\subseteq\mathrm{EXPTIME}$](paper.html#m35);
$\mathrm{NL}\subseteq\mathrm P$ is stated without a proof.
We also state $\mathrm{P}\ne\mathrm{NP}$ as an open question.
