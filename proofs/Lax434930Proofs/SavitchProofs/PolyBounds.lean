import Lax434930Proofs.SavitchProofs.PolynomialConstructor
import Lax434930Proofs.SavitchDefinitions.PolyBounds

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions.SpaceConstructibility

/--
Count the input, append each polynomial term using nested counters, and scan
the output track to halt at position $p(n)+n+1$.
-/
lemma polynomial_constructible (p : Polynomial ℕ) :
    Constructible (fun n => p.eval n + n + 2) := by
  refine ⟨UnaryPolynomial.constructor p, ?_, UnaryPolynomial.constructor_execution p⟩
  exact ParkMachine.deterministic _ _ (StackMachine.deterministic _)

end Lax434930Proofs.SavitchProofs
