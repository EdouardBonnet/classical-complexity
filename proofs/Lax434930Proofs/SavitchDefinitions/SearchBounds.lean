import Lax434930Proofs.SavitchDefinitions.ConfigurationGraph
import Lax434930.SpaceBounds

set_option backward.isDefEq.respectTransparency false

/-!
The number of recursion frames is logarithmic in the configuration count.
Multiplying this depth by the space for configurations and counters gives
$O(s^2)$ when $s$ bounds the input logarithm.
-/

namespace Lax434930Proofs.SavitchDefinitions.SearchBounds

open Lax434930.SpaceMachines Lax434930.SpaceBounds BoundedConfigurations

def stackSpace (M : Machine) (n s : ℕ) : ℕ :=
  (Nat.clog 2 (Fintype.card (Config M n s)) + 1) * (s + logSpace n + 1)


end Lax434930Proofs.SavitchDefinitions.SearchBounds
