import Lax434930Proofs.SavitchDefinitions.ConfigurationGraph
import Lax434930Proofs.SavitchDefinitions.SpaceConstructibility

set_option backward.isDefEq.respectTransparency false

/-!
The deterministic machine constructs the space bound, encodes configurations,
and evaluates recursive reachability using parallel stacks. Its work space
is quadratic in the original machine's space bound.
-/

namespace Lax434930Proofs.SavitchDefinitions.SearchMachine

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open ConfigurationGraph SpaceConstructibility


end Lax434930Proofs.SavitchDefinitions.SearchMachine
