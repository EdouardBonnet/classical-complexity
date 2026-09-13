import Lax434930.SpaceMachines
import Mathlib.Data.Fintype.Pi

set_option backward.isDefEq.respectTransparency false

/-!
A configuration using at most $s$ work cells consists of a control state,
an input-head position, a work-head position, and $s$ work symbols.
Cells beyond this prefix are blank.
-/

namespace Lax434930Proofs.SavitchDefinitions.BoundedConfigurations

open Lax434930.SpaceMachines

structure Config (M : Machine) (n s : ℕ) where
  state : M.Q
  inputHead : Fin (n + 2)
  workHead : Fin s
  tape : Fin s → M.Γ
  deriving Fintype

def expand {M : Machine} {n s : ℕ} (c : Config M n s) : M.Config :=
  ⟨c.state, c.inputHead.val, c.workHead.val,
    fun i => if h : i < s then c.tape ⟨i, h⟩ else M.blank⟩

end Lax434930Proofs.SavitchDefinitions.BoundedConfigurations
