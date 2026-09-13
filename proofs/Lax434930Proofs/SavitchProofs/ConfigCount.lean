import Lax434930Proofs.SavitchDefinitions.ConfigCount
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions.BoundedConfigurations Lax434930.SpaceMachines

def configurationEquiv (M : Machine) (n s : ℕ) :
    Config M n s ≃ M.Q × Fin (n + 2) × Fin s × (Fin s → M.Γ) where
  toFun c := (c.state, c.inputHead, c.workHead, c.tape)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
Count the four components of a bounded configuration.
-/
lemma configuration_count (M : Machine) (n s : ℕ) :
    Fintype.card (Config M n s) =
      Fintype.card M.Q * (n + 2) * s * Fintype.card M.Γ ^ s := by
  rw [Fintype.card_congr (configurationEquiv M n s)]
  simp [Nat.mul_assoc]

end Lax434930Proofs.SavitchProofs
