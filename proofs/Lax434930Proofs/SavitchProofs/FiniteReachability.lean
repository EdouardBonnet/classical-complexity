import Lax434930Proofs.SavitchProofs.Reachability
import Lax434930Proofs.SavitchProofs.ShortPaths
import Lax434930Proofs.SavitchProofs.Reachability

set_option backward.isDefEq.respectTransparency false
namespace Lax434930Proofs.SavitchProofs
open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.Reachability
/--
The recursion covers every simple path because $N\leq 2^{\lceil\log_2 N\rceil}$.
-/
lemma finite_reachability {N : ℕ} (G : Graph N) (a b : Fin N) :
    search G (Nat.clog 2 N) a b = true ↔ Reachable G a b := by
  rw [Lax434930Proofs.SavitchProofs.recursive_reachability]
  constructor
  · rintro ⟨k, _, h⟩
    exact walk_reachable h
  · intro h
    obtain ⟨k, hk, hw⟩ := (Lax434930Proofs.SavitchProofs.short_paths G a b).mp h
    exact ⟨k, (Nat.le_of_lt hk).trans (Nat.le_pow_clog (by decide) N), hw⟩

end Lax434930Proofs.SavitchProofs
