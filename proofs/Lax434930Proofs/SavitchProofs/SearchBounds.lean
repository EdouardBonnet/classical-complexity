import Lax434930Proofs.SavitchProofs.ConfigCount
import Lax434930Proofs.SavitchDefinitions.SearchBounds
import Lax434930Proofs.SavitchDefinitions.ConfigCount
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.BoundedConfigurations Lax434930Proofs.SavitchDefinitions.SearchBounds
open Lax434930.SpaceMachines Lax434930.SpaceBounds

/--
Bound the configuration count by an exponential in $s$, then multiply depth by frame size.
-/
lemma quadratic_stack (M : Machine) :
    ∃ c : ℕ, 0 < c ∧ ∀ n s, logSpace n ≤ s → stackSpace M n s ≤ c * s ^ 2 := by
  let q := Fintype.card M.Q
  let g := Fintype.card M.Γ
  refine ⟨3 * (q + g + 4), by omega, ?_⟩
  intro n s hlog
  have hpos : 0 < s := (Nat.log_pos (by decide : 1 < (2 : ℕ)) (by omega : 2 ≤ n + 2)).trans_le hlog
  have hq : q ≤ 2 ^ q := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  have hn : n + 2 ≤ 2 ^ (logSpace n + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (n + 2)).le
  have hs : s ≤ 2 ^ s := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  have hg : g ^ s ≤ 2 ^ (g * s) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le) s
  have hcard : Fintype.card (Config M n s) ≤ 2 ^ (q + (logSpace n + 1) + s + g * s) := by
    rw [Lax434930Proofs.SavitchProofs.configuration_count]
    calc
      q * (n + 2) * s * g ^ s ≤ 2 ^ q * 2 ^ (logSpace n + 1) * 2 ^ s * 2 ^ (g * s) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hq hn) hs) hg
      _ = _ := by simp only [pow_add]
  have hdepth := Nat.clog_le_of_le_pow hcard
  have hqs : q ≤ q * s := by nlinarith
  have hdepth' : Nat.clog 2 (Fintype.card (Config M n s)) + 1 ≤ (q + g + 4) * s := by
    nlinarith
  have hframe : s + logSpace n + 1 ≤ 3 * s := by omega
  have h := Nat.mul_le_mul hdepth' hframe
  simpa only [stackSpace, pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using h

end Lax434930Proofs.SavitchProofs
