import Lax434930Proofs.SavitchProofs.Configurations
import Lax434930Proofs.SavitchProofs.PolyBounds
import Lax434930Proofs.SavitchProofs.SearchMachine
import Lax434930Proofs.SavitchDefinitions.Savitch
import Lax434930Proofs.SavitchDefinitions.Acceptance
import Lax434930Proofs.SavitchDefinitions.SearchMachine
import Lax434930Proofs.SavitchDefinitions.PolynomialSpace
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.SpaceConstructibility
open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open Lax434930.PolynomialSpace Lax434930.NondeterministicPolynomialSpace

/--
Apply the deterministic search machine to a space-bounded nondeterministic decider.
-/
theorem savitch (s : ℕ → ℕ) (hs : Constructible s)
    (hlog : ∀ n, logSpace n ≤ s n) (A : Language) :
    A ∈ NSPACE s → ∃ c : ℕ, 0 < c ∧ A ∈ DSPACE (fun n => c * (s n) ^ 2) := by
  rintro ⟨M, hd, hb⟩
  obtain ⟨c, D, hc, hdet, hD, hspace⟩ := Lax434930Proofs.SavitchProofs.search_machine M s hs hlog hb
  refine ⟨c, hc, D, hdet, ?_, hspace⟩
  · intro w
    exact ⟨(hD w).1, (hD w).2.trans ((Lax434930Proofs.SavitchProofs.search_acceptance M w _ (hb w)).trans (hd w).2)⟩

/--
Enlarge the original polynomial bound to $p(n)+n+2$ and square it.
-/
theorem polynomial_space : PSPACE = NPSPACE := by
  ext A
  constructor
  · rintro ⟨p, M, _, hd, hb⟩
    exact ⟨p, M, hd, hb⟩
  · rintro ⟨p, M, hd, hb⟩
    let s := fun n => p.eval n + n + 2
    have hs : Constructible s := Lax434930Proofs.SavitchProofs.polynomial_constructible p
    have hlog : ∀ n, logSpace n ≤ s n := by
      intro n
      have := Nat.log_le_self 2 (n + 2)
      dsimp [logSpace, s]
      omega
    have hA : A ∈ NSPACE s := by
      refine ⟨M, hd, ?_⟩
      intro w t c hr
      have := hb w t c hr
      change c.workHead < p.eval w.length at this
      dsimp [s]
      omega
    obtain ⟨c, _, D, hdet, hD, hbound⟩ := Lax434930Proofs.SavitchProofs.savitch s hs hlog A hA
    refine ⟨Polynomial.C c * (p + Polynomial.X + Polynomial.C 2) ^ 2, D, hdet, hD, ?_⟩
    intro w
    simpa [s] using hbound w

end Lax434930Proofs.SavitchProofs
