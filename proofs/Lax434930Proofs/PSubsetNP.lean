import Lax434930.BasicProperties
import Lax434930Proofs.CertificateProjection

namespace Lax434930Proofs

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime
open Lax434930.Certificates CertificateProjection

/--
---
conclusion: Lax434930.BasicProperties.P_subset_NP
assumptions:
---
Extract the input from the existing pair encoding in linear time, then run the
polynomial-time decider. The empty certificate suffices for every input.
-/
theorem P_subset_NP : P ⊆ NP := by
  rintro A ⟨f, hf, ⟨M⟩⟩
  obtain ⟨N⟩ := PolynomialComposition.comp computable M
  let V : Language := {w | f (first w) = true}
  refine ⟨V, ⟨f ∘ first, fun _ => Iff.rfl, ⟨N⟩⟩, 0, ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    change f (first (pair x [])) = true
    rw [first_pair]
    exact (hf x).mpr hx
  · rintro ⟨y, _, hy⟩
    change f (first (pair x y)) = true at hy
    rw [first_pair] at hy
    exact (hf x).mp hy

end Lax434930Proofs
