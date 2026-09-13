import Lax434930Proofs.SavitchProofs.Configurations
import Lax434930Proofs.SavitchProofs.ConstructedSearch
import Lax434930Proofs.SavitchDefinitions.SearchMachine
import Lax434930Proofs.SavitchDefinitions.Acceptance

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.SpaceConstructibility
open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds

/--
Compose the space constructor, configuration query, and stack search.
The stack compiler supplies a deterministic machine in the original tape model.
-/
lemma search_machine (M : Machine) (s : ℕ → ℕ) (hs : Constructible s)
    (hlog : ∀ n, logSpace n ≤ s n)
    (hM : ∀ w, M.UsesSpace w (s w.length)) :
    ∃ (c : ℕ) (D : Machine), 0 < c ∧ D.Deterministic ∧
      (∀ w, D.HaltsOn w ∧ (D.Accepts w ↔ ConfigurationGraph.SearchAccepts M w (s w.length))) ∧
      ∀ w, D.UsesSpace w (c * (s w.length) ^ 2) := by
  obtain ⟨B, hdet, hB⟩ := hs
  refine ⟨ConstructedSearch.spaceConstant M, ConstructedSearch.machine M B,
    ConstructedSearch.spaceConstant_pos M, ConstructedSearch.deterministic M B, ?_, ?_⟩
  · intro w
    have he := ConstructedSearch.execution M B w (s w.length) hdet
      (hB w).2.1 (hB w).2.2 (hlog _) (hM w)
    exact ⟨he.1, he.2.2.trans (Lax434930Proofs.SavitchProofs.search_acceptance M w _ (hM w)).symm⟩
  · intro w t c hc
    have he := ConstructedSearch.execution M B w (s w.length) hdet
      (hB w).2.1 (hB w).2.2 (hlog _) (hM w)
    have hpos : 0 < s w.length := hM w 0 M.initial .zero
    exact (he.2.1 t c hc).trans_le (ConstructedSearch.quadratic M _ hpos)

end Lax434930Proofs.SavitchProofs
