import Lax434930Proofs.SavitchProofs.FiniteReachability
import Lax434930Proofs.SavitchDefinitions.Runs
import Lax434930Proofs.SavitchDefinitions.Acceptance
import Lax434930Proofs.SavitchDefinitions.FiniteSearch
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.BoundedConfigurations Lax434930Proofs.SavitchDefinitions.ConfigurationGraph
open Lax434930Proofs.SavitchDefinitions.Reachability Lax434930.PolynomialTime Lax434930.SpaceMachines

lemma input_bound {M : Machine} {w : Word} {t : ℕ} {c : M.Config}
    (hr : M.Run w t c) : c.inputHead ≤ w.length + 1 := by
  induction hr with
  | zero => exact Nat.zero_le _
  | succ _ hs _ =>
    obtain ⟨a, _, rfl⟩ := hs
    exact min_le_right _ _

lemma tail_blank {M : Machine} {w : Word} {s t : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hr : M.Run w t c) (i : ℕ) (hi : s ≤ i) :
    c.tape i = M.blank := by
  induction hr with
  | zero => rfl
  | @succ n c d hr he ih =>
    obtain ⟨a, _, rfl⟩ := he
    have hc := hs n c hr
    change Function.update c.tape c.workHead a.write i = M.blank
    rw [Function.update_of_ne (by omega : i ≠ c.workHead)]
    exact ih

def pack {M : Machine} {w : Word} {s t : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hr : M.Run w t c) : Config M w.length s where
  state := c.state
  inputHead := ⟨c.inputHead, by have := input_bound hr; omega⟩
  workHead := ⟨c.workHead, hs t c hr⟩
  tape i := c.tape i

@[simp] lemma expand_pack {M : Machine} {w : Word} {s t : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hr : M.Run w t c) : expand (pack hs hr) = c := by
  have ht := tail_blank hs hr
  cases c with
  | mk q i j f =>
    simp only [pack, expand]
    congr 1
    funext k
    split_ifs with hk
    · rfl
    · exact (ht k (by omega)).symm

lemma graph_edge (M : Machine) (w : Word) (s : ℕ) (a b : Config M w.length s) :
    graph M w s (numbering M w.length s a) (numbering M w.length s b) = true ↔
      M.Step w (expand a) (expand b) := by
  classical
  simp [graph]

lemma encoded_run {M : Machine} {w : Word} {s t : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hr : M.Run w t c) :
    Reachable (graph M w s) (numbering M w.length s (pack hs .zero))
      (numbering M w.length s (pack hs hr)) := by
  induction hr with
  | zero => exact .refl
  | succ hr he ih =>
    apply ih.tail
    rw [graph_edge, expand_pack, expand_pack]
    exact he

lemma decoded_path {M : Machine} {w : Word} {s : ℕ}
    {a b : Fin (Fintype.card (Config M w.length s))}
    (h : Reachable (graph M w s) a b) :
    (∃ t, M.Run w t (expand ((numbering M w.length s).symm a))) →
    ∃ t, M.Run w t (expand ((numbering M w.length s).symm b)) := by
  induction h with
  | refl => exact id
  | tail _ he ih =>
    intro h₀
    obtain ⟨t, ht⟩ := ih h₀
    exact ⟨t + 1, .succ ht (by simpa [graph] using he)⟩

/--
Encode each reachable configuration by its bounded tape prefix and decode each graph edge.
-/
lemma configuration_acceptance (M : Machine) (w : Word) (s : ℕ)
    (hs : M.UsesSpace w s) : AcceptsBounded M w s ↔ M.Accepts w := by
  constructor
  · rintro ⟨a, b, ha, hb, haccept, hpath⟩
    have hstart : ∃ t, M.Run w t (expand ((numbering M w.length s).symm
        (numbering M w.length s a))) := by
      simpa [ha] using (show ∃ t, M.Run w t M.initial from ⟨0, .zero⟩)
    obtain ⟨t, ht⟩ := decoded_path hpath hstart
    simp only [Equiv.symm_apply_apply] at ht
    exact ⟨t, expand b, ht, hb, haccept⟩
  · rintro ⟨t, c, hr, ht, ha⟩
    refine ⟨pack hs .zero, pack hs hr, expand_pack hs .zero, ?_, ha, encoded_run hs hr⟩
    simpa using ht

/--
Replace each recursive search by graph reachability and apply the configuration correspondence.
-/
lemma search_acceptance (M : Machine) (w : Word) (s : ℕ)
    (hs : M.UsesSpace w s) : SearchAccepts M w s ↔ M.Accepts w := by
  rw [← Lax434930Proofs.SavitchProofs.configuration_acceptance M w s hs]
  simp only [SearchAccepts, AcceptsBounded, Lax434930Proofs.SavitchProofs.finite_reachability]

end Lax434930Proofs.SavitchProofs
