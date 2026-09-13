import Lax434930Proofs.SavitchProofs.Reachability

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.Reachability

lemma layer_closed {N : ℕ} {G : Graph N} {a b : Fin N} {k : ℕ}
    (h : ∀ v, Within (fun u v => G u v = true) (k + 1) a v →
      Within (fun u v => G u v = true) k a v)
    (hr : Reachable G a b) : Within (fun u v => G u v = true) k a b := by
  induction hr with
  | refl => exact ⟨0, Nat.zero_le _, Walk.nil a⟩
  | tail _ e ih =>
    obtain ⟨l, hl, hw⟩ := ih
    exact h _ ⟨l + 1, by omega, Walk.tail hw e⟩

/--
Reachable layers grow strictly until they contain the target; there are only $N$ vertices.
-/
lemma short_paths {N : ℕ} (G : Graph N) (a b : Fin N) :
    Reachable G a b ↔ ∃ k < N, Walk (fun u v => G u v = true) k a b := by
  classical
  constructor
  · intro hr
    let R := fun u v => G u v = true
    let S := fun k => Finset.univ.filter (fun v => Within R k a v)
    have mem (k : ℕ) (v : Fin N) : v ∈ S k ↔ Within R k a v := by simp [S]
    have mono (r s : ℕ) (hrs : r ≤ s) : S r ⊆ S s := by
      intro v hv
      exact (mem s v).mpr (within_mono hrs ((mem r v).mp hv))
    have grows (k : ℕ) (hb : ¬ Within R k a b) : S k ⊂ S (k + 1) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨mono k (k + 1) (by omega), ?_⟩
      intro heq
      apply hb
      apply layer_closed (hr := hr)
      intro v hv
      apply (mem k v).mp
      rw [heq]
      exact (mem (k + 1) v).mpr hv
    have lower : ∀ k, ¬ Within R k a b → k + 1 ≤ (S k).card := by
      intro k
      induction k with
      | zero =>
        intro _
        exact Finset.card_pos.mpr ⟨a, (mem 0 a).mpr ⟨0, le_rfl, Walk.nil a⟩⟩
      | succ k ih =>
        intro hb
        have hb' : ¬ Within R k a b := fun h => hb (within_mono (by omega) h)
        have h₁ := ih hb'
        have h₂ := Finset.card_lt_card (grows k hb')
        omega
    have hb : Within R (N - 1) a b := by
      by_contra hn
      have h₁ := lower (N - 1) hn
      have hsub : S (N - 1) ⊂ Finset.univ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        apply hn
        apply (mem (N - 1) b).mp
        rw [heq]
        exact Finset.mem_univ b
      have h₂ := Finset.card_lt_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at h₂
      have := a.isLt
      omega
    obtain ⟨k, hk, hw⟩ := hb
    exact ⟨k, by have := a.isLt; omega, hw⟩
  · rintro ⟨k, _, hw⟩
    exact walk_reachable hw

end Lax434930Proofs.SavitchProofs
