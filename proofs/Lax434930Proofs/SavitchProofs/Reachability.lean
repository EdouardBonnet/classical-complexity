import Lax434930Proofs.SavitchDefinitions.FiniteSearch
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs

open Lax434930Proofs.SavitchDefinitions Lax434930Proofs.SavitchDefinitions.Reachability

lemma walk_trans {α : Type} {R : α → α → Prop} {r s : ℕ} {a b c : α}
    (h₁ : Walk R r a b) (h₂ : Walk R s b c) : Walk R (r + s) a c := by
  induction h₂ with
  | nil => simpa using h₁
  | tail _ e ih => simpa [Nat.add_assoc] using Walk.tail (ih h₁) e

lemma walk_split {α : Type} {R : α → α → Prop} {r s : ℕ} {a b : α}
    (h : Walk R (r + s) a b) : ∃ m, Walk R r a m ∧ Walk R s m b := by
  induction s generalizing b with
  | zero => exact ⟨b, by simpa using h, Walk.nil b⟩
  | succ s ih =>
    rw [Nat.add_succ] at h
    cases h with
    | tail h e =>
      obtain ⟨m, h₁, h₂⟩ := ih h
      exact ⟨m, h₁, Walk.tail h₂ e⟩

lemma within_mono {α : Type} {R : α → α → Prop} {r s : ℕ} {a b : α}
    (hrs : r ≤ s) : Within R r a b → Within R s a b := by
  rintro ⟨k, hk, h⟩
  exact ⟨k, hk.trans hrs, h⟩

/--
Split at the $r$th edge, or at the endpoint when the walk is shorter.
-/
lemma path_splitting {α : Type} (R : α → α → Prop) (r s : ℕ) (a b : α) :
    Within R (r + s) a b ↔ ∃ m, Within R r a m ∧ Within R s m b := by
  constructor
  · rintro ⟨k, hk, h⟩
    by_cases hkr : k ≤ r
    · exact ⟨b, ⟨k, hkr, h⟩, ⟨0, Nat.zero_le _, Walk.nil b⟩⟩
    · have heq : r + (k - r) = k := by omega
      obtain ⟨m, h₁, h₂⟩ := walk_split (r := r) (s := k - r) (heq.symm ▸ h)
      exact ⟨m, ⟨r, le_rfl, h₁⟩, ⟨k - r, by omega, h₂⟩⟩
  · rintro ⟨m, ⟨k, hk, h₁⟩, ⟨l, hl, h₂⟩⟩
    exact ⟨k + l, Nat.add_le_add hk hl, walk_trans h₁ h₂⟩

lemma within_one {α : Type} (R : α → α → Prop) (a b : α) :
    Within R 1 a b ↔ a = b ∨ R a b := by
  constructor
  · rintro ⟨k, hk, h⟩
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · cases h
      exact Or.inl rfl
    · cases h with
      | tail h e =>
        cases h
        exact Or.inr e
  · rintro (rfl | e)
    · exact ⟨0, by omega, Walk.nil a⟩
    · exact ⟨1, le_rfl, Walk.tail (Walk.nil a) e⟩

/--
Induction on the recursion depth, using the midpoint decomposition.
-/
lemma recursive_reachability {N : ℕ} (G : Graph N) (k : ℕ) (a b : Fin N) :
    search G k a b = true ↔ Within (fun u v => G u v = true) (2 ^ k) a b := by
  induction k generalizing a b with
  | zero => simp [search, within_one]
  | succ k ih =>
    simp only [search, List.any_eq_true, Bool.and_eq_true, List.mem_finRange,
      true_and, ih]
    rw [pow_succ, Nat.mul_two, Lax434930Proofs.SavitchProofs.path_splitting]

lemma walk_reachable {N : ℕ} {G : Graph N} {k : ℕ} {a b : Fin N}
    (h : Walk (fun u v => G u v = true) k a b) : Reachable G a b := by
  induction h with
  | nil => exact .refl
  | tail _ e ih => exact ih.tail e


end Lax434930Proofs.SavitchProofs
