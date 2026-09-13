import Lax434930Proofs.SpaceSemantics
import Mathlib.Data.Nat.Find

/-! Bounds on branch lengths obtained by counting the unchanged space-machine configurations. -/

namespace Lax434930Proofs.ConfigurationTime

open Lax434930.PolynomialTime Lax434930.SpaceMachines

noncomputable section

/-- A bound on all branch lengths supplies a reachable terminal configuration. -/
lemma terminal_run {M : Machine} {w : Word} (hh : M.HaltsOn w) :
    ∃ n c, M.Run w n c ∧ M.Terminal w c := by
  classical
  obtain ⟨T, hT⟩ := hh
  let n := Nat.findGreatest (fun t => ∃ c, M.Run w t c) T
  obtain ⟨c, hc⟩ : ∃ c, M.Run w n c :=
    Nat.findGreatest_spec (P := fun t => ∃ c, M.Run w t c) (Nat.zero_le T)
      ⟨M.initial, .zero⟩
  refine ⟨n, c, hc, ?_⟩
  intro d he
  have hd := Machine.Run.succ hc he
  have hbad : n + 1 ≤ n := Nat.le_findGreatest (P := fun t => ∃ c, M.Run w t c)
    (hT _ _ hd) ⟨d, hd⟩
  omega

/-- The finite data retained by a configuration using `s` work cells. -/
abbrev BoundedConfig (M : Machine) (n s : ℕ) :=
  M.Q × Fin (n + 2) × Fin s × (Fin s → M.Γ)

def expand {M : Machine} {n s : ℕ} (c : BoundedConfig M n s) : M.Config :=
  ⟨c.1, c.2.1, c.2.2.1, fun i => if h : i < s then c.2.2.2 ⟨i, h⟩ else M.blank⟩

def pack {M : Machine} {w : Word} {s n : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hr : M.Run w n c) : BoundedConfig M w.length s :=
  ⟨c.state, ⟨c.inputHead, by have := SpaceSemantics.inputHead_le hr; omega⟩,
    ⟨c.workHead, hs n c hr⟩, fun i => c.tape i⟩

lemma expand_pack {M : Machine} {w : Word} {s n : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hr : M.Run w n c) : expand (pack hs hr) = c := by
  cases c with
  | mk q i j tape =>
    simp only [pack, expand]
    congr 1
    funext k
    split_ifs with hk
    · rfl
    · exact (SpaceSemantics.unvisited_tail_blank hs hr k (by omega)).symm

lemma card_bounded (M : Machine) (n s : ℕ) :
    Fintype.card (BoundedConfig M n s) =
      Fintype.card M.Q * (n + 2) * s * Fintype.card M.Γ ^ s := by
  simp [BoundedConfig, Nat.mul_assoc]

/-- The greatest length of a run ending at this configuration, within a global halting bound. -/
def rank (M : Machine) (w : Word) (T : ℕ) (c : M.Config) : ℕ :=
  haveI := Classical.propDecidable
  Nat.findGreatest (fun t => M.Run w t c) T

lemma rank_step {M : Machine} {w : Word} {T n : ℕ} {c d : M.Config}
    (hT : ∀ t e, M.Run w t e → t ≤ T) (hr : M.Run w n c) (he : M.Step w c d) :
    rank M w T c < rank M w T d := by
  classical
  have hc : M.Run w (rank M w T c) c := by
    exact Nat.findGreatest_spec (P := fun t => M.Run w t c) (hT n c hr) hr
  have hd := Machine.Run.succ hc he
  exact (Nat.lt_succ_self _).trans_le (Nat.le_findGreatest (hT _ _ hd) hd)

def predecessors (M : Machine) (w : Word) (s T : ℕ) (c : M.Config) :
    Finset (BoundedConfig M w.length s) :=
  haveI := Classical.propDecidable
  Finset.univ.filter (fun b => rank M w T (expand b) ≤ rank M w T c)

lemma predecessors_strict {M : Machine} {w : Word} {s T n : ℕ} {c d : M.Config}
    (hs : M.UsesSpace w s) (hT : ∀ t e, M.Run w t e → t ≤ T)
    (hr : M.Run w n c) (he : M.Step w c d) :
    predecessors M w s T c ⊂ predecessors M w s T d := by
  classical
  have hcd := rank_step hT hr he
  have hsub : predecessors M w s T c ⊆ predecessors M w s T d := by
    intro b hb
    simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.trans hcd.le
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro eq
  have hd : pack hs (.succ hr he) ∈ predecessors M w s T d := by
    simp [predecessors, expand_pack]
  rw [← eq] at hd
  have hbad : rank M w T d ≤ rank M w T c := by
    simpa only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and,
      expand_pack] using hd
  exact (not_le_of_gt hcd) hbad

/-- Every branch of a halting space-bounded machine is shorter than its configuration count. -/
lemma run_lt_configuration_count {M : Machine} {w : Word} {s n : ℕ} {c : M.Config}
    (hs : M.UsesSpace w s) (hh : M.HaltsOn w) (hr : M.Run w n c) :
    n < Fintype.card M.Q * (w.length + 2) * s * Fintype.card M.Γ ^ s := by
  classical
  obtain ⟨T, hT⟩ := hh
  have h : n < (predecessors M w s T c).card := by
    induction hr with
    | zero =>
      exact Finset.card_pos.mpr ⟨pack hs .zero, by simp [predecessors, expand_pack]⟩
    | succ hr he ih =>
      have hlt := Finset.card_lt_card (predecessors_strict hs hT hr he)
      omega
  rw [← card_bounded]
  exact h.trans_le (Finset.card_le_univ _)

/-- The configuration count for a polynomial space bound has an exponential time bound. -/
lemma configuration_count_le_exp (M : Machine) (n s : ℕ) :
    Fintype.card M.Q * (n + 2) * s * Fintype.card M.Γ ^ s ≤
      2 ^ (Fintype.card M.Q + (n + 2) + s + Fintype.card M.Γ * s) := by
  have h (a : ℕ) : a ≤ 2 ^ a := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  have hg : Fintype.card M.Γ ^ s ≤ 2 ^ (Fintype.card M.Γ * s) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (h _) s
  calc
    _ ≤ 2 ^ Fintype.card M.Q * 2 ^ (n + 2) * 2 ^ s *
        2 ^ (Fintype.card M.Γ * s) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (h _) (h _)) (h _)) hg
    _ = _ := by simp only [pow_add]

/-- The configuration count for logarithmic work space is polynomial in input length. -/
lemma configuration_count_log (M : Machine) (n c : ℕ) :
    Fintype.card M.Q * (n + 2) * (c * Nat.log 2 (n + 2)) *
      Fintype.card M.Γ ^ (c * Nat.log 2 (n + 2)) ≤
      (Fintype.card M.Q * c) * (n + 2) ^ (Fintype.card M.Γ * c + 2) := by
  have hg : Fintype.card M.Γ ≤ 2 ^ Fintype.card M.Γ :=
    (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  have hpow : Fintype.card M.Γ ^ (c * Nat.log 2 (n + 2)) ≤
      (n + 2) ^ (Fintype.card M.Γ * c) := by
    calc
      _ ≤ (2 ^ Fintype.card M.Γ) ^ (c * Nat.log 2 (n + 2)) :=
        Nat.pow_le_pow_left hg _
      _ = (2 ^ Nat.log 2 (n + 2)) ^ (Fintype.card M.Γ * c) := by
        simp only [← pow_mul]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) _
  calc
    _ ≤ Fintype.card M.Q * (n + 2) * (c * (n + 2)) *
        (n + 2) ^ (Fintype.card M.Γ * c) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left c (Nat.log_le_self 2 (n + 2)))) hpow
    _ = _ := by rw [pow_add]; ring

/-- The polynomial bounding every computation branch of a polynomial-space decider. -/
def spaceTimeExponent (M : Machine) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (Fintype.card M.Q) + (Polynomial.X + Polynomial.C 2) + p +
    Polynomial.C (Fintype.card M.Γ) * p

lemma polynomial_space_branch_time (M : Machine) (p : Polynomial ℕ)
    (hh : ∀ w, M.HaltsOn w) (hs : ∀ w, M.UsesSpace w (p.eval w.length)) :
    ∀ w n c, M.Run w n c → n < 2 ^ (spaceTimeExponent M p).eval w.length := by
  intro w n c hr
  have h := (run_lt_configuration_count (hs w) (hh w) hr).trans_le
    (configuration_count_le_exp M w.length (p.eval w.length))
  simpa [spaceTimeExponent] using h

/-- The polynomial bounding every computation branch of a logarithmic-space decider. -/
def logTimePolynomial (M : Machine) (c : ℕ) : Polynomial ℕ :=
  Polynomial.C (Fintype.card M.Q * c) *
    (Polynomial.X + Polynomial.C 2) ^ (Fintype.card M.Γ * c + 2)

lemma logarithmic_space_branch_time (M : Machine) (c : ℕ)
    (hh : ∀ w, M.HaltsOn w)
    (hs : ∀ w, M.UsesSpace w (c * Nat.log 2 (w.length + 2))) :
    ∀ w n d, M.Run w n d → n < (logTimePolynomial M c).eval w.length := by
  intro w n d hr
  have h := (run_lt_configuration_count (hs w) (hh w) hr).trans_le
    (configuration_count_log M w.length c)
  simpa [logTimePolynomial] using h

end

end Lax434930Proofs.ConfigurationTime
