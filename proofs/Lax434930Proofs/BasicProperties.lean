import Lax434930.BasicProperties
import Lax554803.ModelEquivalence
import Mathlib.Tactic

namespace Lax434930Proofs.BasicProperties

open Lax434930.PolynomialTime Lax434930.SpaceBounds
open Lax434930.LogarithmicSpace Lax434930.NondeterministicLogarithmicSpace
open Lax434930.PolynomialSpace Lax434930.NondeterministicPolynomialSpace
open Lax434930.ComplementClasses Lax434930.NondeterministicPolynomialTime
open Lax434930.ExponentialTime Lax434930.Certificates

theorem dspace_subset_nspace (s : ℕ → ℕ) : DSPACE s ⊆ NSPACE s := by
  rintro A ⟨M, _, hdec, hspace⟩
  exact ⟨M, hdec, hspace⟩

theorem dspace_mono {s t : ℕ → ℕ} (h : ∀ n, s n ≤ t n) : DSPACE s ⊆ DSPACE t := by
  rintro A ⟨M, hdet, hdec, hspace⟩
  exact ⟨M, hdet, hdec, fun w n c hr => (hspace w n c hr).trans_le (h w.length)⟩

theorem nspace_mono {s t : ℕ → ℕ} (h : ∀ n, s n ≤ t n) : NSPACE s ⊆ NSPACE t := by
  rintro A ⟨M, hdec, hspace⟩
  exact ⟨M, hdec, fun w n c hr => (hspace w n c hr).trans_le (h w.length)⟩

/--
---
conclusion: Lax434930.BasicProperties.L_subset_NL
assumptions:
---
Use the same machine and the same logarithmic bound, allowing nondeterminism.
-/
theorem L_subset_NL : L ⊆ NL := by
  rintro A ⟨c, hc, h⟩
  exact ⟨c, hc, dspace_subset_nspace _ h⟩

/--
---
conclusion: Lax434930.BasicProperties.PSPACE_subset_NPSPACE
assumptions:
---
Use the same machine and polynomial, allowing nondeterminism.
-/
theorem PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE := by
  rintro A ⟨p, h⟩
  exact ⟨p, dspace_subset_nspace _ h⟩

/--
---
conclusion: Lax434930.BasicProperties.L_subset_PSPACE
assumptions:
---
The logarithmic bound is at most the linear polynomial c(n+2).
-/
theorem L_subset_PSPACE : L ⊆ PSPACE := by
  rintro A ⟨c, _, h⟩
  refine ⟨Polynomial.C c * (Polynomial.X + Polynomial.C 2), dspace_mono ?_ h⟩
  intro n
  simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X] using Nat.mul_le_mul_left c (Nat.log_le_self 2 (n + 2))

/--
---
conclusion: Lax434930.BasicProperties.NL_subset_NPSPACE
assumptions:
---
Enlarge the bound to c(n+2) on every nondeterministic branch.
-/
theorem NL_subset_NPSPACE : NL ⊆ NPSPACE := by
  rintro A ⟨c, _, h⟩
  refine ⟨Polynomial.C c * (Polynomial.X + Polynomial.C 2), nspace_mono ?_ h⟩
  intro n
  simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X] using Nat.mul_le_mul_left c (Nat.log_le_self 2 (n + 2))

/--
---
conclusion: Lax434930.BasicProperties.P_subset_EXPTIME
assumptions:
  - Lax554803.ModelEquivalence.singleTapeP_eq_P
---
Use the proved single-tape characterization of P from lax-554803, then
enlarge the polynomial bound p(n) to 2 to the power p(n).
-/
theorem P_subset_EXPTIME : P ⊆ EXPTIME := by
  intro A h
  have hs : A ∈ Lax554803.MachineModels.SingleTapeP := by
    rw [Lax554803.ModelEquivalence.singleTapeP_eq_P]
    exact h
  obtain ⟨M, p, hp⟩ := hs
  refine ⟨M, p, ?_⟩
  intro w
  obtain ⟨c, ⟨ht⟩, hhalt, hanswer⟩ := hp w
  have hb : p.eval w.length ≤ 2 ^ p.eval w.length :=
    (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  exact ⟨c, ⟨⟨ht.toEvalsTo, ht.steps_le_m.trans hb⟩⟩, hhalt, hanswer⟩

/--
---
conclusion: Lax434930.BasicProperties.co_co
assumptions:
---
Complementing a binary language twice returns the original language.
-/
theorem co_co (C : Set Language) : co (co C) = C := by
  ext A
  simp only [co, Set.mem_setOf_eq, compl_compl]

/--
---
conclusion: Lax434930.BasicProperties.mem_coNP_iff
assumptions:
---
Negate the existential certificate characterization of the complement language.
-/
theorem mem_coNP_iff (A : Language) : A ∈ coNP ↔
    ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
      x ∈ A ↔ ∀ y : Word, y.length ≤ p.eval x.length → pair x y ∉ V := by
  classical
  constructor
  · rintro ⟨V, hV, p, hp⟩
    refine ⟨V, hV, p, fun x => ?_⟩
    have h := not_congr (hp x)
    simpa only [Set.mem_compl_iff, not_not, not_exists, not_and] using h
  · rintro ⟨V, hV, p, hp⟩
    refine ⟨V, hV, p, fun x => ?_⟩
    have h := not_congr (hp x)
    simpa only [Set.mem_compl_iff, not_forall, Classical.not_imp, not_not, exists_prop] using h

end Lax434930Proofs.BasicProperties
