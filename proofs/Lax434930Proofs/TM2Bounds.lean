import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! Output-length bounds and sequential composition of finite Turing-machine runs. -/

namespace Lax434930Proofs.TM2Bounds

open Turing

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

theorem cfg_ext {c d : TM2.Cfg Γ Λ σ} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : c.stk = d.stk) : c = d := by
  cases c
  cases d
  cases hl
  cases hv
  cases hs
  rfl

/-- A uniform bound on the number of symbols a single statement can add. -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .pop _ _ q | .peek _ _ q | .load _ q => pushes q
  | .branch _ p q => max (pushes p) (pushes q)
  | .goto _ | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ)
    (s : (k : K) → List (Γ k)) (k : K) :
    ((TM2.stepAux q v s).stk k).length ≤ (s k).length + pushes q := by
  induction q generalizing v s with
  | push j f q ih =>
      have h := ih v (Function.update s j (f v :: s j))
      have hu : ((Function.update s j (f v :: s j)) k).length ≤ (s k).length + 1 := by
        by_cases hj : k = j
        · subst k; simp
        · simp [Function.update_of_ne hj]
      dsimp only [TM2.stepAux, pushes]
      omega
  | pop j f q ih =>
      have h := ih (f v (s j).head?) (Function.update s j (s j).tail)
      have hu : ((Function.update s j (s j).tail) k).length ≤ (s k).length := by
        by_cases hj : k = j
        · subst k; simp
        · simp [Function.update_of_ne hj]
      dsimp only [TM2.stepAux, pushes]
      omega
  | peek j f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq =>
      cases hf : f v
      · simpa only [TM2.stepAux, hf, Bool.cond_false] using!
          (ihq v s).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · simpa only [TM2.stepAux, hf, Bool.cond_true] using!
          (ihp v s).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

noncomputable def factor (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  ∑ l : tm.Λ, pushes (tm.m l)

theorem pushes_le_factor (tm : FinTM2) (l : tm.Λ) : pushes (tm.m l) ≤ factor tm := by
  classical
  letI := tm.ΛFin
  change pushes (tm.m l) ≤ ∑ j : tm.Λ, pushes (tm.m j)
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (pushes (tm.m j))) (Finset.mem_univ l)

theorem step_length (tm : FinTM2) {c d : tm.Cfg} (h : tm.step c = some d) (k : tm.K) :
    (d.stk k).length ≤ (c.stk k).length + factor tm := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (tm.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact (stepAux_length _ _ _ _).trans
            (Nat.add_le_add_left (pushes_le_factor tm l) _)

theorem run_length (tm : FinTM2) (t : ℕ) {c d : tm.Cfg}
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[t] (some c) = some d) (k : tm.K) :
    (d.stk k).length ≤ (c.stk k).length + factor tm * t := by
  induction t generalizing c with
  | zero => cases Option.some.inj h; simp
  | succ t ih =>
      rw [Function.iterate_succ_apply] at h
      cases he : tm.step c with
      | none =>
          have hn : (fun x : Option tm.Cfg => x.bind tm.step)^[t] none = none :=
            Function.iterate_fixed rfl t
          simp only [Option.bind_some, he, hn, reduceCtorEq] at h
      | some e =>
          have hr := ih (by simpa only [Option.bind_some, he] using h)
          have hs := step_length tm he k
          rw [Nat.mul_succ]
          omega

theorem output_length (tm : FinTM2) {xs : List (tm.Γ tm.k₀)}
    {ys : List (tm.Γ tm.k₁)} {t : ℕ}
    (h : TM2OutputsInTime tm xs (some ys) t) :
    ys.length ≤ xs.length + factor tm * t := by
  have hl := run_length tm h.steps h.evals_in_steps tm.k₁
  have hi' : ∀ k, ((initList tm xs).stk k).length ≤ xs.length := by
    intro k
    by_cases hk : k = tm.k₀
    · subst k; simp [initList]
    · simp [initList, hk]
  have hi := hi' tm.k₁
  have ho : ((haltList tm ys).stk tm.k₁).length = ys.length := by simp [haltList]
  change ((haltList tm ys).stk tm.k₁).length ≤ _ at hl
  rw [ho] at hl
  exact hl.trans (Nat.add_le_add hi (Nat.mul_le_mul_left _ h.steps_le_m))

/-- Lift a finite successful run using preservation of each successful step.
The image of a halting configuration may be a subroutine's continuation. -/
theorem lift_run {A B : Type} (f : A → Option A) (g : B → Option B) (embed : A → B)
    (hstep : ∀ a b, f a = some b → g (embed a) = some (embed b))
    (t : ℕ) {a b : A}
    (h : (fun x : Option A => x.bind f)^[t] (some a) = some b) :
    (fun x : Option B => x.bind g)^[t] (some (embed a)) = some (embed b) := by
  induction t generalizing a with
  | zero => cases Option.some.inj h; rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply] at h ⊢
      cases he : f a with
      | none =>
          have hn : (fun x : Option A => x.bind f)^[t] none = none :=
            Function.iterate_fixed rfl t
          simp only [Option.bind_some, he, hn, reduceCtorEq] at h
      | some c =>
          simp only [Option.bind_some, hstep a c he]
          apply ih
          simpa only [Option.bind_some, he] using h

theorem append_run {A : Type} (f : A → Option A) {a b c : A} {s t : ℕ}
    (hs : (fun x : Option A => x.bind f)^[s] (some a) = some b)
    (ht : (fun x : Option A => x.bind f)^[t] (some b) = some c) :
    (fun x : Option A => x.bind f)^[s + t] (some a) = some c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

end Lax434930Proofs.TM2Bounds
