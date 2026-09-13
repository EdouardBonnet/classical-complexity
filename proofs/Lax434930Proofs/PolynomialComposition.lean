import Lax434930Proofs.TM2Transfer

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.PolynomialComposition

open Turing TM2Bounds TM2Composition Polynomial

theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial k c =>
      simp only [eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

/-- Composition of polynomial-time functions with a binary intermediate encoding. -/
theorem comp {α β γ αΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List Bool}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  let q : Polynomial ℕ := X + C (factor h₁.tm) * h₁.time
  let p : Polynomial ℕ := h₁.time + 2 * q + 2 + h₂.time.comp q
  let T := machine h₁.tm h₂.tm h₁.outputAlphabet h₂.inputAlphabet
  refine ⟨{ tm := T
            inputAlphabet := h₁.inputAlphabet
            outputAlphabet := h₂.outputAlphabet
            time := p
            outputsFun := ?_ }⟩
  intro a
  let r₁ := h₁.outputsFun a
  let r₂ := h₂.outputsFun (f a)
  have hl : (eβ (f a)).length ≤ q.eval (eα a).length := by
    have h := output_length h₁.tm r₁
    simpa [q] using h
  have ht₂ : h₂.time.eval (eβ (f a)).length ≤ h₂.time.eval (q.eval (eα a).length) :=
    eval_mono h₂.time hl
  have hfirst := lift_run h₁.tm.step T.step (leftCfg h₁.tm h₂.tm)
    (fun _ _ h => left_step h₁.tm h₂.tm h₁.outputAlphabet h₂.inputAlphabet h)
    r₁.steps r₁.evals_in_steps
  have hcopy := transfer_run h₁.tm h₂.tm h₁.outputAlphabet h₂.inputAlphabet
    ((eβ (f a)).map h₁.outputAlphabet.invFun)
  have hmiddle :
      (((eβ (f a)).map h₁.outputAlphabet.invFun).map h₁.outputAlphabet).map
        h₂.inputAlphabet.symm = (eβ (f a)).map h₂.inputAlphabet.invFun := by
    simp [List.map_map, Function.comp_def]
  rw [hmiddle] at hcopy
  have hsecond := lift_run h₂.tm.step T.step (rightCfg h₁.tm h₂.tm)
    (fun _ _ h => right_step h₁.tm h₂.tm h₁.outputAlphabet h₂.inputAlphabet h)
    r₂.steps r₂.evals_in_steps
  have hfull := append_run T.step (append_run T.step hfirst hcopy) hsecond
  refine ⟨⟨r₁.steps + (2 * (eβ (f a)).length + 2) + r₂.steps, ?_⟩, ?_⟩
  · simpa only [List.length_map, initial_eq,
      terminal_eq h₁.tm h₂.tm h₁.outputAlphabet h₂.inputAlphabet, Function.comp_apply, T,
      Option.map_some] using! hfull
  · have hb₁ := r₁.steps_le_m
    have hb₂ := r₂.steps_le_m
    change r₁.steps ≤ h₁.time.eval (eα a).length at hb₁
    change r₂.steps ≤ h₂.time.eval (eβ (f a)).length at hb₂
    dsimp only [p]
    simp only [eval_add, eval_mul, eval_ofNat, eval_comp]
    omega

end Lax434930Proofs.PolynomialComposition
