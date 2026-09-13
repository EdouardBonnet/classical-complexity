import Lax434930Proofs.SavitchProofs.StackMacros

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.BinaryCounter

open Lax434930.PolynomialTime
open StackMacros
open StackRoutines (Data)
open scoped Classical

noncomputable section

variable {K Γ σ : Type} [Inhabited Γ]

def decrement (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Macro K Γ σ :=
  Macro.increment src aux (fun b => bit (!b)) (fun g => !(readBit g))

lemma decrement_guard (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (k n : ℕ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hsrc : d.store src = (word k n).map bit) (ha : d.store aux = []) :
    (decrement src aux bit readBit).guard w bound d := by
  simp [decrement, Macro.increment, hne, hbit, hsrc, ha, List.map_map, Function.comp_def]

lemma decrement_result (w : Word) (src aux : K)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (k n : ℕ) (hn : n < 2 ^ k) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hsrc : d.store src = (word k n).map bit) :
    (decrement src aux bit readBit).result w d =
      ⟨{d.state with value := none, flag := decide (n = 0)}, d.inputHead,
        Function.update d.store src ((word k (if n = 0 then 2 ^ k - 1 else n - 1)).map bit)⟩ := by
  have he := congrArg (List.map bit) (decrement_word k n hn)
  simp only [List.map_map, Function.comp_def] at he
  simp [decrement, Macro.increment, hsrc, List.map_map, Function.comp_def, hbit,
    decrement_carry k n hn, he]

lemma decrement_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (k n : ℕ) (hn : n < 2 ^ k) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hd : StackLanguage.Good w bound d) (hsrc : d.store src = (word k n).map bit) (ha : d.store aux = []) :
    StackLanguage.Exec w bound (decrement src aux bit readBit).code d
      ⟨{d.state with value := none, flag := decide (n = 0)}, d.inputHead,
        Function.update d.store src ((word k (if n = 0 then 2 ^ k - 1 else n - 1)).map bit)⟩ := by
  have h := (decrement src aux bit readBit).correct w bound d hd
    (decrement_guard w bound src aux hne bit readBit hbit k n d hsrc ha)
  simpa only [decrement_result w src aux bit readBit hbit k n hn d hsrc] using h

end

end Lax434930Proofs.SavitchProofs.BinaryCounter
