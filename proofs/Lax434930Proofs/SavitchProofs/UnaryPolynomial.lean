import Lax434930Proofs.SavitchProofs.UnaryExpansion

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.UnaryPolynomial

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Exec Good assigned popped)
open StackMacros (Macro)
open scoped Classical

noncomputable section

inductive Register (maxDegree : ℕ) where
  | input | output | aux | counter (i : Fin maxDegree)
  deriving Fintype

abbrev Data (m : ℕ) := StackRoutines.Data (K := Register m) (Γ := Unit) (σ := Unit)
abbrev Code (m : ℕ) := StackRoutines.Code (K := Register m) (Γ := Unit) (σ := Unit)

def grown {m : ℕ} (d : Data m) (n : ℕ) : Data m :=
  ⟨{d.state with value := none}, d.inputHead,
    Function.update d.store .output (List.replicate n () ++ d.store .output)⟩

lemma grown_zero {m : ℕ} (d : Data m) : grown d 0 = assigned d {d.state with value := none} := by
  simp [grown, assigned]

lemma grown_add {m : ℕ} (d : Data m) (a b : ℕ) : grown (grown d a) b = grown d (a + b) := by
  simp only [grown, Function.update_self, Function.update_idem]
  congr 1
  rw [Nat.add_comm a b, List.replicate_add, List.append_assoc]

def repeated {m : ℕ} (d : Data m) (k : Fin m) (count value : ℕ) : Data m :=
  grown (StackRoutines.cleared d (.counter k)) (count * value)

def repeatCode {m : ℕ} (k : Fin m) (body : Code m) : Code m :=
  .seq (StackRoutines.read (.counter k))
    (.loop (fun s => s.value.isSome) (.seq body (StackRoutines.read (.counter k))))

def monomial {m : ℕ} : (degree : ℕ) → degree ≤ m → ℕ → Code m
  | 0, _, a => .seq (StackRoutines.putWord .output (List.replicate a ()))
      (.assign (fun s => {s with value := none}))
  | degree + 1, h, a =>
      let k : Fin m := ⟨degree, by omega⟩
      .seq (StackRoutines.copy .input (.counter k) .aux)
        (repeatCode k (monomial degree (by omega) a))

lemma monomial_exec {m : ℕ} (degree : ℕ) (hdegree : degree ≤ m) (a n : ℕ)
    (w : Word) (bound : ℕ) (d : Data m) (hd : Good w bound d)
    (hn : d.store .input = List.replicate n ()) (ha : d.store .aux = [])
    (hc : ∀ k : Fin m, k.val < degree → d.store (.counter k) = [])
    (hb : a * n ^ degree + (d.store .output).length < bound) :
    Exec w bound (monomial degree hdegree a) d (grown d (a * n ^ degree)) := by
  induction degree generalizing d with
  | zero =>
    have hp := StackRoutines.prefix_exec w bound (Register.output : Register m)
      (List.replicate a ()) d hd (by simpa using hb)
    have he := Exec.seq hp (Exec.assign _ (fun s => {s with value := none}) hp.good.2)
    simpa [monomial, grown, assigned] using he
  | succ degree ih =>
    let k : Fin m := ⟨degree, by omega⟩
    let value := a * n ^ degree
    have repeat_exec (count : ℕ) (d : Data m) (hd : Good w bound d)
        (hn : d.store .input = List.replicate n ()) (ha : d.store .aux = [])
        (hc : ∀ j : Fin m, j.val < degree → d.store (.counter j) = [])
        (hk : d.store (.counter k) = List.replicate count ())
        (hb : count * value + (d.store .output).length < bound) :
        Exec w bound (repeatCode k (monomial degree (by omega) a)) d (repeated d k count value) := by
      induction count generalizing d with
      | zero =>
        let dr := popped d (.counter k) (fun s v => {s with value := v})
        have hr : Exec w bound (StackRoutines.read (.counter k)) d dr := .pop d _ _ hd
        have hv : dr.state.value.isSome = false := by simp [dr, popped, hk]
        have hl := Exec.loop_false (fun s => s.value.isSome)
          (.seq (monomial degree (by omega) a) (StackRoutines.read (.counter k))) dr hr.good.2 hv
        have he : dr = repeated d k 0 value := by simp [dr, popped, repeated, grown, StackRoutines.cleared, hk]
        exact he ▸ Exec.seq hr hl
      | succ count iht =>
        let dr := popped d (.counter k) (fun s v => {s with value := v})
        have hr : Exec w bound (StackRoutines.read (.counter k)) d dr := .pop d _ _ hd
        have hrn : dr.store .input = List.replicate n () := by simpa [dr, popped] using hn
        have hra : dr.store .aux = [] := by simpa [dr, popped] using ha
        have hrc (j : Fin m) (hj : j.val < degree) : dr.store (.counter j) = [] := by
          have hne : j ≠ k := by intro he; subst j; simp [k] at hj
          simpa [dr, popped, hne] using hc j hj
        have hrout : dr.store .output = d.store .output := by simp [dr, popped]
        have hrk : dr.store (.counter k) = List.replicate count () := by simp [dr, popped, hk]
        have hbody : Exec w bound (monomial degree (by omega) a) dr (grown dr value) :=
          ih (by omega) dr hr.good.2 hrn hra hrc (by
            rw [hrout]
            have hv : value ≤ (count + 1) * value := by
              simpa using Nat.mul_le_mul_right value (show 1 ≤ count + 1 by omega)
            exact (Nat.add_le_add_right hv _).trans_lt hb)
        let de := grown dr value
        have hen : de.store .input = List.replicate n () := by simpa [de, grown] using hrn
        have hea : de.store .aux = [] := by simpa [de, grown] using hra
        have hec (j : Fin m) (hj : j.val < degree) : de.store (.counter j) = [] := by
          simpa [de, grown] using hrc j hj
        have hek : de.store (.counter k) = List.replicate count () := by simpa [de, grown] using hrk
        have heb : count * value + (de.store .output).length < bound := by
          simpa [de, grown, hrout, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
        have ht := iht de hbody.good.2 hen hea hec hek heb
        cases ht with
        | @seq _ _ _ dn _ hread hloop =>
          have hl := Exec.loop_true (by simp [dr, popped, hk]) (Exec.seq hbody hread) hloop
          have he : repeated de k count value = repeated d k (count + 1) value := by
            dsimp only [repeated, de, grown, dr, popped, StackRoutines.cleared]
            congr 1
            funext j
            by_cases hj : j = .output
            · subst j
              simp only [Function.update_self, Function.update_of_ne (show (Register.output : Register m) ≠ .counter k by simp)]
              rw [← List.append_assoc, ← List.replicate_add]
              congr 2
              ring
            · by_cases hjk : j = .counter k <;> simp [Function.update_apply, hj, hjk]
          exact he ▸ Exec.seq hr hl
    let dc : Data m :=
      ⟨{d.state with value := none}, d.inputHead, Function.update d.store (.counter k) (d.store .input)⟩
    have hcopy : Exec w bound (StackRoutines.copy .input (.counter k) .aux) d dc :=
      StackRoutines.copy_exec w bound .input (.counter k) .aux (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) d hd ha
    have hcn : dc.store .input = List.replicate n () := by simpa [dc] using hn
    have hca : dc.store .aux = [] := by simpa [dc] using ha
    have hcc (j : Fin m) (hj : j.val < degree) : dc.store (.counter j) = [] := by
      have hne : j ≠ k := by intro he; subst j; simp [k] at hj
      simpa [dc, hne] using hc j (by omega)
    have hck : dc.store (.counter k) = List.replicate n () := by simp [dc, hn]
    have hcb : n * value + (dc.store .output).length < bound := by
      simpa [dc, value, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb
    have hr := repeat_exec n dc hcopy.good.2 hcn hca hcc hck hcb
    have he : repeated dc k n value = grown d (a * n ^ (degree + 1)) := by
      have hk0 := hc k (by simp [k])
      dsimp only [repeated, dc, grown, StackRoutines.cleared]
      congr 1
      funext j
      by_cases hj : j = .output
      · subst j
        simp [value, pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      · by_cases hjk : j = .counter k <;> simp [Function.update_apply, hj, hjk, hk0]
    exact he ▸ Exec.seq hcopy hr

end

end Lax434930Proofs.SavitchProofs.UnaryPolynomial
