import Lax434930Proofs.SavitchProofs.StackRoutines

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.BinaryCounter

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Command Exec Good assigned popped pushed)
open StackRoutines
open scoped Classical

noncomputable section

def increment : List Bool → List Bool
  | [] => []
  | false :: xs => true :: xs
  | true :: xs => false :: increment xs

def carry : List Bool → Bool
  | [] => true
  | false :: _ => false
  | true :: xs => carry xs

def value : List Bool → ℕ
  | [] => 0
  | b :: xs => b.toNat + 2 * value xs

lemma increment_length (xs : List Bool) : (increment xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [increment, ih]

lemma value_lt (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp [value, pow_succ] <;> omega

lemma increment_value (xs : List Bool) :
    value (increment xs) + (if carry xs then 2 ^ xs.length else 0) = value xs + 1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b
    · simp [increment, carry, value, Nat.add_comm]
    · cases hc : carry xs <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at ih <;>
        simp [increment, carry, value, hc, pow_succ] <;> omega

variable {K Γ σ : Type} [Inhabited Γ]

def finish (src aux : K) (bit : Bool → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (.assign (fun s => {s with flag := !s.value.isSome}))
    (.seq (.branch (fun s => s.value.isSome)
      (.push (fun _ => src) (fun _ => bit true)) .skip) (transfer aux src))

def counter (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) :
    Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (read src) (.seq
    (.loop (fun s => s.value.isSome && (s.value.map readBit).getD false)
      (.seq (.push (fun _ => aux) (fun _ => bit false)) (read src)))
    (finish src aux bit))

def finishData (d : Data (K := K) (Γ := Γ) (σ := σ)) (src : K) (bit : Bool → Γ) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with flag := !d.state.value.isSome}, d.inputHead,
    Function.update d.store src (if d.state.value.isSome then bit true :: d.store src else d.store src)⟩

lemma finish_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store aux).length + (d.store src).length + (if d.state.value.isSome then 1 else 0) < bound) :
    Exec w bound (finish src aux bit) d (transferred (finishData d src bit) aux src) := by
  let da := assigned d {d.state with flag := !d.state.value.isSome}
  have ha : Exec w bound (.assign (fun s => {s with flag := !s.value.isSome})) d da :=
    Exec.assign d _ hd
  have hd' : Good w bound (finishData d src bit) := by
    apply good_store_update (d := da) ha.good.2 src _
    cases hv : d.state.value <;> simp [hv] at hb ⊢ <;> omega
  have hbranch : Exec w bound (.branch (fun s : Control Γ σ => s.value.isSome)
      (.push (fun _ => src) (fun _ => bit true)) .skip) da (finishData d src bit) := by
    cases hv : d.state.value with
    | none =>
      apply Exec.branch_false (by simp [da, assigned, hv])
      simpa [finishData, da, assigned, hv] using Exec.skip da ha.good.2
    | some g =>
      apply Exec.branch_true (by simp [da, assigned, hv])
      simpa [finishData, da, assigned, pushed, hv] using
        Exec.push da (fun _ => src) (fun _ => bit true) ha.good.2
          (by simpa [finishData, da, assigned, pushed, hv] using hd')
  have ht := transfer_exec w bound aux src (Ne.symm hne) (finishData d src bit) hd' (by
    cases hv : d.state.value <;>
      simp [finishData, Ne.symm hne, hv, Nat.add_assoc, Nat.add_comm] at hb ⊢ <;> omega)
  exact .seq ha (.seq hbranch ht)

def result (d : Data (K := K) (Γ := Γ) (σ := σ)) (src aux : K) (bit : Bool → Γ)
    (xs : List Bool) (zeros : ℕ) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none, flag := carry xs}, d.inputHead,
    Function.update (Function.update d.store aux []) src
      ((List.replicate zeros false ++ increment xs).map bit)⟩

lemma counter_exec_general (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (xs : List Bool) (zeros : ℕ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hd : Good w bound d) (hsrc : d.store src = xs.map bit)
    (haux : d.store aux = List.replicate zeros (bit false)) (hb : xs.length + zeros < bound) :
    Exec w bound (counter src aux bit readBit) d (result d src aux bit xs zeros) := by
  induction xs generalizing zeros d with
  | nil =>
    let dr := popped d src (fun s value => {s with value := value})
    have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
    have hl := Exec.loop_false
      (fun s : Control Γ σ => s.value.isSome && (s.value.map readBit).getD false)
      (.seq (.push (fun _ => aux) (fun _ => bit false)) (read src)) dr hr.good.2
      (by simp [dr, popped, hsrc])
    have hf := finish_exec w bound src aux hne bit dr hr.good.2 (by
      simpa [dr, popped, hsrc, haux, Ne.symm hne] using hb)
    have he : transferred (finishData dr src bit) aux src = result d src aux bit [] zeros := by
      simp only [transferred, finishData, result, dr, popped, hsrc, List.map_nil, List.head?_nil,
        List.tail_nil, increment, carry]
      congr 1
      funext j
      by_cases hs : j = src <;> by_cases ha : j = aux <;>
        simp_all [Function.update_apply, Ne.symm hne]
    exact he ▸ Exec.seq hr (Exec.seq hl hf)
  | cons b xs ih =>
    cases b with
    | false =>
      let dr := popped d src (fun s value => {s with value := value})
      have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
      have hl := Exec.loop_false
        (fun s : Control Γ σ => s.value.isSome && (s.value.map readBit).getD false)
        (.seq (.push (fun _ => aux) (fun _ => bit false)) (read src)) dr hr.good.2
        (by simp [dr, popped, hsrc, hbit])
      have hf := finish_exec w bound src aux hne bit dr hr.good.2 (by
        simp [dr, popped, hsrc, haux, Ne.symm hne] at hb ⊢; omega)
      have he : transferred (finishData dr src bit) aux src = result d src aux bit (false :: xs) zeros := by
        simp only [transferred, finishData, result, dr, popped, hsrc, List.map_cons,
          List.head?_cons, List.tail_cons, increment, carry]
        congr 1
        funext j
        by_cases hs : j = src <;> by_cases ha : j = aux <;>
          simp_all [Function.update_apply, Ne.symm hne]
      exact he ▸ Exec.seq hr (Exec.seq hl hf)
    | true =>
      let dr := popped d src (fun s value => {s with value := value})
      have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
      let dp := pushed dr aux (bit false)
      have hpGood : Good w bound dp := good_pushed hr.good.2 aux (bit false) (by
        simp [dr, popped, haux, Ne.symm hne] at hb ⊢; omega)
      have hp : Exec w bound (.push (fun _ => aux) (fun _ => bit false)) dr dp :=
        Exec.push dr _ _ hr.good.2 hpGood
      have hpSrc : dp.store src = xs.map bit := by simp [dp, pushed, dr, popped, hsrc, hne]
      have hpAux : dp.store aux = List.replicate (zeros + 1) (bit false) := by
        simp [dp, pushed, dr, popped, haux, Ne.symm hne, List.replicate_succ]
      have hpBudget : xs.length + (zeros + 1) < bound := by simp only [List.length_cons] at hb; omega
      have htail := ih (zeros + 1) dp hpGood hpSrc hpAux hpBudget
      cases htail with
      | @seq _ _ _ dm _ hread hrest =>
        cases hrest with
        | @seq _ _ _ dn _ hloop hpost =>
          have hl : Exec w bound
              (.loop (fun s : Control Γ σ => s.value.isSome && (s.value.map readBit).getD false)
                (.seq (.push (fun _ => aux) (fun _ => bit false)) (read src))) dr dn :=
            .loop_true (by simp [dr, popped, hsrc, hbit]) (.seq hp hread) hloop
          have he : result dp src aux bit xs (zeros + 1) = result d src aux bit (true :: xs) zeros := by
            simp only [result, dp, pushed, dr, popped, hsrc, List.map_cons, List.head?_cons,
              List.tail_cons, increment, carry]
            congr 1
            funext j
            by_cases hs : j = src <;> by_cases ha : j = aux <;>
              simp_all [Function.update_apply, List.replicate_add, List.append_assoc]
          exact he ▸ Exec.seq hr (Exec.seq hl hpost)

lemma counter_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (xs : List Bool) (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hsrc : d.store src = xs.map bit) (haux : d.store aux = []) :
    Exec w bound (counter src aux bit readBit) d
      ⟨{d.state with value := none, flag := carry xs}, d.inputHead,
        Function.update d.store src ((increment xs).map bit)⟩ := by
  have h := counter_exec_general w bound src aux hne bit readBit hbit xs 0 d hd hsrc
    (by simpa using haux) (by simpa [hsrc] using hd.2 src)
  have he : result d src aux bit xs 0 =
      ⟨{d.state with value := none, flag := carry xs}, d.inputHead,
        Function.update d.store src ((increment xs).map bit)⟩ := by
    simp [result, ← haux]
  exact he ▸ h

end

end Lax434930Proofs.SavitchProofs.BinaryCounter
