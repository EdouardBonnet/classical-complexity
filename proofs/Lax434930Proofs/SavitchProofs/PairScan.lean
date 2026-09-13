import Lax434930Proofs.SavitchProofs.StackRoutines

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackRoutines

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Command Exec Good assigned popped)
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def withPair (s : Control Γ σ) (a b : Option Γ) : Control Γ σ :=
  {s with value := a, other := b}

def readPair (first second : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (read first) (.pop (fun _ => second) (fun s g => {s with other := g}))

def readPairData (d : Data (K := K) (Γ := Γ) (σ := σ)) (first second : K) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨withPair d.state (d.store first).head? (d.store second).head?, d.inputHead,
    Function.update (Function.update d.store first (d.store first).tail) second
      (d.store second).tail⟩

lemma readPair_exec (w : Word) (bound : ℕ) (first second : K) (hne : first ≠ second)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) :
    Exec w bound (readPair first second) d (readPairData d first second) := by
  have h₁ := Exec.pop d (fun _ => first) (fun s value => {s with value := value}) hd
  have h₂ := Exec.pop _ (fun _ => second) (fun s other => {s with other := other}) h₁.good.2
  simpa [readPairData, withPair, popped, Ne.symm hne] using! Exec.seq h₁ h₂

def pairFold (f : Control Γ σ → Control Γ σ) : List Γ → List Γ → Control Γ σ → Control Γ σ
  | [], [], s => withPair s none none
  | x :: xs, ys, s => pairFold f xs ys.tail (f (withPair s (some x) ys.head?))
  | [], y :: ys, s => pairFold f [] ys (f (withPair s none (some y)))

def scanPairs (first second : K) (f : Control Γ σ → Control Γ σ) :
    Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (readPair first second)
    (.loop (fun s => s.value.isSome || s.other.isSome)
      (.seq (.assign f) (readPair first second)))

def scannedPairs (d : Data (K := K) (Γ := Γ) (σ := σ)) (first second : K)
    (f : Control Γ σ → Control Γ σ) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨pairFold f (d.store first) (d.store second) d.state, d.inputHead,
    Function.update (Function.update d.store first []) second []⟩

lemma scanPairs_exec (w : Word) (bound : ℕ) (first second : K) (hne : first ≠ second)
    (f : Control Γ σ → Control Γ σ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) :
    Exec w bound (scanPairs first second f) d (scannedPairs d first second f) := by
  generalize hx : d.store first = xs at *
  generalize hy : d.store second = ys at *
  induction hn : xs.length + ys.length using Nat.strong_induction_on generalizing d xs ys with
  | h n ih =>
    have hr := readPair_exec w bound first second hne d hd
    let dr := readPairData d first second
    by_cases hempty : xs = [] ∧ ys = []
    · obtain ⟨rfl, rfl⟩ := hempty
      have hl := Exec.loop_false
        (fun s : Control Γ σ => s.value.isSome || s.other.isSome)
        (.seq (.assign f) (readPair first second)) dr hr.good.2
        (by simp [dr, readPairData, withPair, hx, hy])
      simpa [scanPairs, dr, readPairData, scannedPairs, hx, hy, pairFold] using Exec.seq hr hl
    · let da := assigned dr (f dr.state)
      have ha : Exec w bound (.assign f) dr da := Exec.assign dr f hr.good.2
      have hax : da.store first = xs.tail := by simp [da, assigned, dr, readPairData, hne, hx]
      have hay : da.store second = ys.tail := by simp [da, assigned, dr, readPairData, hy]
      have hlen : xs.tail.length + ys.tail.length < n := by
        cases xs <;> cases ys <;> simp_all <;> omega
      have ht := ih _ hlen da ha.good.2 xs.tail hax ys.tail hay rfl
      cases ht with
      | @seq _ _ _ dm _ hread hloop =>
        have hl : Exec w bound
            (.loop (fun s : Control Γ σ => s.value.isSome || s.other.isSome)
              (.seq (.assign f) (readPair first second))) dr (scannedPairs da first second f) :=
          .loop_true (by
            cases xs <;> cases ys <;> simp_all [dr, readPairData, withPair])
            (.seq ha hread) hloop
        have he : scannedPairs da first second f = scannedPairs d first second f := by
          simp only [scannedPairs, hx, hy, da, assigned, dr, readPairData]
          congr 1
          · cases xs <;> cases ys <;> simp_all [pairFold, withPair]
          · funext j
            by_cases h₁ : j = first <;> by_cases h₂ : j = second <;>
              simp_all [Function.update_apply]
        exact he ▸ Exec.seq hr hl

def comparePair (s : Control Γ σ) : Control Γ σ :=
  {s with flag := s.flag && decide (s.value = s.other)}

lemma compare_fold (xs ys : List Γ) (s : Control Γ σ) :
    pairFold comparePair xs ys s =
      {s with value := none, other := none, flag := s.flag && decide (xs = ys)} := by
  induction xs generalizing ys s with
  | nil =>
    induction ys generalizing s with
    | nil => simp [pairFold, withPair]
    | cons y ys ih => simp [pairFold, ih, comparePair, withPair]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pairFold, ih, comparePair, withPair]
    | cons y ys =>
      simp [pairFold, ih, comparePair, withPair, Bool.and_assoc]

def compareWords (first second : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (.assign (fun s => {s with flag := true})) (scanPairs first second comparePair)

lemma compareWords_exec (w : Word) (bound : ℕ) (first second : K) (hne : first ≠ second)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) :
    Exec w bound (compareWords first second) d
      ⟨{d.state with
          value := none
          other := none
          flag := decide (d.store first = d.store second)}, d.inputHead,
        Function.update (Function.update d.store first []) second []⟩ := by
  have ha := Exec.assign d (fun s => {s with flag := true}) hd
  have hs := scanPairs_exec w bound first second hne comparePair _ ha.good.2
  simpa [scannedPairs, assigned, compare_fold] using! Exec.seq ha hs

end

end Lax434930Proofs.SavitchProofs.StackRoutines
