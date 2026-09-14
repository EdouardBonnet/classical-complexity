import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceRoutines

set_option backward.isDefEq.respectTransparency false

/-! Generate a word one Boolean choice at a time, using a supplied width. -/

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.GuessWord

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ChoiceLanguage
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

abbrev Data := StackRoutines.Data (K := K) (Γ := Γ) (σ := σ)
abbrev Code := Command K Γ (StackRoutines.Control Γ σ)

def choose : Code (K := K) (Γ := Γ) (σ := σ) := .choose (fun s b => {s with flag := b})

def write (dst : K) (bit : Bool → Γ) : StackRoutines.Code (K := K) (Γ := Γ) (σ := σ) :=
  .push (fun _ => dst) (fun s => bit s.flag)

def body (src dst : K) (bit : Bool → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq choose (.seq (.det (write dst bit)) (.det (StackRoutines.read src)))

def loopCode (src dst : K) (bit : Bool → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .loop (fun s => s.value.isSome) (body src dst bit)

def code (src dst : K) (bit : Bool → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (.det (StackRoutines.read src)) (loopCode src dst bit)

def chosen (d : Data (K := K) (Γ := Γ) (σ := σ)) (b : Bool) : Data (K := K) (Γ := Γ) (σ := σ) :=
  StackLanguage.assigned d {d.state with flag := b}

def pushed (d : Data (K := K) (Γ := Γ) (σ := σ)) (dst : K) (bit : Bool → Γ) (b : Bool) : Data (K := K) (Γ := Γ) (σ := σ) :=
  StackLanguage.pushed (chosen d b) dst (bit b)

def after (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) (bit : Bool → Γ) (b : Bool) : Data (K := K) (Γ := Γ) (σ := σ) :=
  StackLanguage.popped (pushed d dst bit b) src (fun s v => {s with value := v})

lemma body_execution (w : Word) (bound : ℕ) (src dst : K) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store dst).length + 1 < bound) (b : Bool) :
    Exec w bound (body src dst bit) d (after d src dst bit b) := by
  have hg : Good w bound (chosen d b) := hd
  have hp : Good w bound (pushed d dst bit b) := StackRoutines.good_pushed hg dst (bit b) hb
  exact .seq (.choose d _ b hd)
    (.seq (.det (.push (chosen d b) _ _ hg hp)) (.det (.pop (pushed d dst bit b) _ _ hp)))

lemma body_exec_iff (w : Word) (bound : ℕ) (src dst : K) (bit : Bool → Γ)
    (d e : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store dst).length + 1 < bound) :
    Exec w bound (body src dst bit) d e ↔ ∃ b, e = after d src dst bit b := by
  constructor
  · intro h
    cases h with
    | seq hchoose hrest =>
      cases hchoose with
      | choose _ _ b _ =>
        have hg : Good w bound (chosen d b) := hd
        have hp : Good w bound (pushed d dst bit b) := StackRoutines.good_pushed hg dst (bit b) hb
        cases hrest with
        | seq hpush hread =>
          obtain rfl := (det_exec_iff (StackLanguage.Exec.push (chosen d b)
            (fun _ => dst) (fun s => bit s.flag) hg hp)).mp hpush
          exact ⟨b, (det_exec_iff (StackLanguage.Exec.pop (pushed d dst bit b) _ _ hp)).mp hread⟩
  · rintro ⟨b, rfl⟩
    exact body_execution w bound src dst bit d hd hb b

lemma body_total (w : Word) (bound : ℕ) (src dst : K) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store dst).length + 1 < bound) : Total w bound (body src dst bit) d := by
  apply Total.seq (.choose d _ hd)
  intro e he
  cases he with
  | choose _ _ b _ =>
    have hg : Good w bound (chosen d b) := hd
    have hp : Good w bound (pushed d dst bit b) := StackRoutines.good_pushed hg dst (bit b) hb
    apply total_det_seq (StackLanguage.Exec.push (chosen d b) (fun _ => dst) (fun s => bit s.flag) hg hp)
    exact .det (.pop (pushed d dst bit b) _ _ hp)

def pending (d : Data (K := K) (Γ := Γ) (σ := σ)) (src : K) : ℕ :=
  (d.store src).length + (if d.state.value.isSome then 1 else 0)

lemma after_pending (src dst : K) (hne : src ≠ dst) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (b : Bool) :
    pending (after d src dst bit b) src = (d.store src).length ∧
      ((after d src dst bit b).store dst).length = (d.store dst).length + 1 := by
  cases hsrc : d.store src <;>
    simp [pending, after, pushed, chosen, StackLanguage.popped, StackLanguage.pushed,
      StackLanguage.assigned, hne, Ne.symm hne, hsrc]

lemma loop_total (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : pending d src + (d.store dst).length < bound) : Total w bound (loopCode src dst bit) d := by
  apply total_loop_rank (fun s => s.value.isSome) (body src dst bit)
    (fun e => Good w bound e ∧ pending e src + (e.store dst).length < bound)
    (fun e => pending e src) (fun _ h => h.1) ?_ ?_ d ⟨hd, hb⟩
  · intro e he ht
    apply body_total w bound src dst bit e he.1
    have hh := he.2
    simp only [pending, ht, ↓reduceIte] at hh
    omega
  · intro e f he ht hex
    have hh := he.2
    have hg : (e.store dst).length + 1 < bound := by
      simp only [pending, ht, ↓reduceIte] at hh
      omega
    obtain ⟨b, rfl⟩ := (body_exec_iff w bound src dst bit e f he.1 hg).mp hex
    obtain ⟨hp, hl⟩ := after_pending src dst hne bit e b
    refine ⟨⟨hex.good.2, ?_⟩, ?_⟩
    · rw [hp, hl]
      simp only [pending, ht, ↓reduceIte] at hh
      omega
    · change pending (after e src dst bit b) src < pending e src
      rw [hp]
      simp [pending, ht]

lemma total (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store src).length + (d.store dst).length < bound) : Total w bound (code src dst bit) d := by
  have hr := StackLanguage.Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
  apply total_det_seq hr
  apply loop_total w bound src dst hne bit _ hr.good.2
  cases hsrc : d.store src <;>
    simpa [pending, StackLanguage.popped, Ne.symm hne, hsrc] using hb

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.GuessWord
