import Lax434930Proofs.InclusionAux.ChoiceProofs.StackCompilation
import Lax434930Proofs.SavitchProofs.StackLanguage

set_option backward.isDefEq.respectTransparency false

/-! Structured nondeterministic programs. Deterministic subroutines retain
their existing semantics; choice changes only the finite control. -/

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

abbrev Data := StackLanguage.Data
abbrev Good := @StackLanguage.Good
abbrev assigned := @StackLanguage.assigned

inductive Command (K Γ σ : Type) where
  | det (code : StackLanguage.Command K Γ σ)
  | choose (update : σ → Bool → σ)
  | seq (first second : Command K Γ σ)
  | branch (test : σ → Bool) (yes no : Command K Γ σ)
  | loop (test : σ → Bool) (body : Command K Γ σ)

inductive Exec (w : Word) (bound : ℕ) : Command K Γ σ → Data K Γ σ → Data K Γ σ → Prop
  | det {code d e} : StackLanguage.Exec w bound code d e → Exec w bound (.det code) d e
  | choose (d : Data K Γ σ) (f : σ → Bool → σ) (b : Bool) (hd : Good w bound d) :
      Exec w bound (.choose f) d (assigned d (f d.state b))
  | seq {a b d e f} : Exec w bound a d e → Exec w bound b e f → Exec w bound (.seq a b) d f
  | branch_true {test yes no d e} : test d.state = true → Exec w bound yes d e →
      Exec w bound (.branch test yes no) d e
  | branch_false {test yes no d e} : test d.state = false → Exec w bound no d e →
      Exec w bound (.branch test yes no) d e
  | loop_false (test : σ → Bool) (body) (d : Data K Γ σ) (hd : Good w bound d) :
      test d.state = false → Exec w bound (.loop test body) d d
  | loop_true {test body d e f} : test d.state = true → Exec w bound body d e →
      Exec w bound (.loop test body) e f → Exec w bound (.loop test body) d f

lemma Exec.good {w : Word} {bound : ℕ} {c : Command K Γ σ} {d e : Data K Γ σ}
    (h : Exec w bound c d e) : Good w bound d ∧ Good w bound e := by
  induction h with
  | det he => exact he.good
  | choose _ _ _ hd => exact ⟨hd, hd⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | branch_true _ _ ih => exact ih
  | branch_false _ _ ih => exact ih
  | loop_false _ _ _ hd _ => exact ⟨hd, hd⟩
  | loop_true _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-- Every choice terminates, and each execution respects the stack bound. -/
inductive Total (w : Word) (bound : ℕ) : Command K Γ σ → Data K Γ σ → Prop
  | det {code d e} : StackLanguage.Exec w bound code d e → Total w bound (.det code) d
  | choose (d : Data K Γ σ) (f : σ → Bool → σ) : Good w bound d → Total w bound (.choose f) d
  | seq {a b d} : Total w bound a d →
      (∀ e, Exec w bound a d e → Total w bound b e) → Total w bound (.seq a b) d
  | branch_true {test yes no d} : test d.state = true → Total w bound yes d →
      Total w bound (.branch test yes no) d
  | branch_false {test yes no d} : test d.state = false → Total w bound no d →
      Total w bound (.branch test yes no) d
  | loop_false (test : σ → Bool) (body) (d : Data K Γ σ) : Good w bound d →
      test d.state = false → Total w bound (.loop test body) d
  | loop_true {test body d} : test d.state = true → Total w bound body d →
      (∀ e, Exec w bound body d e → Total w bound (.loop test body) e) →
      Total w bound (.loop test body) d

lemma Total.good {w : Word} {bound : ℕ} {c : Command K Γ σ} {d : Data K Γ σ}
    (h : Total w bound c d) : Good w bound d := by
  induction h with
  | det he => exact he.good.1
  | choose _ _ hd => exact hd
  | seq _ _ ih _ => exact ih
  | branch_true _ _ ih => exact ih
  | branch_false _ _ ih => exact ih
  | loop_false _ _ _ hd _ => exact hd
  | loop_true _ _ _ ih _ => exact ih

lemma Total.exists_exec {w : Word} {bound : ℕ} {c : Command K Γ σ} {d : Data K Γ σ}
    (h : Total w bound c d) : ∃ e, Exec w bound c d e := by
  induction h with
  | det he => exact ⟨_, .det he⟩
  | choose d f hd => exact ⟨_, .choose d f false hd⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂ e he
    exact ⟨f, .seq he hf⟩
  | branch_true ht _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨e, .branch_true ht he⟩
  | branch_false ht _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨e, .branch_false ht he⟩
  | loop_false test body d hd ht => exact ⟨d, .loop_false test body d hd ht⟩
  | loop_true ht _ _ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂ e he
    exact ⟨f, .loop_true ht he hf⟩

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
