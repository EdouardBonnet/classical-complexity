import Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceMachine
import Lax434930Proofs.SavitchProofs.StackMacros

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

lemma deterministic_exec_unique {w : Word} {bound : ℕ} {c : StackLanguage.Command K Γ σ}
    {d e f : Data K Γ σ} (h : StackLanguage.Exec w bound c d e)
    (hf : StackLanguage.Exec w bound c d f) : e = f := by
  induction h generalizing f with
  | skip d hd => cases hf; rfl
  | assign d g hd => cases hf; rfl
  | input d g hd => cases hf; rfl
  | move d g hd => cases hf; rfl
  | push d k g hd he => cases hf; rfl
  | pop d k g hd => cases hf; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
    cases hf with
    | seq hf₁ hf₂ =>
      obtain rfl := ih₁ hf₁
      exact ih₂ hf₂
  | branch_true hp h ih =>
    cases hf with
    | branch_true _ hf => exact ih hf
    | branch_false hq _ => simp [hp] at hq
  | branch_false hp h ih =>
    cases hf with
    | branch_true hq _ => simp [hp] at hq
    | branch_false _ hf => exact ih hf
  | loop_false test body d hd hp =>
    cases hf with
    | loop_false => rfl
    | loop_true hq _ _ => simp [hp] at hq
  | loop_true hp h₁ h₂ ih₁ ih₂ =>
    cases hf with
    | loop_false _ _ _ _ hq => simp [hp] at hq
    | loop_true _ hf₁ hf₂ =>
      obtain rfl := ih₁ hf₁
      exact ih₂ hf₂

lemma det_exec_iff {w : Word} {bound : ℕ} {c : StackLanguage.Command K Γ σ}
    {d e f : Data K Γ σ} (h : StackLanguage.Exec w bound c d e) :
    Exec w bound (.det c) d f ↔ f = e := by
  constructor
  · intro hf
    cases hf with
    | det hf => exact deterministic_exec_unique hf h
  · rintro rfl
    exact .det h

lemma total_det_seq {w : Word} {bound : ℕ} {a : StackLanguage.Command K Γ σ}
    {b : Command K Γ σ} {d e : Data K Γ σ}
    (ha : StackLanguage.Exec w bound a d e) (hb : Total w bound b e) :
    Total w bound (.seq (.det a) b) d := by
  exact .seq (.det ha) (fun f hf => (det_exec_iff ha).mp hf ▸ hb)

lemma total_loop_rank {w : Word} {bound : ℕ} (test : σ → Bool) (body : Command K Γ σ)
    (invariant : Data K Γ σ → Prop) (rank : Data K Γ σ → ℕ)
    (hg : ∀ d, invariant d → Good w bound d)
    (ht : ∀ d, invariant d → test d.state = true → Total w bound body d)
    (hs : ∀ d e, invariant d → test d.state = true → Exec w bound body d e →
      invariant e ∧ rank e < rank d)
    (d : Data K Γ σ) (hd : invariant d) : Total w bound (.loop test body) d := by
  have hr (n : ℕ) : ∀ d, rank d = n → invariant d → Total w bound (.loop test body) d := by
    intro d hn hd
    induction n using Nat.strong_induction_on generalizing d with
    | h n ih =>
      cases he : test d.state with
      | false => exact .loop_false test body d (hg d hd) he
      | true =>
        apply Total.loop_true he (ht d hd he)
        intro e hex
        obtain ⟨hie, hlt⟩ := hs d e hd he hex
        exact ih (rank e) (by omega) e rfl hie
  exact hr (rank d) d rfl hd

lemma exec_loop_true {w : Word} {bound : ℕ} {test : σ → Bool} {body : Command K Γ σ}
    {d e : Data K Γ σ} (h : Exec w bound (.loop test body) d e) (ht : test d.state = true) :
    ∃ f, Exec w bound body d f ∧ Exec w bound (.loop test body) f e := by
  cases h with
  | loop_false _ _ _ _ hf => simp [ht] at hf
  | loop_true _ hb hr => exact ⟨_, hb, hr⟩

lemma exec_loop_invariant {w : Word} {bound : ℕ} {test : σ → Bool} {body : Command K Γ σ}
    (invariant : Data K Γ σ → Prop)
    (hs : ∀ d e, invariant d → test d.state = true → Exec w bound body d e → invariant e)
    {d e : Data K Γ σ} (h : Exec w bound (.loop test body) d e) (hd : invariant d) :
    invariant e ∧ test e.state = false := by
  generalize hc : Command.loop test body = c at h
  induction h with
  | loop_false test' body' d hg hp =>
    cases hc
    exact ⟨hd, hp⟩
  | loop_true hp hb hl ihb ihl =>
    cases hc
    exact ihl (hs _ _ hd hp hb) rfl
  | det _ => cases hc
  | choose _ _ _ _ => cases hc
  | seq _ _ _ _ => cases hc
  | branch_true _ _ _ => cases hc
  | branch_false _ _ _ => cases hc

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.ChoiceLanguage
