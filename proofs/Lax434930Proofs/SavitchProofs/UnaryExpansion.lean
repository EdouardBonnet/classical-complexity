import Lax434930Proofs.SavitchProofs.StackMacros

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackMacros.Macro

open Lax434930.PolynomialTime
open StackLanguage (assigned)
open StackRoutines (Data)
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def putWord (dst : K) (xs : List Γ) : Macro K Γ σ where
  code := StackRoutines.putWord dst xs
  result _ d := ⟨d.state, d.inputHead, Function.update d.store dst (xs ++ d.store dst)⟩
  guard _ b d := xs.length + (d.store dst).length < b
  correct w b d hd h := StackRoutines.prefix_exec w b dst xs d hd h

def appendCopies [Inhabited Γ] (src dst aux : K) : ℕ → Macro K Γ σ
  | 0 => assign (fun s => {s with value := none})
  | n + 1 => seq (copyAppend src dst aux) (appendCopies src dst aux n)

lemma appendCopies_spec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst aux : K)
    (h₁ : src ≠ dst) (h₂ : src ≠ aux) (h₃ : dst ≠ aux)
    (g : Γ) (n len : ℕ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hsrc : d.store src = List.replicate len g) (haux : d.store aux = [])
    (hb : n * len + (d.store dst).length < bound) :
    (appendCopies src dst aux n).guard w bound d ∧
      (appendCopies src dst aux n).result w d =
        ⟨{d.state with value := none}, d.inputHead,
          Function.update d.store dst (List.replicate (n * len) g ++ d.store dst)⟩ := by
  induction n generalizing d with
  | zero =>
    refine ⟨trivial, ?_⟩
    simp [appendCopies, assign, assigned]
  | succ n ih =>
    let dc := (copyAppend src dst aux).result w d
    have hs : dc.store src = List.replicate len g := by simp [dc, copyAppend, StackRoutines.copiedAppend, h₁, hsrc]
    have ha : dc.store aux = [] := by simp [dc, copyAppend, StackRoutines.copiedAppend, Ne.symm h₃, haux]
    have ht : dc.store dst = List.replicate len g ++ d.store dst := by
      simp [dc, copyAppend, StackRoutines.copiedAppend, hsrc]
    have hbound : n * len + (dc.store dst).length < bound := by
      rw [ht]
      simp only [List.length_append, List.length_replicate]
      simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
    obtain ⟨hg, he⟩ := ih dc hs ha hbound
    refine ⟨⟨?_, hg⟩, ?_⟩
    · simp [copyAppend, h₁, h₂, h₃, haux, hsrc]
      nlinarith
    · change (appendCopies src dst aux n).result w dc = _
      rw [he]
      simp only [dc, copyAppend, StackRoutines.copiedAppend]
      congr 1
      funext k
      by_cases hk : k = dst
      · subst k
        simp only [Function.update_self, hsrc, Nat.add_mul, Nat.one_mul]
        rw [List.replicate_add, List.append_assoc]
      · simp [Function.update_apply, hk]

end

end Lax434930Proofs.SavitchProofs.StackMacros.Macro
