import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingForLayout

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename Lax434930Proofs.InclusionAux.TimeCompiler.StackFor
open Lax434930Proofs.InclusionAux.TimeCompiler.StackClear (clear)
open CNFOutput Lax434930.PolynomialTime Polynomial

variable {I : Type} [DecidableEq I]

noncomputable def Emitter.forRange (domain : I) {f : (Option I → Word) → Word}
    (p : Emitter (Option I) f) :
    Emitter I (fun a => (List.range (a domain).length).flatMap
      (fun i => f (extend a (List.replicate i true)))) where
  Workspace := ForWork p.Workspace
  program := .seq (rename forLength (Emitter.length domain).program)
    (.seq (forValues (.work (.inl .domain)) (.work (.inl .counter)) (.work (.inl .coord))
      (.work (.inl .temporary)) (rename forBody p.program)) (clear (.work (.inl .domain))))
  bound := (p.bound + C 24) * X + C 16
  length_bound a b hb := by
    have hn := hb domain
    have h := flatMap_length_bound (List.range (a domain).length)
      (fun i => f (extend a (List.replicate i true))) (p.bound.eval b) (by
        intro i hi
        have hi' := List.mem_range.mp hi
        apply p.length_bound _ b
        intro j
        cases j with
        | none => simp only [extend, Option.elim_none, List.length_replicate]; omega
        | some j => exact hb j)
    simp only [List.length_range] at h
    have hm := Nat.mul_le_mul_right (p.bound.eval b) hn
    simp only [eval_add, eval_mul, eval_C, eval_X]
    nlinarith
  executes a tail scratch b hb := by
    let n := (a domain).length
    have hn : n ≤ b := hb domain
    let base : Word → BitStore (Key I (ForWork p.Workspace)) Unit := forStore a n
    let body := rename (forBody (I := I)) p.program
    let emit : ℕ → Word → Word := fun i w => (f (extend a (List.replicate i true))).reverse ++ w
    obtain ⟨t, ht, hlength⟩ := (Emitter.length domain).run_in forLength forLength_injective
      (store (W := ForWork p.Workspace) a tail scratch) a b
      (by intro i; rfl) (by intro w; rfl) hb
    simp only [forLength, forStore_start] at hlength
    have hbody : ∀ i, i < n → ∀ w remaining scratch,
        ∃ cost scratch', cost ≤ p.bound.eval b ∧ Executes body
          (pack base (.work (.inl .counter)) (.work (.inl .coord)) w i remaining scratch)
          (pack base (.work (.inl .counter)) (.work (.inl .coord)) (emit i w) i remaining scratch') cost := by
      intro i hi w remaining scratch
      obtain ⟨c, hc, he⟩ := p.run_in forBody forBody_injective
        (pack base (.work (.inl .counter)) (.work (.inl .coord)) w i remaining scratch)
        (extend a (List.replicate i true)) b
        (by intro j; cases j <;> simp [forBody, pack, working, base, forStore, extend])
        (by intro v; simp [forBody, pack, working, base, forStore]) (by
          intro j
          cases j with
          | none => simp only [extend, Option.elim_none, List.length_replicate]; omega
          | some j => exact hb j)
      refine ⟨c, none, hc, ?_⟩
      simpa only [forBody, base, forStore_emitted] using he
    obtain ⟨u, hu, hfor⟩ := forValues_executes base (.work (.inl .domain)) (.work (.inl .counter))
      (.work (.inl .coord)) (.work (.inl .temporary)) (by simp) body emit n (p.bound.eval b)
      (by intro w; rfl) (by intro w; rfl) (by intro w; rfl) hbody tail rfl
    have hr : reset (base (foldRange emit 0 n tail)) =
        forStore a n (((List.range n).flatMap fun i => f (extend a (List.replicate i true))).reverse ++ tail) := by
      change base (foldRange emit 0 n tail) = _
      rw [show foldRange emit 0 n tail = _ from foldRange_emitting _ 0 n tail]
      rw [← List.range_eq_range']
    rw [hr] at hfor
    have hclear := forStore_clear (W := p.Workspace) a n
      (((List.range n).flatMap fun i => f (extend a (List.replicate i true))).reverse ++ tail)
    refine ⟨t + (u + (2 * n + 2)), ?_, .seq hlength (.seq hfor hclear)⟩
    simp only [Emitter.length, Emitter.congr, Emitter.sourceMap,
      eval_add, eval_mul, eval_C, eval_X] at ht ⊢
    have hm := Nat.mul_le_mul_left (p.bound.eval b + 12) hn
    nlinarith

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
