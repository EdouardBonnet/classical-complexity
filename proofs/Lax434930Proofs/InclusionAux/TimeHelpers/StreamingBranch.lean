import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingAppend

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer Lax434930Proofs.InclusionAux.TimeCompiler.StackRename
open CNFOutput Lax434930.PolynomialTime Polynomial

variable {I : Type} [DecidableEq I]

noncomputable def Emitter.inspect (i : I) (f : Option Bool → Bool) :
    Emitter I (fun a => [f (a i).head?]) where
  Workspace := Empty
  program := .seq (.atom (.peek (.input i) (fun _ b => ((), b))))
    (.seq (.atom (.push .output (fun s => f s.2))) (.atom (.load (fun _ => ((), none)))))
  bound := C 3
  length_bound a b hb := by simp
  executes a tail scratch b hb := by
    let s : BitStore (Key I Empty) Unit := store a tail scratch
    let peek : Op (fun _ : Key I Empty => Bool) (Unit × Option Bool) := .peek (.input i) (fun _ b => ((), b))
    let push : Op (fun _ : Key I Empty => Bool) (Unit × Option Bool) := .push .output (fun s => f s.2)
    let reset : Op (fun _ : Key I Empty => Bool) (Unit × Option Bool) := .load (fun _ => ((), none))
    refine ⟨3, by simp, ?_⟩
    have h := Executes.seq (Executes.atom peek s)
      (.seq (Executes.atom push (peek.apply s)) (Executes.atom reset (push.apply (peek.apply s))))
    convert h using 1
    apply Store.ext
    · rfl
    · funext k
      rcases k with j | _ | w
      · simp [s, peek, push, reset, Op.apply, store]
      · simp [s, peek, push, reset, Op.apply, store]
      · cases w

noncomputable def Emitter.branch (i : I) {f g : (I → Word) → Word}
    (p : Emitter I f) (q : Emitter I g) :
    Emitter I (fun a => if (a i).head?.getD false then f a else g a) where
  Workspace := p.Workspace ⊕ q.Workspace
  program := .seq (.atom (.peek (.input i) (fun _ b => ((), b))))
    (.branch (fun s => s.2.getD false)
      (rename (workMap Sum.inl) p.program) (rename (workMap Sum.inr) q.program))
  bound := p.bound + q.bound + C 2
  length_bound a b hb := by
    have hp := p.length_bound a b hb
    have hq := q.length_bound a b hb
    split <;> simp only [eval_add, eval_C] <;> omega
  executes a tail scratch b hb := by
    let s : BitStore (Key I (p.Workspace ⊕ q.Workspace)) Unit := store a tail scratch
    let mid : BitStore (Key I (p.Workspace ⊕ q.Workspace)) Unit := store a tail (a i).head?
    have hp : Executes (.atom (.peek (.input i) (fun _ b => ((), b)))) s mid 1 := Executes.atom _ _
    cases hh : (a i).head?.getD false with
    | true =>
      obtain ⟨t, ht, he⟩ := p.run_in (workMap Sum.inl) (workMap_injective _ Sum.inl_injective)
        mid a b (by intro j; rfl) (by intro w; rfl) hb
      simp only [workMap, mid, emitted_store] at he
      refine ⟨1 + (t + 1), ?_, ?_⟩
      · simp only [eval_add, eval_C]; omega
      · simpa only [hh, Bool.true_eq, ite_true] using Executes.seq hp
          (Executes.branch_true (b := fun s => s.2.getD false) hh he)
    | false =>
      obtain ⟨t, ht, he⟩ := q.run_in (workMap Sum.inr) (workMap_injective _ Sum.inr_injective)
        mid a b (by intro j; rfl) (by intro w; rfl) hb
      simp only [workMap, mid, emitted_store] at he
      refine ⟨1 + (t + 1), ?_, ?_⟩
      · simp only [eval_add, eval_C]; omega
      · simpa only [hh, Bool.false_eq_true, ite_false] using Executes.seq hp
          (Executes.branch_false (b := fun s => s.2.getD false) hh he)

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
