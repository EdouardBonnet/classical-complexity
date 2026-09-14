import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingPrograms

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename CNFOutput Lax434930.PolynomialTime Polynomial

variable {I : Type} [DecidableEq I]

noncomputable def Emitter.append {f g : (I → Word) → Word} (p : Emitter I f) (q : Emitter I g) :
    Emitter I (fun a => f a ++ g a) where
  Workspace := p.Workspace ⊕ q.Workspace
  program := .seq (rename (workMap Sum.inl) p.program) (rename (workMap Sum.inr) q.program)
  bound := p.bound + q.bound
  length_bound a b hb := by
    simpa only [List.length_append, eval_add] using Nat.add_le_add (p.length_bound a b hb) (q.length_bound a b hb)
  executes a tail scratch b hb := by
    obtain ⟨t, ht, hp⟩ := p.run_in (workMap Sum.inl) (workMap_injective _ Sum.inl_injective)
      (store (W := p.Workspace ⊕ q.Workspace) a tail scratch) a b (by intro i; rfl) (by intro w; rfl) hb
    simp only [workMap, emitted_store] at hp
    obtain ⟨u, hu, hq⟩ := q.run_in (workMap Sum.inr) (workMap_injective _ Sum.inr_injective)
      (store (W := p.Workspace ⊕ q.Workspace) a ((f a).reverse ++ tail) none) a b
      (by intro i; rfl) (by intro w; rfl) hb
    simp only [workMap, emitted_store] at hq
    refine ⟨t + u, by simpa only [eval_add] using Nat.add_le_add ht hu, ?_⟩
    simpa only [List.reverse_append, List.append_assoc] using Executes.seq hp hq

def writeWord {K : Type} (out : K) : Word → BitProgram K Unit
  | [] => .atom (.load (fun _ => ((), none)))
  | b :: bs => .seq (.atom (.push out (fun _ => b))) (writeWord out bs)

lemma writeWord_executes {K : Type} [DecidableEq K] (out : K) (w : Word) (s : BitStore K Unit) :
    Executes (writeWord out w) s (emitted out w s) (w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have he : Op.apply (.load (fun _ : Unit × Option Bool => ((), none))) s = emitted out [] s := by
      apply Store.ext
      · exact Prod.ext (Subsingleton.elim _ _) rfl
      · simp [emitted, Op.apply]
    exact he ▸ Executes.atom (.load (fun _ => ((), none))) s
  | cons b bs ih =>
    have hp := Executes.atom (.push out (fun _ : Unit × Option Bool => b)) s
    have hh := ih (Op.apply (.push out (fun _ : Unit × Option Bool => b)) s)
    have he := Executes.seq hp hh
    have hc : 1 + (bs.length + 1) = (b :: bs).length + 1 := by simp; omega
    simpa only [hc, emitted, Op.apply, List.reverse_cons, List.append_assoc,
      Function.update_idem, Function.update_self, List.singleton_append] using! he

noncomputable def Emitter.constant (w : Word) : Emitter I (fun _ => w) where
  Workspace := Empty
  program := writeWord .output w
  bound := C (w.length + 1)
  length_bound a b hb := by simp
  executes a tail scratch b hb := by
    refine ⟨w.length + 1, by simp, ?_⟩
    simpa [emitted_store] using writeWord_executes (Key.output : Key I Empty) w (store a tail scratch)

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
