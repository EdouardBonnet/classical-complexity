import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingSource
import Lax434930Proofs.InclusionAux.TimeHelpers.StackDrop

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy
open Lax434930.PolynomialTime Polynomial

variable {I : Type} [DecidableEq I]

inductive DropSlot where
  | counter | buffer | temporary
  deriving DecidableEq, Fintype

def dropStore (a : I → Word) (tail counter buffer : Word) (scratch : Option Bool) :
    BitStore (Key I DropSlot) Unit :=
  ⟨((), scratch), fun k => match k with
    | .input i => a i
    | .output => tail
    | .work .counter => counter
    | .work .buffer => buffer
    | .work .temporary => []⟩

lemma dropStore_first (a : I → Word) (tail : Word) (scratch : Option Bool) (source : I) :
    Executes (copy (.input source) (.work .buffer) (.work .temporary)) (store a tail scratch)
      (dropStore a tail [] (a source) none) (7 * (a source).length + 4) := by
  have h := copy_store (Key.input source) (.work DropSlot.buffer) (.work .temporary)
    (by simp) (by simp) (by simp) (store a tail scratch) rfl
  convert h using 1
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | s <;> try simp [dropStore, store]
  cases s <;> simp [dropStore, store]
  all_goals rfl

lemma dropStore_second (a : I → Word) (tail buffer : Word) (index : I) :
    Executes (copy (.input index) (.work .counter) (.work .temporary)) (dropStore a tail [] buffer none)
      (dropStore a tail (a index) buffer none) (7 * (a index).length + 4) := by
  have h := copy_store (Key.input index) (.work DropSlot.counter) (.work .temporary)
    (by simp) (by simp) (by simp) (dropStore a tail [] buffer none) rfl
  convert h using 1
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | s <;> try simp [dropStore]
  cases s <;> simp [dropStore]
  all_goals rfl

lemma dropStore_drop (a : I → Word) (tail counter buffer : Word) :
    ∃ t, t ≤ 3 * counter.length + 2 ∧
      Executes (StackDrop.dropCount (.work .counter) (.work .buffer))
        (dropStore a tail counter buffer none)
        (dropStore a tail [] (buffer.drop counter.length) none) t := by
  obtain ⟨t, ht, he⟩ := StackDrop.dropCount_store (.work DropSlot.counter) (.work .buffer)
    (by simp) (dropStore a tail counter buffer none)
  refine ⟨t, ht, ?_⟩
  convert he using 1
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | s <;> try simp [dropStore]
  cases s <;> simp [dropStore]

lemma dropStore_output (a : I → Word) (tail buffer : Word) :
    Executes (transfer (.work .buffer) .output) (dropStore a tail [] buffer none)
      (store a (buffer.reverse ++ tail) none) (3 * buffer.length + 2) := by
  have h := transfer_store (.work DropSlot.buffer) Key.output (by simp) (dropStore a tail [] buffer none)
  convert h using 1
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | s <;> try simp [dropStore, store]
  cases s <;> simp [dropStore, store]
  all_goals rfl

noncomputable def Emitter.drop (source index : I) :
    Emitter I (fun a => (a source).drop (a index).length) where
  Workspace := DropSlot
  program := .seq (copy (.input source) (.work .buffer) (.work .temporary))
    (.seq (copy (.input index) (.work .counter) (.work .temporary))
      (.seq (StackDrop.dropCount (.work .counter) (.work .buffer)) (transfer (.work .buffer) .output)))
  bound := C 20 * X + C 12
  length_bound a b hb := by
    have h := hb source
    simp only [List.length_drop, eval_add, eval_mul, eval_C, eval_X]
    omega
  executes a tail scratch b hb := by
    have hfirst := dropStore_first a tail scratch source
    have hsecond := dropStore_second a tail (a source) index
    obtain ⟨t, ht, hdrop⟩ := dropStore_drop a tail (a index) (a source)
    have houtput := dropStore_output a tail ((a source).drop (a index).length)
    refine ⟨(7 * (a source).length + 4) + ((7 * (a index).length + 4) +
      (t + (3 * ((a source).drop (a index).length).length + 2))), ?_,
      .seq hfirst (.seq hsecond (.seq hdrop houtput))⟩
    have hs := hb source
    have hi := hb index
    simp only [List.length_drop, eval_add, eval_mul, eval_C, eval_X]
    omega

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
