import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingAppend
import Lax434930Proofs.InclusionAux.TimeHelpers.StackMapTransfer

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy
open Lax434930.PolynomialTime Polynomial

variable {I : Type} [DecidableEq I]

noncomputable def Emitter.sourceMap (i : I) (f : Bool → Bool) :
    Emitter I (fun a => (a i).map f) where
  Workspace := Bool
  program := .seq (copy (.input i) (.work false) (.work true))
    (StackMapTransfer.transfer (.work false) .output f)
  bound := C 10 * X + C 6
  length_bound a b hb := by simp only [List.length_map, eval_add, eval_mul, eval_C, eval_X]; have := hb i; omega
  executes a tail scratch b hb := by
    let s : BitStore (Key I Bool) Unit := store a tail scratch
    let mid : BitStore (Key I Bool) Unit :=
      ⟨((), none), Function.update s.stk (.work false) (a i)⟩
    have hc : Executes (copy (.input i) (.work false) (.work true)) s mid (7 * (a i).length + 4) := by
      simpa [s, mid, store] using copy_store (Key.input i) (.work false) (.work true)
        (by simp) (by simp) (by simp) s rfl
    have ht := StackMapTransfer.transfer_store (Key.work false) .output (by simp) f mid
    refine ⟨(7 * (a i).length + 4) + (3 * (a i).length + 2), ?_, ?_⟩
    · simp only [eval_add, eval_mul, eval_C, eval_X]
      have := hb i
      omega
    · convert Executes.seq hc ht using 1
      · apply Store.ext
        · rfl
        · funext k
          rcases k with j | _ | w
          · simp [s, mid, store]
          · simp [s, mid, store]
          · cases w <;> simp [s, mid, store]
      · rfl

noncomputable def Emitter.source (i : I) : Emitter I (fun a => a i) := by
  exact (Emitter.sourceMap i id).congr (by intro a; simp)

noncomputable def Emitter.length (i : I) : Emitter I (fun a => List.replicate (a i).length true) := by
  exact (Emitter.sourceMap i (fun _ => true)).congr (by intro a; simp)

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
