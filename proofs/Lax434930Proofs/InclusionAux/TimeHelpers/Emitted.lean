import Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy
import Lax434930Proofs.PolynomialComposition
import Lax434930.PolynomialTime

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.CNFOutput

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930.PolynomialTime

variable {K Aux : Type} [DecidableEq K]

def emitted (out : K) (w : Word) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk out (w.reverse ++ s.stk out)⟩

@[simp] lemma emitted_aux (out : K) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).state.1 = s.state.1 := rfl

@[simp] lemma emitted_scratch (out : K) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).state.2 = none := rfl

lemma emitted_empty (out : K) (s : BitStore K Aux) :
    emitted out [] s = ⟨(s.state.1, none), s.stk⟩ := by
  simp [emitted, Function.update_eq_self]

lemma emitted_append (out : K) (u v : Word) (s : BitStore K Aux) :
    emitted out v (emitted out u s) = emitted out (u ++ v) s := by
  simp [emitted, List.reverse_append, List.append_assoc, Function.update_idem]

lemma emitted_source (out src : K) (h : src ≠ out) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).stk src = s.stk src := by
  simp [emitted, h]

end Lax434930Proofs.InclusionAux.TimeHelpers.CNFOutput
