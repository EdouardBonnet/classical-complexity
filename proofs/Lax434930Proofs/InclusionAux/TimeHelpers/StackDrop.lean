import Lax434930Proofs.InclusionAux.TimeCompiler.StackRepeat
import Lax434930Proofs.PolynomialComposition

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.StackDrop

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer Lax434930Proofs.InclusionAux.TimeCompiler.StackRepeat

variable {K Aux : Type} [DecidableEq K]

def dropCount (counter src : K) : BitProgram K Aux := repeatCount counter (read src)

lemma read_target (base : K → List Bool) (counter src : K) (xs ys : List Bool)
    (a : Aux) (scratch : Option Bool) :
    readStore src (working base counter src xs ys a scratch) =
      working base counter src xs ys.tail a ys.head? := by
  apply Store.ext <;> try rfl
  · simp [readStore, Op.apply, working]
  · funext k
    by_cases hk : k = src <;> simp_all [readStore, Op.apply, working]

lemma result_drop (base : K → List Bool) (counter src : K) (hne : counter ≠ src)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    result counter (readStore src) xs.length (working base counter src xs ys a scratch) =
      working base counter src [] (ys.drop xs.length) a none := by
  induction xs generalizing ys scratch with
  | nil => simpa only [result, List.length_nil, List.drop_zero] using!
      pop_working base counter src hne [] ys a scratch
  | cons b bs ih =>
    simp only [List.length_cons, result]
    rw [show readStore counter (working base counter src (b :: bs) ys a scratch) =
      working base counter src bs ys a (some b) from pop_working base counter src hne _ _ _ _]
    rw [read_target, ih]
    congr 1
    cases ys <;> simp

lemma dropCount_executes (base : K → List Bool) (counter src : K) (hne : counter ≠ src)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    ∃ t, t ≤ 3 * xs.length + 2 ∧ Executes (dropCount counter src)
      (working base counter src xs ys a scratch)
      (working base counter src [] (ys.drop xs.length) a none) t := by
  have h := repeat_executes counter (read src) (readStore src) (fun _ => True) 1
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun s _ => by simp [readStore, Op.apply, hne])
    (fun s _ => ⟨1, le_refl _, Executes.atom _ _⟩)
    (working base counter src xs ys a scratch) trivial
  have hs : (working base counter src xs ys a scratch).stk counter = xs := by simp [working, hne]
  simpa only [hs, result_drop base counter src hne, Nat.reduceAdd] using! h

lemma dropCount_store (counter src : K) (hne : counter ≠ src) (s : BitStore K Aux) :
    ∃ t, t ≤ 3 * (s.stk counter).length + 2 ∧ Executes (dropCount counter src) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk counter []) src
        ((s.stk src).drop (s.stk counter).length)⟩ t := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    dropCount_executes s.stk counter src hne (s.stk counter) (s.stk src) s.state.1 s.state.2

end Lax434930Proofs.InclusionAux.TimeHelpers.StackDrop
