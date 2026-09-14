import Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
import Lax434930Proofs.PolynomialComposition

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.StackMapTransfer

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer

variable {K Aux : Type} [DecidableEq K]

def body (src dst : K) (f : Bool → Bool) : BitProgram K Aux :=
  .seq (.atom (.push dst (fun s => f (s.2.getD false)))) (read src)

def loop (src dst : K) (f : Bool → Bool) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (body src dst f)

def transfer (src dst : K) (f : Bool → Bool) : BitProgram K Aux :=
  .seq (read src) (loop src dst f)

lemma loop_executes (base : K → List Bool) (src dst : K) (hne : src ≠ dst)
    (f : Bool → Bool) (xs ys : List Bool) (a : Aux) :
    Executes (loop src dst f) (working base src dst xs.tail ys a xs.head?)
      (working base src dst [] ((xs.map f).reverse ++ ys) a none) (3 * xs.length + 1) := by
  induction xs generalizing ys with
  | nil => exact Executes.loop_false rfl
  | cons b bs ih =>
    have hp := Executes.atom (.push dst (fun s : Aux × Option Bool => f (s.2.getD false)))
      (working base src dst bs ys a (some b))
    have he : Op.apply (.push dst (fun s : Aux × Option Bool => f (s.2.getD false)))
        (working base src dst bs ys a (some b)) = working base src dst bs (f b :: ys) a (some b) := by
      apply Store.ext
      · rfl
      · funext k; by_cases hk : k = dst <;> simp_all [Op.apply, working]
    rw [he] at hp
    have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base src dst bs (f b :: ys) a (some b))
    rw [pop_working base src dst hne] at hr
    have hh := Executes.loop_true (p := body src dst f)
      (b := fun s : Aux × Option Bool => s.2.isSome) rfl (.seq hp hr) (ih (f b :: ys))
    have hc : (1 + 1) + (3 * bs.length + 1) + 1 = 3 * (bs.length + 1) + 1 := by omega
    simpa only [loop, List.tail_cons, List.head?_cons, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.length_cons, hc] using! hh

lemma transfer_executes (base : K → List Bool) (src dst : K) (hne : src ≠ dst)
    (f : Bool → Bool) (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Executes (transfer src dst f) (working base src dst xs ys a scratch)
      (working base src dst [] ((xs.map f).reverse ++ ys) a none) (3 * xs.length + 2) := by
  have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working base src dst xs ys a scratch)
  rw [pop_working base src dst hne] at hr
  have hc : 1 + (3 * xs.length + 1) = 3 * xs.length + 2 := by omega
  simpa only [hc] using! Executes.seq hr (loop_executes base src dst hne f xs ys a)

lemma transfer_store (src dst : K) (hne : src ≠ dst) (f : Bool → Bool) (s : BitStore K Aux) :
    Executes (transfer src dst f) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk src []) dst
        (((s.stk src).map f).reverse ++ s.stk dst)⟩ (3 * (s.stk src).length + 2) := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    transfer_executes s.stk src dst hne f (s.stk src) (s.stk dst) s.state.1 s.state.2

end Lax434930Proofs.InclusionAux.TimeHelpers.StackMapTransfer
