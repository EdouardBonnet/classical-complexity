import Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
import Mathlib.Data.Fintype.Prod

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer

open StackProgram

variable {K Aux : Type}

abbrev BitStore (K Aux : Type) := Store (fun _ : K => Bool) (Aux × Option Bool)
abbrev BitProgram (K Aux : Type) := Program (fun _ : K => Bool) (Aux × Option Bool)

def read (src : K) : BitProgram K Aux :=
  .atom (.pop src (fun s b => (s.1, b)))

def transferBody (src dst : K) : BitProgram K Aux :=
  .seq (.atom (.push dst (fun s => s.2.getD false))) (read src)

def transferLoop (src dst : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (transferBody src dst)

/-- Move a bit string from one stack onto another, in reversed order.
The auxiliary finite state and every other stack are preserved. -/
def transfer (src dst : K) : BitProgram K Aux :=
  .seq (read src) (transferLoop src dst)

def working [DecidableEq K] (base : K → List Bool) (src dst : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(a, scratch), Function.update (Function.update base src xs) dst ys⟩

theorem pop_working [DecidableEq K] (base : K → List Bool) (src dst : K)
    (hne : src ≠ dst) (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Op.apply (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base src dst xs ys a scratch) =
      working base src dst xs.tail ys a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working, hne]
  · funext k
    by_cases hs : k = src <;> by_cases hd : k = dst <;>
      simp_all [Op.apply, working]

theorem push_working [DecidableEq K] (base : K → List Bool) (src dst : K)
    (xs ys : List Bool) (a : Aux) (b : Bool) :
    Op.apply (.push dst (fun s : Aux × Option Bool => s.2.getD false))
      (working base src dst xs ys a (some b)) =
      working base src dst xs (b :: ys) a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hd : k = dst <;> simp_all [Op.apply, working, Function.update_apply]

theorem transferLoop_executes [DecidableEq K] (base : K → List Bool) (src dst : K)
    (hne : src ≠ dst) (xs ys : List Bool) (a : Aux) :
    Executes (transferLoop src dst)
      (working base src dst xs.tail ys a xs.head?)
      (working base src dst [] (xs.reverse ++ ys) a none) (3 * xs.length + 1) := by
  induction xs generalizing ys with
  | nil => exact Executes.loop_false rfl
  | cons b bs ih =>
      have hp := Executes.atom (.push dst (fun s : Aux × Option Bool => s.2.getD false))
        (working base src dst bs ys a (some b))
      rw [push_working] at hp
      have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
        (working base src dst bs (b :: ys) a (some b))
      rw [pop_working base src dst hne] at hr
      have hh := Executes.loop_true (p := transferBody src dst)
        (b := fun s : Aux × Option Bool => s.2.isSome) rfl
        (Executes.seq hp hr) (ih (b :: ys))
      have ht : (1 + 1) + (3 * bs.length + 1) + 1 = 3 * (bs.length + 1) + 1 := by omega
      simpa only [List.tail_cons, List.head?_cons, List.reverse_cons,
        List.length_cons, List.append_assoc, List.singleton_append, ht] using! hh

theorem transfer_executes [DecidableEq K] (base : K → List Bool) (src dst : K)
    (hne : src ≠ dst) (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Executes (transfer src dst) (working base src dst xs ys a scratch)
      (working base src dst [] (xs.reverse ++ ys) a none) (3 * xs.length + 2) := by
  have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working base src dst xs ys a scratch)
  rw [pop_working base src dst hne] at hr
  have h := Executes.seq hr (transferLoop_executes base src dst hne xs ys a)
  have ht : 1 + (3 * xs.length + 1) = 3 * xs.length + 2 := by omega
  simpa only [ht] using! h

theorem transfer_store [DecidableEq K] (src dst : K) (hne : src ≠ dst)
    (s : BitStore K Aux) :
    Executes (transfer src dst) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk src []) dst
        ((s.stk src).reverse ++ s.stk dst)⟩ (3 * (s.stk src).length + 2) := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    transfer_executes s.stk src dst hne (s.stk src) (s.stk dst) s.state.1 s.state.2

theorem working_input (xs : List Bool) :
    working (fun _ : Bool => []) false true xs [] () none =
      ioStore false ((), none) xs := by
  apply Store.ext
  · rfl
  · funext k
    cases k <;> rfl

theorem working_output (xs : List Bool) :
    working (fun _ : Bool => []) false true [] xs () none =
      ioStore true ((), none) xs := by
  apply Store.ext
  · rfl
  · funext k
    cases k <;> rfl

/-- An end-to-end use of the compiler, including the required input/output
stack convention and finite-control reset. -/
theorem reverse_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id List.reverse) := by
  apply program_polytime (transfer (Aux := Unit) false true) false true ((), none)
    id id List.reverse (Polynomial.C 3 * Polynomial.X + 2)
  intro xs
  refine ⟨3 * xs.length + 2, by simp, ?_⟩
  simpa only [List.append_nil, working_input, working_output] using!
    transfer_executes (fun _ : Bool => []) false true (by decide) xs [] () none

end Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
