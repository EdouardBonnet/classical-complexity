import Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackClear

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def clearLoop (src : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (read src)

def clear (src : K) : BitProgram K Aux := .seq (read src) (clearLoop src)

def working (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(a, scratch), Function.update base src xs⟩

theorem pop_working (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (scratch : Option Bool) :
    Op.apply (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base src xs a scratch) = working base src xs.tail a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working]
  · funext k
    by_cases hk : k = src <;> simp_all [Op.apply, working]

theorem clearLoop_executes (base : K → List Bool) (src : K) (xs : List Bool) (a : Aux) :
    Executes (clearLoop src) (working base src xs.tail a xs.head?)
      (working base src [] a none) (2 * xs.length + 1) := by
  induction xs with
  | nil => exact Executes.loop_false rfl
  | cons b bs ih =>
      have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
        (working base src bs a (some b))
      rw [pop_working] at hr
      have hh := Executes.loop_true (b := fun s : Aux × Option Bool => s.2.isSome) rfl hr ih
      have ht : 1 + (2 * bs.length + 1) + 1 = 2 * (bs.length + 1) + 1 := by omega
      simpa only [List.tail_cons, List.head?_cons, List.length_cons, ht] using! hh

theorem clear_executes (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (scratch : Option Bool) :
    Executes (clear src) (working base src xs a scratch)
      (working base src [] a none) (2 * xs.length + 2) := by
  have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working base src xs a scratch)
  rw [pop_working] at hr
  have hh := Executes.seq hr (clearLoop_executes base src xs a)
  have ht : 1 + (2 * xs.length + 1) = 2 * xs.length + 2 := by omega
  simpa only [ht] using! hh

theorem clear_store (src : K) (s : BitStore K Aux) :
    Executes (clear src) s ⟨(s.state.1, none), Function.update s.stk src []⟩
      (2 * (s.stk src).length + 2) := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    clear_executes s.stk src (s.stk src) s.state.1 s.state.2

end Lax434930Proofs.InclusionAux.TimeCompiler.StackClear
