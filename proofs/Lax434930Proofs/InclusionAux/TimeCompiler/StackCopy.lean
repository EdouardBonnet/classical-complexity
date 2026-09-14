import Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def working3 (base : K → List Bool) (src left right : K)
    (xs ys zs : List Bool) (a : Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(a, scratch), Function.update (Function.update (Function.update base src xs) left ys)
    right zs⟩

def forkBody (src left right : K) : BitProgram K Aux :=
  .seq (.atom (.push left (fun s => s.2.getD false)))
    (.seq (.atom (.push right (fun s => s.2.getD false))) (read src))

def forkLoop (src left right : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (forkBody src left right)

/-- Consume a string, pushing its reverse onto each of two target stacks. -/
def fork (src left right : K) : BitProgram K Aux :=
  .seq (read src) (forkLoop src left right)

theorem pop_working3 (base : K → List Bool) (src left right : K)
    (hl : src ≠ left) (hr : src ≠ right) (xs ys zs : List Bool)
    (a : Aux) (scratch : Option Bool) :
    Op.apply (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working3 base src left right xs ys zs a scratch) =
      working3 base src left right xs.tail ys zs a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working3, hl, hr]
  · funext k
    by_cases hs : k = src <;> by_cases hl : k = left <;> by_cases hr : k = right <;>
      simp_all [Op.apply, working3]

theorem push_left (base : K → List Bool) (src left right : K)
    (h : left ≠ right) (xs ys zs : List Bool) (a : Aux) (b : Bool) :
    Op.apply (.push left (fun s : Aux × Option Bool => s.2.getD false))
      (working3 base src left right xs ys zs a (some b)) =
      working3 base src left right xs (b :: ys) zs a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hl : k = left <;> by_cases hr : k = right <;>
      simp_all [Op.apply, working3]

theorem push_right (base : K → List Bool) (src left right : K)
    (xs ys zs : List Bool) (a : Aux) (b : Bool) :
    Op.apply (.push right (fun s : Aux × Option Bool => s.2.getD false))
      (working3 base src left right xs ys zs a (some b)) =
      working3 base src left right xs ys (b :: zs) a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hr : k = right <;> simp_all [Op.apply, working3, Function.update_apply]

theorem forkLoop_executes (base : K → List Bool) (src left right : K)
    (hl : src ≠ left) (hr : src ≠ right) (hlr : left ≠ right)
    (xs ys zs : List Bool) (a : Aux) :
    Executes (forkLoop src left right)
      (working3 base src left right xs.tail ys zs a xs.head?)
      (working3 base src left right [] (xs.reverse ++ ys) (xs.reverse ++ zs) a none)
      (4 * xs.length + 1) := by
  induction xs generalizing ys zs with
  | nil => exact Executes.loop_false rfl
  | cons b bs ih =>
      have hp := Executes.atom (.push left (fun s : Aux × Option Bool => s.2.getD false))
        (working3 base src left right bs ys zs a (some b))
      rw [push_left base src left right hlr] at hp
      have hq := Executes.atom (.push right (fun s : Aux × Option Bool => s.2.getD false))
        (working3 base src left right bs (b :: ys) zs a (some b))
      rw [push_right] at hq
      have hr' := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
        (working3 base src left right bs (b :: ys) (b :: zs) a (some b))
      rw [pop_working3 base src left right hl hr] at hr'
      have hh := Executes.loop_true (p := forkBody src left right)
        (b := fun s : Aux × Option Bool => s.2.isSome) rfl
        (Executes.seq hp (Executes.seq hq hr')) (ih (b :: ys) (b :: zs))
      have ht : (1 + (1 + 1)) + (4 * bs.length + 1) + 1 =
          4 * (bs.length + 1) + 1 := by omega
      simpa only [List.tail_cons, List.head?_cons, List.reverse_cons,
        List.length_cons, List.append_assoc, List.singleton_append, ht] using! hh

theorem fork_executes (base : K → List Bool) (src left right : K)
    (hl : src ≠ left) (hr : src ≠ right) (hlr : left ≠ right)
    (xs ys zs : List Bool) (a : Aux) (scratch : Option Bool) :
    Executes (fork src left right)
      (working3 base src left right xs ys zs a scratch)
      (working3 base src left right [] (xs.reverse ++ ys) (xs.reverse ++ zs) a none)
      (4 * xs.length + 2) := by
  have hr' := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working3 base src left right xs ys zs a scratch)
  rw [pop_working3 base src left right hl hr] at hr'
  have h := Executes.seq hr' (forkLoop_executes base src left right hl hr hlr xs ys zs a)
  have ht : 1 + (4 * xs.length + 1) = 4 * xs.length + 2 := by omega
  simpa only [ht] using! h

/-- Copy onto a target stack using an initially empty temporary stack.
The source string is restored in its original order. -/
def copy (src dst tmp : K) : BitProgram K Aux :=
  .seq (transfer src tmp) (fork tmp src dst)

theorem copy_executes (base : K → List Bool) (src dst tmp : K)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Executes (copy src dst tmp)
      (working3 base src dst tmp xs ys [] a scratch)
      (working3 base src dst tmp xs (xs ++ ys) [] a none) (7 * xs.length + 4) := by
  have layout (us vs ws : List Bool) (b : Option Bool) :
      working (Function.update base dst vs) src tmp us ws a b =
        working3 base src dst tmp us vs ws a b := by
    apply Store.ext
    · rfl
    · funext k
      by_cases hs : k = src <;> by_cases hd : k = dst <;> by_cases ht : k = tmp <;>
        simp_all [working, working3]
  have permute (us vs ws : List Bool) (b : Option Bool) :
      working3 base tmp src dst ws us vs a b =
        working3 base src dst tmp us vs ws a b := by
    apply Store.ext
    · rfl
    · funext k
      by_cases hs : k = src <;> by_cases hd : k = dst <;> by_cases ht : k = tmp <;>
        simp_all [working3]
  have ht := transfer_executes (Function.update base dst ys) src tmp hst xs [] a scratch
  simp only [List.append_nil, layout] at ht
  have hf := fork_executes base tmp src dst (Ne.symm hst) (Ne.symm hdt) hsd
    xs.reverse [] ys a none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse, permute] at hf
  have h := Executes.seq ht hf
  have hc : (3 * xs.length + 2) + (4 * xs.length + 2) = 7 * xs.length + 4 := by omega
  simpa only [copy, hc] using h

/-- Store-level interface: only the destination contents and scratch control
change; the temporary stack is empty both before and after the operation. -/
theorem copy_store (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : BitStore K Aux) (ht : s.stk tmp = []) :
    Executes (copy src dst tmp) s
      ⟨(s.state.1, none), Function.update s.stk dst (s.stk src ++ s.stk dst)⟩
      (7 * (s.stk src).length + 4) := by
  have h := copy_executes s.stk src dst tmp hsd hst hdt
    (s.stk src) (s.stk dst) s.state.1 s.state.2
  have hin : working3 s.stk src dst tmp (s.stk src) (s.stk dst) [] s.state.1 s.state.2 = s := by
    simp only [working3, Function.update_eq_self, ← ht, Prod.mk.eta]
  have hout : working3 s.stk src dst tmp (s.stk src) (s.stk src ++ s.stk dst) []
      s.state.1 none =
      (⟨(s.state.1, none), Function.update s.stk dst (s.stk src ++ s.stk dst)⟩ : BitStore K Aux) := by
    apply Store.ext
    · rfl
    · funext k
      by_cases hk : k = tmp
      · subst k; simp [working3, Ne.symm hdt, ht]
      · simp [working3, hk]
  rw [hin, hout] at h
  exact h

end Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy
