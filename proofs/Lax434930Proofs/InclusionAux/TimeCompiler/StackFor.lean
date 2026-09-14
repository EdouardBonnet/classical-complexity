import Lax434930Proofs.InclusionAux.TimeCompiler.StackClear
import Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackFor

open StackProgram StackTransfer

variable {K Aux α : Type} [DecidableEq K]

def pack (base : α → BitStore K Aux) (counter coord : K) (a : α)
    (i remaining : Nat) (scratch : Option Bool) : BitStore K Aux :=
  working (base a).stk counter coord (List.replicate remaining true) (List.replicate i true)
    (base a).state.1 scratch

def increment (coord : K) : BitProgram K Aux := .atom (.push coord (fun _ => true))

def loopBody (counter coord : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq body (.seq (increment coord) (read counter))

def loop (counter coord : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (loopBody counter coord body)

def forCount (counter coord : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (read counter) (loop counter coord body)

/-- A fixed structured program; the range bound is read from the domain
stack, never captured as an input-dependent program constant. -/
def forValues (domain counter coord tmp : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (StackCopy.copy domain counter tmp)
    (.seq (forCount counter coord body) (StackClear.clear coord))

def foldRange (f : Nat → α → α) (start : Nat) : Nat → α → α
  | 0, a => a
  | n + 1, a => foldRange f (start + 1) n (f start a)

theorem pop_pack (base : α → BitStore K Aux) (counter coord : K) (hne : counter ≠ coord)
    (a : α) (i remaining : Nat) (scratch : Option Bool) :
    Op.apply (.pop counter (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (pack base counter coord a i remaining scratch) =
      pack base counter coord a i (remaining - 1) (if remaining = 0 then none else some true) := by
  have h := pop_working (base a).stk counter coord hne (List.replicate remaining true)
    (List.replicate i true) (base a).state.1 scratch
  cases remaining <;> simpa [pack, List.replicate_succ] using h

theorem increment_pack (base : α → BitStore K Aux) (counter coord : K)
    (a : α) (i remaining : Nat) (scratch : Option Bool) :
    Op.apply (.push coord (fun _ : Aux × Option Bool => true))
      (pack base counter coord a i remaining scratch) =
      pack base counter coord a (i + 1) remaining scratch := by
  apply Store.ext
  · rfl
  · funext key
    by_cases hk : key = coord <;> simp_all [pack, working, Op.apply, List.replicate_succ]

/-- The callback is needed only at indices below n. Its result can change
the semantic payload and scratch register, while retaining the loop counters.
Every callback execution is a concrete structured execution with bound B. -/
theorem loop_executes (base : α → BitStore K Aux) (counter coord : K) (hne : counter ≠ coord)
    (body : BitProgram K Aux) (f : Nat → α → α) (n B : Nat)
    (hbody : ∀ i, i < n → ∀ a remaining scratch,
      ∃ cost scratch', cost ≤ B ∧ Executes body
        (pack base counter coord a i remaining scratch)
        (pack base counter coord (f i a) i remaining scratch') cost)
    (start remaining : Nat) (hbound : start + remaining ≤ n) (a : α) :
    ∃ cost, cost ≤ (B + 3) * remaining + 1 ∧
      Executes (loop counter coord body)
        (pack base counter coord a start (remaining - 1) (if remaining = 0 then none else some true))
        (pack base counter coord (foldRange f start remaining a) (start + remaining) 0 none) cost := by
  induction remaining generalizing start a with
  | zero => exact ⟨1, by simp, Executes.loop_false rfl⟩
  | succ remaining ih =>
      obtain ⟨c, scratch, hc, hp⟩ := hbody start (by omega) a remaining (some true)
      have hi := Executes.atom (.push coord (fun _ : Aux × Option Bool => true))
        (pack base counter coord (f start a) start remaining scratch)
      rw [increment_pack] at hi
      have hr := Executes.atom (.pop counter (fun s : Aux × Option Bool => fun b => (s.1, b)))
        (pack base counter coord (f start a) (start + 1) remaining scratch)
      rw [pop_pack base counter coord hne] at hr
      obtain ⟨d, hd, hq⟩ := ih (start + 1) (by omega) (f start a)
      have he := Executes.loop_true (b := fun s : Aux × Option Bool => s.2.isSome) rfl
        (Executes.seq hp (Executes.seq hi hr)) hq
      refine ⟨(c + (1 + 1)) + d + 1, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · simpa only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          if_false, foldRange, Nat.add_assoc, Nat.add_comm 1 remaining] using! he

theorem forCount_executes (base : α → BitStore K Aux) (counter coord : K) (hne : counter ≠ coord)
    (body : BitProgram K Aux) (f : Nat → α → α) (n B : Nat)
    (hbody : ∀ i, i < n → ∀ a remaining scratch,
      ∃ cost scratch', cost ≤ B ∧ Executes body
        (pack base counter coord a i remaining scratch)
        (pack base counter coord (f i a) i remaining scratch') cost)
    (a : α) (scratch : Option Bool) :
    ∃ cost, cost ≤ (B + 3) * n + 2 ∧
      Executes (forCount counter coord body) (pack base counter coord a 0 n scratch)
        (pack base counter coord (foldRange f 0 n a) n 0 none) cost := by
  have hr := Executes.atom (.pop counter (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (pack base counter coord a 0 n scratch)
  rw [pop_pack base counter coord hne] at hr
  obtain ⟨c, hc, hp⟩ := loop_executes base counter coord hne body f n B hbody 0 n (by omega) a
  simp only [Nat.zero_add] at hp
  exact ⟨1 + c, by omega, Executes.seq hr hp⟩

def reset (s : BitStore K Aux) : BitStore K Aux := ⟨(s.state.1, none), s.stk⟩

theorem forValues_executes (base : α → BitStore K Aux) (domain counter coord tmp : K)
    (hsep : [domain, counter, coord, tmp].Nodup)
    (body : BitProgram K Aux) (f : Nat → α → α) (n B : Nat)
    (hcounter : ∀ a, (base a).stk counter = []) (hcoord : ∀ a, (base a).stk coord = [])
    (htmp : ∀ a, (base a).stk tmp = [])
    (hbody : ∀ i, i < n → ∀ a remaining scratch,
      ∃ cost scratch', cost ≤ B ∧ Executes body
        (pack base counter coord a i remaining scratch)
        (pack base counter coord (f i a) i remaining scratch') cost)
    (a : α) (hdomain : (base a).stk domain = List.replicate n true) :
    ∃ cost, cost ≤ (B + 12) * n + 8 ∧
      Executes (forValues domain counter coord tmp body) (base a) (reset (base (foldRange f 0 n a))) cost := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have hdc : domain ≠ counter := by tauto
  have hdt : domain ≠ tmp := by tauto
  have hct : counter ≠ tmp := by tauto
  have hcc : counter ≠ coord := by tauto
  have hcopy := StackCopy.copy_store domain counter tmp hdc hdt hct (base a) (htmp a)
  rw [hdomain, hcounter, List.append_nil, List.length_replicate] at hcopy
  have he : (⟨((base a).state.1, none), Function.update (base a).stk counter (List.replicate n true)⟩ :
      BitStore K Aux) = pack base counter coord a 0 n none := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hc : key = coord
      · subst key; simp [pack, working, Ne.symm hcc, hcoord]
      · simp [pack, working, hc]
  rw [he] at hcopy
  obtain ⟨c, hc, hfor⟩ := forCount_executes base counter coord hcc body f n B hbody a none
  have hclear := StackClear.clear_store coord (pack base counter coord (foldRange f 0 n a) n 0 none)
  have hp : (pack base counter coord (foldRange f 0 n a) n 0 none).stk coord = List.replicate n true := by
    simp [pack, working]
  rw [hp, List.length_replicate] at hclear
  have he' : (⟨((pack base counter coord (foldRange f 0 n a) n 0 none).state.1, none),
      Function.update (pack base counter coord (foldRange f 0 n a) n 0 none).stk coord []⟩ : BitStore K Aux) =
      reset (base (foldRange f 0 n a)) := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hk : key = counter
      · subst key; simp [pack, working, reset, hcc, hcounter]
      · by_cases hk' : key = coord
        · subst key; simp [pack, working, reset, hcoord]
        · simp [pack, working, reset, hk, hk']
  rw [he'] at hclear
  refine ⟨(7 * n + 4) + (c + (2 * n + 2)), ?_, Executes.seq hcopy (Executes.seq hfor hclear)⟩
  simp only [Nat.add_mul] at hc ⊢
  omega

theorem foldRange_eq_foldl (f : Nat → α → α) (start count : Nat) (a : α) :
    foldRange f start count a = (List.range' start count).foldl (fun a i => f i a) a := by
  induction count generalizing start a with
  | zero => rfl
  | succ count ih => rw [foldRange, List.range'_succ, List.foldl_cons, ih]

theorem foldRange_zero_eq (f : Nat → α → α) (n : Nat) (a : α) :
    foldRange f 0 n a = (List.range n).foldl (fun a i => f i a) a := by
  rw [foldRange_eq_foldl, List.range_eq_range']

end Lax434930Proofs.InclusionAux.TimeCompiler.StackFor
