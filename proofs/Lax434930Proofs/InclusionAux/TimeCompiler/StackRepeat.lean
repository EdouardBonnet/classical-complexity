import Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackRepeat

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- The pure effect of reading one counter token into scratch control. -/
def readStore (counter : K) (s : BitStore K Aux) : BitStore K Aux :=
  Op.apply (.pop counter (fun q b => (q.1, b))) s

@[simp] theorem readStore_counter (counter : K) (s : BitStore K Aux) :
    (readStore counter s).stk counter = (s.stk counter).tail := by
  simp [readStore, Op.apply]

@[simp] theorem readStore_scratch (counter : K) (s : BitStore K Aux) :
    (readStore counter s).state.2 = (s.stk counter).head? := rfl

def repeatLoop (counter : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (.seq body (read counter))

/-- Execute the body once per token on a private counter stack. The body
may change scratch control, but must preserve the remaining counter. -/
def repeatCount (counter : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (read counter) (repeatLoop counter body)

/-- Mathematical result of the bounded iteration, including the final read
that detects exhaustion and clears scratch control. -/
def result (counter : K) (f : BitStore K Aux → BitStore K Aux) :
    Nat → BitStore K Aux → BitStore K Aux
  | 0, s => readStore counter s
  | n + 1, s => result counter f n (f (readStore counter s))

theorem repeatLoop_executes (counter : K) (body : BitProgram K Aux)
    (f : BitStore K Aux → BitStore K Aux) (Valid : BitStore K Aux → Prop) (B : Nat)
    (hread : ∀ s, Valid s → Valid (readStore counter s))
    (hf : ∀ s, Valid s → Valid (f s))
    (hframe : ∀ s, Valid s → (f s).stk counter = s.stk counter)
    (hbody : ∀ s, Valid s → ∃ c, c ≤ B ∧ Executes body s (f s) c)
    (s : BitStore K Aux) (hs : Valid s) :
    ∃ c, c ≤ (B + 2) * (s.stk counter).length + 1 ∧
      Executes (repeatLoop counter body) (readStore counter s)
        (result counter f (s.stk counter).length s) c := by
  generalize hn : (s.stk counter).length = n
  induction n generalizing s with
  | zero =>
      have he : s.stk counter = [] := List.length_eq_zero_iff.mp hn
      refine ⟨1, by omega, ?_⟩
      exact Executes.loop_false (by simp [readStore_scratch, he])
  | succ n ih =>
      have hr := hread s hs
      obtain ⟨a, ha, hb⟩ := hbody (readStore counter s) hr
      have he : (f (readStore counter s)).stk counter = (s.stk counter).tail := by
        rw [hframe _ hr, readStore_counter]
      have hn' : ((f (readStore counter s)).stk counter).length = n := by
        rw [he, List.length_tail, hn]
        omega
      obtain ⟨c, hc, hh⟩ := ih (f (readStore counter s)) (hf _ hr) hn'
      have hp : Executes (read counter) (f (readStore counter s))
          (readStore counter (f (readStore counter s))) 1 := Executes.atom _ _
      have guard : (readStore counter s).state.2.isSome = true := by
        simp only [readStore_scratch]
        cases he' : s.stk counter with
        | nil => simp [he'] at hn
        | cons b bs => rfl
      refine ⟨(a + 1) + c + 1, ?_, Executes.loop_true guard (Executes.seq hb hp) hh⟩
      simp only [Nat.mul_succ]
      omega

theorem repeat_executes (counter : K) (body : BitProgram K Aux)
    (f : BitStore K Aux → BitStore K Aux) (Valid : BitStore K Aux → Prop) (B : Nat)
    (hread : ∀ s, Valid s → Valid (readStore counter s))
    (hf : ∀ s, Valid s → Valid (f s))
    (hframe : ∀ s, Valid s → (f s).stk counter = s.stk counter)
    (hbody : ∀ s, Valid s → ∃ c, c ≤ B ∧ Executes body s (f s) c)
    (s : BitStore K Aux) (hs : Valid s) :
    ∃ c, c ≤ (B + 2) * (s.stk counter).length + 2 ∧
      Executes (repeatCount counter body) s (result counter f (s.stk counter).length s) c := by
  obtain ⟨c, hc, hh⟩ := repeatLoop_executes counter body f Valid B hread hf hframe hbody s hs
  exact ⟨1 + c, by omega, Executes.seq (Executes.atom _ _) hh⟩

theorem result_spec (counter : K) (f : BitStore K Aux → BitStore K Aux)
    (Valid : BitStore K Aux → Prop)
    (hread : ∀ s, Valid s → Valid (readStore counter s))
    (hf : ∀ s, Valid s → Valid (f s))
    (hframe : ∀ s, Valid s → (f s).stk counter = s.stk counter)
    (s : BitStore K Aux) (hs : Valid s) :
    let t := result counter f (s.stk counter).length s
    Valid t ∧ t.stk counter = [] ∧ t.state.2 = none := by
  generalize hn : (s.stk counter).length = n
  induction n generalizing s with
  | zero =>
      have he : s.stk counter = [] := List.length_eq_zero_iff.mp hn
      exact ⟨hread s hs, by simp [result, he], by simp [result, he]⟩
  | succ n ih =>
      apply ih _ (hf _ (hread s hs))
      rw [hframe _ (hread s hs), readStore_counter, List.length_tail, hn]
      omega

end Lax434930Proofs.InclusionAux.TimeCompiler.StackRepeat
