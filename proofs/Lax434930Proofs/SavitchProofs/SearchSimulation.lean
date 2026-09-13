import Lax434930Proofs.SavitchProofs.SearchCode

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.SearchProgram

open StackSearch StackMacros
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Good Exec assigned popped pushed)
open scoped Classical

noncomputable section

variable {β ε δ : Type}

def MemoryFits (m : ℕ) (s : State (2 ^ m)) (d : Data β ε δ) : Prop :=
  ∀ r, d.store (key r) = store m s r

lemma memory_room (m : ℕ) (s : State (2 ^ m)) (d : Data β ε δ)
    (hs : s.Valid m) (hd : MemoryFits m s d) (r : Register) :
    (d.store (key r)).length + m + 1 < budget m := by
  rw [hd r]
  exact store_lt_budget m s hs r

lemma clearActive_guard (w : Word) (b : ℕ) (d : Data β ε δ) :
    (clearActive (β := β) (ε := ε) (δ := δ)).guard w b d := by
  simp [clearActive, Macro.seq, Macro.clear]

lemma return_guard (w : Word) (b : ℕ) (d : Data β ε δ) (answer : Context β ε → Bool) :
    (returnValue answer).guard w b d := by
  simp [returnValue, clearActive, Macro.seq, Macro.clear, Macro.assign]

lemma saveFields_guard (w : Word) (m : ℕ) (k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (hs : (State.scan k a b mid stack).Valid m) (d : Data β ε δ)
    (hd : MemoryFits m (.scan k a b mid stack) d) :
    (saveFields (β := β) (ε := ε) (δ := δ)).guard w (budget m) d := by
  have hA := memory_room m _ d hs hd .frameA
  have hB := memory_room m _ d hs hd .frameB
  have hM := memory_room m _ d hs hd .frameMiddle
  have hD := memory_room m _ d hs hd .frameDepth
  have hk := hs.1
  have ha : d.store (key .aux) = [] := hd .aux
  have h₁ : (d.store (key .a)).length = m := by rw [hd .a]; simp [store]
  have h₂ : (d.store (key .b)).length = m := by rw [hd .b]; simp [store]
  have h₃ : (d.store (key .middle)).length = m := by rw [hd .middle]; simp [store]
  have h₄ : (d.store (key .depth)).length = k := by rw [hd .depth]; simp [store]
  simp only [key] at hA hB hM hD ha h₁ h₂ h₃ h₄
  simp [saveFields, Macro.seq, Macro.save, key, ha, h₁, h₂, h₃, h₄]
  omega

lemma descendLeft_guard (w : Word) (m k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (hs : (State.scan k a b mid stack).Valid m) (d : Data β ε δ)
    (hd : MemoryFits m (.scan k a b mid stack) d) :
    (descendLeft (β := β) (ε := ε) (δ := δ)).guard w (budget m) d := by
  have hsave := saveFields_guard w m k a b mid stack hs d hd
  have hr := memory_room m _ d hs hd .kinds
  have ha : d.store (key .aux) = [] := hd .aux
  simpa [descendLeft, saveFields, setPhase, Macro.seq, Macro.save, Macro.push, Macro.copy,
    Macro.clear, Macro.assign, StackRoutines.cleared, pushed, key] using
    And.intro hsave ⟨(show (d.store (key .kinds)).length + 1 < budget m by omega), ha⟩

lemma descendRight_guard (w : Word) (m k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (hs : (State.scan k a b mid stack).Valid m) (d : Data β ε δ)
    (hd : MemoryFits m (.scan k a b mid stack) d) :
    (descendRight (β := β) (ε := ε) (δ := δ)).guard w (budget m) d := by
  have hsave := saveFields_guard w m k a b mid stack hs d hd
  have hr := memory_room m _ d hs hd .kinds
  have ha : d.store (key .aux) = [] := hd .aux
  simpa [descendRight, saveFields, setPhase, Macro.seq, Macro.save, Macro.push, Macro.copy,
    Macro.clear, Macro.assign, StackRoutines.cleared, pushed, key] using
    And.intro hsave ⟨(show (d.store (key .kinds)).length + 1 < budget m by omega), ha⟩

lemma descendLeft_fits (w : Word) (m k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : MemoryFits m (.scan k a b mid stack) d) :
    Fits m (.call k a mid (.left k a b mid :: stack)) (descendLeft.result w d) := by
  refine ⟨rfl, ?_, trivial⟩
  intro r
  cases r <;>
    simp [descendLeft, saveFields, setPhase, Macro.seq, Macro.save, Macro.push, Macro.copy,
      Macro.clear, Macro.assign, assigned, pushed, StackRoutines.cleared, key,
      show ∀ r, d.store (.inl r) = store m (.scan k a b mid stack) r from hd,
      store, stackStore, column_cons, Frame.first, Frame.second, Frame.middle, Frame.kind, Frame.depth]

lemma descendRight_fits (w : Word) (m k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : MemoryFits m (.scan k a b mid stack) d) :
    Fits m (.call k mid b (.right k a b mid :: stack)) (descendRight.result w d) := by
  refine ⟨rfl, ?_, trivial⟩
  intro r
  cases r <;>
    simp [descendRight, saveFields, setPhase, Macro.seq, Macro.save, Macro.push, Macro.copy,
      Macro.clear, Macro.assign, assigned, pushed, StackRoutines.cleared, key,
      show ∀ r, d.store (.inl r) = store m (.scan k a b mid stack) r from hd,
      store, stackStore, column_cons, Frame.first, Frame.second, Frame.middle, Frame.kind, Frame.depth]

lemma nextMiddle_guard (w : Word) (bound m k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : MemoryFits m (.scan k a b mid stack) d) :
    (nextMiddle (β := β) (ε := ε) (δ := δ)).guard w bound d := by
  simp [nextMiddle, Macro.seq, Macro.increment, Macro.assign, key,
    show ∀ r, d.store (.inl r) = store m (.scan k a b mid stack) r from hd,
    store, stackStore, word]

lemma nextMiddle_fits (w : Word) (m k : ℕ) (a b mid : Fin (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : MemoryFits m (.scan k a b mid stack) d) :
    Fits m (.scan k a b (mid + 1) stack) (nextMiddle.result w d) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r
    cases r <;>
      simp [nextMiddle, Macro.seq, Macro.increment, Macro.assign, assigned, key,
        show ∀ r, d.store (.inl r) = store m (.scan k a b mid stack) r from hd,
        store, stackStore, BinaryCounter.word_increment, word, Function.comp_def]
  · simpa [nextMiddle, Macro.seq, Macro.increment, Macro.assign, assigned, key,
      show ∀ r, d.store (.inl r) = store m (.scan k a b mid stack) r from hd,
      store, word_read] using BinaryCounter.word_carry m mid mid.isLt

def stateStack {N : ℕ} : State N → List (Frame N)
  | .call _ _ _ stack | .scan _ _ _ _ stack | .ret _ stack => stack

lemma returnValue_fits (w : Word) (m : ℕ) (s : State (2 ^ m))
    (d : Data β ε δ) (hd : MemoryFits m s d) (answer : Context β ε → Bool) :
    Fits m (.ret (answer {d.state with value := none}) (stateStack s))
      ((returnValue answer).result w d) := by
  refine ⟨rfl, ?_, rfl⟩
  have hh : ∀ r, d.store (.inl r) = store m s r := hd
  intro r
  cases s <;> cases r <;>
    simp [returnValue, clearActive, Macro.seq, Macro.clear, Macro.assign, assigned,
      StackRoutines.cleared, key, hh, store, stackStore, stateStack]

lemma call_successor (w : Word) (m k : ℕ) (a b : Fin (2 ^ m)) (stack)
    (query : Routine β ε δ) (d : Data β ε δ) (hd : Fits m (.call (k + 1) a b stack) d) :
    (onCall query).guard w (budget m) d ∧
      Fits m (.scan k a b 0 stack) ((onCall query).result w d) := by
  have hm := hd.2.1
  have hN : 2 ^ m ≠ 0 := by positivity
  constructor
  · simp [onCall, zeroMiddle, Macro.seq, Macro.read, Macro.branch, Macro.copyMap, Macro.assign,
      popped, key, show ∀ r, d.store (.inl r) = store m (.call (k + 1) a b stack) r from hm,
      store, stackStore, unary, List.replicate_succ]
  · refine ⟨?_, ?_, ?_⟩
    · simp [onCall, zeroMiddle, Macro.seq, Macro.read, Macro.branch, Macro.copyMap, Macro.assign,
        popped, assigned, key,
        show ∀ r, d.store (.inl r) = store m (.call (k + 1) a b stack) r from hm,
        store, stackStore, unary, List.replicate_succ, phase]
    · intro r
      cases r <;>
        simp [onCall, zeroMiddle, Macro.seq, Macro.read, Macro.branch, Macro.copyMap, Macro.assign,
          popped, assigned, key,
          show ∀ r, d.store (.inl r) = store m (.call (k + 1) a b stack) r from hm,
          store, stackStore, unary, List.replicate_succ]
    · simp [onCall, zeroMiddle, Macro.seq, Macro.read, Macro.branch, Macro.copyMap, Macro.assign,
        popped, assigned, key,
        show ∀ r, d.store (.inl r) = store m (.call (k + 1) a b stack) r from hm,
        store, stackStore, unary, List.replicate_succ, Ne.symm hN]

def QueryCorrect (query : Routine β ε δ) (G : ∀ (_ : Word) (m : ℕ), Lax434930Proofs.SavitchDefinitions.Reachability.Graph (2 ^ m)) : Prop :=
  ∀ w m a b stack (d : Data β ε δ), Good w (budget m) d → Fits m (.call 0 a b stack) d →
    query.guard w (budget m) d ∧ Fits m (.call 0 a b stack) (query.result w d) ∧
      (query.result w d).state.user.answer = G w m a b

lemma call_zero (w : Word) (m : ℕ) (a b : Fin (2 ^ m)) (stack)
    (query : Routine β ε δ) (G) (hquery : QueryCorrect query G)
    (d : Data β ε δ) (hg : Good w (budget m) d) (hd : Fits m (.call 0 a b stack) d) :
    (onCall query).guard w (budget m) d ∧
      Fits m (.ret (decide (a = b) || G w m a b) stack) ((onCall query).result w d) := by
  let dr := (Macro.read (key .depth)).result w d
  have hdepth : d.store (key .depth) = [] := hd.2.1 .depth
  simp only [key] at hdepth
  have hr : Exec w (budget m) (Macro.read (key .depth)).code d dr :=
    (Macro.read (key .depth)).correct w (budget m) d hg trivial
  have hrf : Fits m (.call 0 a b stack) dr := by
    refine ⟨hd.1, ?_, trivial⟩
    intro r
    cases r <;>
      simp [dr, Macro.read, popped, key,
        show ∀ r, d.store (.inl r) = store m (.call 0 a b stack) r from hd.2.1,
        store, stackStore, unary]
  obtain ⟨hq, hqf, hqv⟩ := hquery w m a b stack dr hr.good.2 hrf
  have hpost : Fits m (.ret (decide (a = b) || G w m a b) stack)
      ((returnValue (fun s => s.user.answer || s.flag)).result w
        ((Macro.compare (key .a) (key .b)).result w (query.result w dr))) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro r
      cases r <;>
        simp [returnValue, clearActive, Macro.seq, Macro.clear, Macro.assign, Macro.compare,
          assigned, StackRoutines.cleared, key,
          show ∀ r, (query.result w dr).store (.inl r) = store m (.call 0 a b stack) r from hqf.2.1,
          store, stackStore]
    · simpa [returnValue, clearActive, Macro.seq, Macro.clear, Macro.assign, Macro.compare,
        assigned, StackRoutines.cleared, hqv, hqf.2.1, store, word_eq_fin_iff, Bool.or_comm]
  constructor
  · simpa [onCall, Macro.seq, Macro.read, Macro.branch, Macro.compare, return_guard, popped,
      hdepth, key, dr] using hq
  · simpa [onCall, Macro.seq, Macro.read, Macro.branch, popped, hdepth, dr, key] using hpost

lemma popFrame_guard (w : Word) (bound m : ℕ) (answer : Bool) (frame : Frame (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : Fits m (.ret answer (frame :: stack)) d) :
    (popFrame (β := β) (ε := ε) (δ := δ)).guard w bound d := by
  have hh : ∀ r, d.store (.inl r) = store m (.ret answer (frame :: stack)) r := hd.2.1
  cases frame <;>
    simp [popFrame, restoreFields, Macro.seq, Macro.read, Macro.assign, Macro.restore,
      assigned, popped, key, hh, store, stackStore, column_cons,
      Frame.first, Frame.second, Frame.middle, Frame.kind, Frame.depth]

lemma popFrame_memory (w : Word) (m : ℕ) (answer : Bool) (frame : Frame (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : Fits m (.ret answer (frame :: stack)) d) :
    MemoryFits m (.scan frame.depth (Frame.first frame) (Frame.second frame) (Frame.middle frame) stack)
      (popFrame.result w d) := by
  have hh : ∀ r, d.store (.inl r) = store m (.ret answer (frame :: stack)) r := hd.2.1
  intro r
  cases frame <;> cases r <;>
    simp [popFrame, restoreFields, Macro.seq, Macro.read, Macro.assign, Macro.restore,
      assigned, popped, key, hh, store, stackStore, column_cons,
      Frame.first, Frame.second, Frame.middle, Frame.kind, Frame.depth,
      Macro.before_append, Macro.after_append]

lemma popFrame_control (w : Word) (m : ℕ) (answer : Bool) (frame : Frame (2 ^ m)) (stack)
    (d : Data β ε δ) (hd : Fits m (.ret answer (frame :: stack)) d) :
    (popFrame.result w d).state.user.answer = answer ∧
    (popFrame.result w d).state.other = some (Frame.kind frame) := by
  have hh : ∀ r, d.store (.inl r) = store m (.ret answer (frame :: stack)) r := hd.2.1
  have hv : d.state.user.answer = answer := hd.2.2
  cases frame <;>
    simp [popFrame, restoreFields, Macro.seq, Macro.read, Macro.assign, Macro.restore,
      assigned, popped, key, hh, hv, store, stackStore, Frame.kind]

lemma frame_valid (m : ℕ) (frame : Frame (2 ^ m)) (stack)
    (h : StackValid m (frame :: stack)) :
    (State.scan frame.depth (Frame.first frame) (Frame.second frame) (Frame.middle frame) stack).Valid m :=
  ⟨h.1, Nat.le_of_lt (Frame.middle frame).isLt, h.2⟩

lemma onReturn_cons_guard (w : Word) (bound : ℕ) (d : Data β ε δ)
    (hn : d.store (key .kinds) ≠ []) :
    (onReturn (β := β) (ε := ε) (δ := δ)).guard w bound d =
      (popFrame.guard w bound d ∧ resumeFrame.guard w bound (popFrame.result w d)) := by
  simp [onReturn, popFrame, Macro.seq, Macro.read, Macro.branch, Macro.assign, popped, hn]

lemma onReturn_cons_result (w : Word) (d : Data β ε δ)
    (hn : d.store (key .kinds) ≠ []) :
    (onReturn (β := β) (ε := ε) (δ := δ)).result w d =
      resumeFrame.result w (popFrame.result w d) := by
  simp [onReturn, popFrame, Macro.seq, Macro.read, Macro.branch, Macro.assign, popped, hn]

lemma resume_frame (w : Word) (m : ℕ) (G : Lax434930Proofs.SavitchDefinitions.Reachability.Graph (2 ^ m))
    (answer : Bool) (frame : Frame (2 ^ m)) (stack) (t : State (2 ^ m))
    (ht : step G (.ret answer (frame :: stack)) = some t)
    (hs : StackValid m (frame :: stack))
    (d : Data β ε δ)
    (hm : MemoryFits m (.scan frame.depth (Frame.first frame) (Frame.second frame) (Frame.middle frame) stack) d)
    (ha : d.state.user.answer = answer) (ho : d.state.other = some (Frame.kind frame)) :
    (resumeFrame (β := β) (ε := ε) (δ := δ)).guard w (budget m) d ∧
      Fits m t (resumeFrame.result w d) := by
  have hv := frame_valid m frame stack hs
  cases frame with
  | left k a b mid =>
    cases answer with
    | false =>
      simp only [step, Option.some.injEq] at ht
      subst t
      simpa [resumeFrame, Macro.branch, ha] using
        And.intro (nextMiddle_guard w (budget m) m k a b mid stack d hm)
          (nextMiddle_fits w m k a b mid stack d hm)
    | true =>
      simp only [step, Option.some.injEq] at ht
      subst t
      simpa [resumeFrame, Macro.branch, ha, ho, Frame.kind] using
        And.intro (descendRight_guard w m k a b mid stack hv d hm)
          (descendRight_fits w m k a b mid stack d hm)
  | right k a b mid =>
    cases answer with
    | false =>
      simp only [step, Option.some.injEq] at ht
      subst t
      simpa [resumeFrame, Macro.branch, ha] using
        And.intro (nextMiddle_guard w (budget m) m k a b mid stack d hm)
          (nextMiddle_fits w m k a b mid stack d hm)
    | true =>
      simp only [step, Option.some.injEq] at ht
      subst t
      simpa [resumeFrame, Macro.branch, ha, ho, Frame.kind, symbol, stateStack] using
        And.intro (return_guard w (budget m) d (fun _ => true))
          (returnValue_fits w m (.scan k a b mid stack) d hm (fun _ => true))

lemma return_step (w : Word) (m : ℕ) (G : Lax434930Proofs.SavitchDefinitions.Reachability.Graph (2 ^ m))
    (answer : Bool) (frame : Frame (2 ^ m)) (stack) (t : State (2 ^ m))
    (ht : step G (.ret answer (frame :: stack)) = some t)
    (hs : (State.ret answer (frame :: stack)).Valid m)
    (d : Data β ε δ) (hd : Fits m (.ret answer (frame :: stack)) d) :
    (onReturn (β := β) (ε := ε) (δ := δ)).guard w (budget m) d ∧
      Fits m t (onReturn.result w d) := by
  have hn : d.store (key .kinds) ≠ [] := by simpa [hd.2.1 .kinds, store, stackStore]
  have hpop := popFrame_guard w (budget m) m answer frame stack d hd
  have hmem := popFrame_memory w m answer frame stack d hd
  have hctrl := popFrame_control w m answer frame stack d hd
  have hresume := resume_frame w m G answer frame stack t ht hs.2 _ hmem hctrl.1 hctrl.2
  exact ⟨(onReturn_cons_guard w (budget m) d hn).mpr ⟨hpop, hresume.1⟩,
    (onReturn_cons_result w d hn).symm ▸ hresume.2⟩

lemma return_nil (w : Word) (m : ℕ) (answer : Bool) (d : Data β ε δ)
    (hd : Fits m (.ret answer []) d) :
    (onReturn (β := β) (ε := ε) (δ := δ)).guard w (budget m) d ∧
      (onReturn.result w d).state.user.phase = .done ∧
      (onReturn.result w d).state.user.answer = answer := by
  have hn : d.store (key .kinds) = [] := hd.2.1 .kinds
  have ha : d.state.user.answer = answer := hd.2.2
  simp [onReturn, Macro.seq, Macro.read, Macro.branch, Macro.assign, setPhase,
    popped, assigned, hn, ha]

lemma scan_step (w : Word) (m k : ℕ) (G : Lax434930Proofs.SavitchDefinitions.Reachability.Graph (2 ^ m))
    (a b : Fin (2 ^ m)) (mid : ℕ) (stack) (t : State (2 ^ m))
    (ht : step G (.scan k a b mid stack) = some t)
    (hs : (State.scan k a b mid stack).Valid m)
    (d : Data β ε δ) (hd : Fits m (.scan k a b mid stack) d) :
    (onScan (β := β) (ε := ε) (δ := δ)).guard w (budget m) d ∧
      Fits m t (onScan.result w d) := by
  by_cases hm : mid < 2 ^ m
  · simp only [step, dif_pos hm, Option.some.injEq] at ht
    subst t
    have ho : d.state.user.overflow = false := by simpa [ne_of_lt hm] using hd.2.2
    simpa [onScan, Macro.branch, ho] using
      And.intro (descendLeft_guard w m k a b ⟨mid, hm⟩ stack hs d hd.2.1)
        (descendLeft_fits w m k a b ⟨mid, hm⟩ stack d hd.2.1)
  · simp only [step, dif_neg hm, Option.some.injEq] at ht
    subst t
    have he : mid = 2 ^ m := by have := hs.2.1; omega
    have ho : d.state.user.overflow = true := by simpa [he] using hd.2.2
    simpa [onScan, Macro.branch, ho, stateStack] using
      And.intro (return_guard w (budget m) d (fun _ => false))
        (returnValue_fits w m (.scan k a b mid stack) d hd.2.1 (fun _ => false))

end

end Lax434930Proofs.SavitchProofs.SearchProgram
