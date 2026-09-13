import Lax434930Proofs.SavitchDefinitions.Reachability
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
An explicit stack evaluator for bounded reachability. Adjacency is supplied
as a Boolean function. These operational lemmas do not implement that query
or the stack operations on the work tape of `SpaceMachines.Machine`.
-/

namespace Lax434930Proofs.SavitchProofs.StackSearch

open Lax434930Proofs.SavitchDefinitions.Reachability

variable {N : ℕ}

inductive Frame (N : ℕ) where
  | left (depth : ℕ) (a b middle : Fin N)
  | right (depth : ℕ) (a b middle : Fin N)

inductive State (N : ℕ) where
  | call (depth : ℕ) (a b : Fin N) (stack : List (Frame N))
  | scan (depth : ℕ) (a b : Fin N) (next : ℕ) (stack : List (Frame N))
  | ret (result : Bool) (stack : List (Frame N))

def step (G : Graph N) : State N → Option (State N)
  | .call 0 a b stack => some (.ret (decide (a = b) || G a b) stack)
  | .call (k + 1) a b stack => some (.scan k a b 0 stack)
  | .scan k a b m stack =>
      if h : m < N then
        some (.call k a ⟨m, h⟩ (.left k a b ⟨m, h⟩ :: stack))
      else some (.ret false stack)
  | .ret _ [] => none
  | .ret false (.left k a b m :: stack) => some (.scan k a b (m + 1) stack)
  | .ret true (.left k a b m :: stack) =>
      some (.call k m b (.right k a b m :: stack))
  | .ret false (.right k a b m :: stack) => some (.scan k a b (m + 1) stack)
  | .ret true (.right _ _ _ _ :: stack) => some (.ret true stack)

def callCost (N : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 + N * (2 * callCost N k + 3)

def scanCost (N k m : ℕ) : ℕ := 1 + (N - m) * (2 * callCost N k + 3)

def Frame.cost : Frame N → ℕ
  | .left k _ _ m => callCost N k + 2 + scanCost N k (m + 1)
  | .right k _ _ m => 1 + scanCost N k (m + 1)

def stackCost (stack : List (Frame N)) : ℕ := (stack.map Frame.cost).sum

def State.cost : State N → ℕ
  | .call k _ _ stack => callCost N k + stackCost stack
  | .scan k _ _ m stack => scanCost N k m + stackCost stack
  | .ret _ stack => stackCost stack

@[simp] lemma stackCost_nil : stackCost ([] : List (Frame N)) = 0 := rfl

@[simp] lemma stackCost_cons (f : Frame N) (stack : List (Frame N)) :
    stackCost (f :: stack) = f.cost + stackCost stack := rfl

lemma cost_decreases (G : Graph N) {s t : State N} (h : step G s = some t) :
    t.cost < s.cost := by
  cases s with
  | call k a b stack =>
    cases k <;> simp only [step, Option.some.injEq] at h <;> subst t
    · simp [State.cost, callCost]
    · simp [State.cost, callCost, scanCost]
  | scan k a b m stack =>
    by_cases hm : m < N
    · simp only [step, dif_pos hm, Option.some.injEq] at h
      subst t
      have hn : N - m = (N - (m + 1)) + 1 := by omega
      simp only [State.cost, stackCost_cons, Frame.cost, scanCost]
      rw [hn, Nat.add_mul]
      omega
    · simp only [step, dif_neg hm, Option.some.injEq] at h
      subst t
      simp [State.cost, scanCost]
  | ret r stack =>
    cases stack with
    | nil => simp [step] at h
    | cons f stack =>
      cases f <;> cases r <;>
        simp only [step, Option.some.injEq] at h
      all_goals subst t; simp [State.cost, Frame.cost, scanCost] <;> omega

def tailValue (G : Graph N) (k : ℕ) (a b : Fin N) (m : ℕ) : Bool :=
  ((List.finRange N).drop m).any fun v => search G k a v && search G k v b

lemma tailValue_zero (G : Graph N) (k : ℕ) (a b : Fin N) :
    tailValue G k a b 0 = search G (k + 1) a b := by
  simp [tailValue, search]

lemma tailValue_end (G : Graph N) (k : ℕ) (a b : Fin N) (m : ℕ) (hm : N ≤ m) :
    tailValue G k a b m = false := by
  have hd : (List.finRange N).drop m = [] :=
    List.drop_eq_nil_of_le (by simpa using hm)
  simp only [tailValue, hd, List.any_nil]

lemma tailValue_next (G : Graph N) (k : ℕ) (a b : Fin N) (m : ℕ) (hm : m < N) :
    tailValue G k a b m =
      ((search G k a ⟨m, hm⟩ && search G k ⟨m, hm⟩ b) || tailValue G k a b (m + 1)) := by
  unfold tailValue
  rw [List.drop_eq_getElem_cons (l := List.finRange N) (i := m) (by simpa using hm)]
  simp only [List.any_cons, List.getElem_finRange, Fin.cast_mk]

def Frame.apply (G : Graph N) : Frame N → Bool → Bool
  | .left k a b m, r => (r && search G k m b) || tailValue G k a b (m + 1)
  | .right k a b m, r => r || tailValue G k a b (m + 1)

def unwind (G : Graph N) (stack : List (Frame N)) (r : Bool) : Bool :=
  stack.foldl (fun value frame => frame.apply G value) r

@[simp] lemma unwind_cons (G : Graph N) (f : Frame N) (stack : List (Frame N)) (r : Bool) :
    unwind G (f :: stack) r = unwind G stack (f.apply G r) := rfl

def State.value (G : Graph N) : State N → Bool
  | .call k a b stack => unwind G stack (search G k a b)
  | .scan k a b m stack => unwind G stack (tailValue G k a b m)
  | .ret r stack => unwind G stack r

lemma value_preserved (G : Graph N) {s t : State N} (h : step G s = some t) :
    t.value G = s.value G := by
  cases s with
  | call k a b stack =>
    cases k <;> simp only [step, Option.some.injEq] at h <;> subst t
    · rfl
    · simp [State.value, tailValue_zero]
  | scan k a b m stack =>
    by_cases hm : m < N
    · simp only [step, dif_pos hm, Option.some.injEq] at h
      subst t
      simp [State.value, Frame.apply, tailValue_next G k a b m hm]
    · simp only [step, dif_neg hm, Option.some.injEq] at h
      subst t
      simp [State.value, tailValue_end G k a b m (by omega)]
  | ret r stack =>
    cases stack with
    | nil => simp [step] at h
    | cons f stack =>
      cases f <;> cases r <;>
        simp only [step, Option.some.injEq] at h <;> subst t <;>
        simp [State.value, Frame.apply]

lemma step_eq_none (G : Graph N) (s : State N) :
    step G s = none ↔ ∃ r, s = .ret r [] := by
  cases s with
  | call k a b stack => cases k <;> simp [step]
  | scan k a b m stack => by_cases h : m < N <;> simp [step, h]
  | ret r stack =>
    cases stack with
    | nil => simp [step]
    | cons f stack => cases f <;> cases r <;> simp [step]

def evaluate (G : Graph N) (s : State N) : Bool :=
  match _h : step G s with
  | none => match s with
      | .ret r _ => r
      | _ => false
  | some t => evaluate G t
termination_by s.cost
decreasing_by exact cost_decreases G _h

lemma evaluate_correct (G : Graph N) (s : State N) : evaluate G s = s.value G := by
  induction s using (measure State.cost).wf.induction with
  | h s ih =>
    rw [evaluate]
    split
    · rename_i ht
      obtain ⟨r, rfl⟩ := (step_eq_none G s).mp ht
      rfl
    · rename_i t ht
      rw [ih t (cost_decreases G ht)]
      exact value_preserved G ht

lemma evaluate_call (G : Graph N) (k : ℕ) (a b : Fin N) :
    evaluate G (.call k a b []) = search G k a b := by
  rw [evaluate_correct]
  rfl

def Frame.depth : Frame N → ℕ
  | .left k _ _ _ => k
  | .right k _ _ _ => k

def StackValid (bound : ℕ) : List (Frame N) → Prop
  | [] => True
  | f :: stack => f.depth + 1 + stack.length ≤ bound ∧ StackValid bound stack

def State.Valid (bound : ℕ) : State N → Prop
  | .call k _ _ stack => k + stack.length ≤ bound ∧ StackValid bound stack
  | .scan k _ _ m stack => k + 1 + stack.length ≤ bound ∧ m ≤ N ∧ StackValid bound stack
  | .ret _ stack => stack.length ≤ bound ∧ StackValid bound stack

lemma valid_preserved (G : Graph N) {s t : State N} {bound : ℕ}
    (hs : s.Valid bound) (ht : step G s = some t) : t.Valid bound := by
  cases s with
  | call k a b stack =>
    cases k <;> simp only [step, Option.some.injEq] at ht <;> subst t
    · simpa [State.Valid] using hs
    · simpa [State.Valid] using hs
  | scan k a b m stack =>
    rcases hs with ⟨hk, _, hstack⟩
    by_cases hm : m < N
    · simp only [step, dif_pos hm, Option.some.injEq] at ht
      subst t
      exact ⟨by simpa [Nat.add_assoc, Nat.add_comm] using hk, hk, hstack⟩
    · simp only [step, dif_neg hm, Option.some.injEq] at ht
      subst t
      exact ⟨by omega, hstack⟩
  | ret r stack =>
    cases stack with
    | nil => simp [step] at ht
    | cons f stack =>
      rcases hs with ⟨hlen, hf, hstack⟩
      cases f <;> cases r <;>
        simp only [step, Option.some.injEq] at ht <;> subst t
      · rename_i k a b m
        exact ⟨hf, by have := m.isLt; omega, hstack⟩
      · exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Frame.depth] using hf, hf, hstack⟩
      · rename_i k a b m
        exact ⟨hf, by have := m.isLt; omega, hstack⟩
      · exact ⟨by simp only [List.length_cons] at hlen; omega, hstack⟩

def Reaches (G : Graph N) : State N → State N → Prop :=
  Relation.ReflTransGen (fun s t => step G s = some t)

lemma reaches_valid (G : Graph N) {s t : State N} {bound : ℕ}
    (h : Reaches G s t) (hs : s.Valid bound) : t.Valid bound := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact valid_preserved G ih hstep

lemma reaches_value (G : Graph N) {s t : State N} (h : Reaches G s t) :
    t.value G = s.value G := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (value_preserved G hstep).trans ih

lemma reaches_terminal (G : Graph N) (s : State N) :
    ∃ r, Reaches G s (.ret r []) := by
  induction s using (measure State.cost).wf.induction with
  | h s ih =>
    cases ht : step G s with
    | none =>
      obtain ⟨r, rfl⟩ := (step_eq_none G s).mp ht
      exact ⟨r, .refl⟩
    | some t =>
      obtain ⟨r, hr⟩ := ih t (cost_decreases G ht)
      have hst : Reaches G s t := .single ht
      exact ⟨r, hst.trans hr⟩

lemma call_execution (G : Graph N) (k : ℕ) (a b : Fin N) :
    Reaches G (.call k a b []) (.ret (search G k a b) []) := by
  obtain ⟨r, hr⟩ := reaches_terminal G (.call k a b [])
  have hvalue : r = search G k a b := reaches_value G hr
  simpa [hvalue] using hr

lemma call_valid (G : Graph N) (k : ℕ) (a b : Fin N) {s : State N}
    (hs : Reaches G (.call k a b []) s) : s.Valid k := by
  apply reaches_valid G hs
  simp [State.Valid, StackValid]

inductive Symbol where
  | tally | separator | bit (value : Bool)
  | callTag | scanTag | retTag | leftTag | rightTag
  deriving DecidableEq, Fintype

def bits (width value : ℕ) : List Symbol :=
  List.ofFn fun i : Fin width => .bit (value.testBit i)

@[simp] lemma bits_length (width value : ℕ) : (bits width value).length = width := by
  simp [bits]

lemma bits_injective (width x y : ℕ) (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (h : bits width x = bits width y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · have he := congrArg (fun l : List Symbol => l[i]?) h
    simpa [bits, hi] using he
  · have hp : 2 ^ width ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (hx.trans_le hp), Nat.testBit_lt_two_pow (hy.trans_le hp)]

def fields (width depth a b middle : ℕ) : List Symbol :=
  List.replicate depth .tally ++ .separator ::
    (bits width a ++ bits width b ++ bits width middle)

def Frame.encode (width : ℕ) : Frame N → List Symbol
  | .left k a b m => .leftTag :: fields width k a b m
  | .right k a b m => .rightTag :: fields width k a b m

def encodeStack (width : ℕ) (stack : List (Frame N)) : List Symbol :=
  stack.flatMap (Frame.encode width)

def State.encode (width : ℕ) : State N → List Symbol
  | .call k a b stack => .callTag ::
      (fields width k a b 0 ++ encodeStack width stack)
  | .scan k a b m stack => .scanTag ::
      (fields width k a b m ++ encodeStack width stack)
  | .ret r stack => .retTag :: .bit r :: encodeStack width stack

lemma frame_length (width : ℕ) (f : Frame N) :
    (f.encode width).length = 2 + f.depth + 3 * width := by
  cases f <;> simp [Frame.encode, Frame.depth, fields] <;> omega

lemma stack_length (width bound : ℕ) (stack : List (Frame N))
    (h : StackValid bound stack) :
    (encodeStack width stack).length ≤ stack.length * (2 + bound + 3 * width) := by
  induction stack with
  | nil => simp [encodeStack]
  | cons f stack ih =>
    rcases h with ⟨hf, hstack⟩
    have htail := ih hstack
    have hhead : f.depth ≤ bound := by omega
    simp only [encodeStack, List.flatMap_cons, List.length_append, frame_length,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    change 2 + f.depth + 3 * width + (encodeStack width stack).length ≤ _
    omega

lemma state_length (width bound : ℕ) (s : State N) (h : s.Valid bound) :
    (s.encode width).length ≤ (bound + 1) * (2 + bound + 3 * width) := by
  cases s with
  | call k a b stack =>
    rcases h with ⟨hk, hstack⟩
    have hl : stack.length ≤ bound := by omega
    have hlen := (stack_length width bound stack hstack).trans
      (Nat.mul_le_mul_right (2 + bound + 3 * width) hl)
    simp only [State.encode, fields, List.length_cons, List.length_append,
      List.length_replicate, bits_length, Nat.add_mul, Nat.one_mul]
    omega
  | scan k a b m stack =>
    rcases h with ⟨hk, _, hstack⟩
    have hl : stack.length ≤ bound := by omega
    have hlen := (stack_length width bound stack hstack).trans
      (Nat.mul_le_mul_right (2 + bound + 3 * width) hl)
    simp only [State.encode, fields, List.length_cons, List.length_append,
      List.length_replicate, bits_length, Nat.add_mul, Nat.one_mul]
    omega
  | ret r stack =>
    rcases h with ⟨hl, hstack⟩
    have hlen := (stack_length width bound stack hstack).trans
      (Nat.mul_le_mul_right (2 + bound + 3 * width) hl)
    simp only [State.encode, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

lemma execution_storage (G : Graph N) (k width : ℕ) (a b : Fin N) {s : State N}
    (hs : Reaches G (.call k a b []) s) :
    (s.encode width).length ≤ (k + 1) * (2 + k + 3 * width) :=
  state_length width k s (call_valid G k a b hs)

end Lax434930Proofs.SavitchProofs.StackSearch
