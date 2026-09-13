import Lax434930Proofs.SavitchProofs.MachinePaths

set_option backward.isDefEq.respectTransparency false

/-!
Finite stack programs with a separate read-only input head, and their
translation to the work-tape model used here. Stack symbols occupy
parallel tracks. A push or pop scans a track from its bottom to its top,
then returns the work head to the left end.
-/

namespace Lax434930Proofs.SavitchProofs.StackMachine

noncomputable section

open scoped Classical

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open MachinePaths

inductive Instruction (K Γ Q : Type) where
  | move (direction : Move) (next : Q)
  | push (stack : K) (symbol : Γ) (next : Q)
  | pop (stack : K) (next : Option Γ → Q)
  | halt

structure Program (K Γ Q : Type) where
  start : Q
  code : Q → InputSymbol → Instruction K Γ Q
  accept : Q → Bool

structure Config (K Γ Q : Type) where
  state : Q
  inputHead : ℕ
  store : K → List Γ

variable {K Γ Q : Type}

def Program.initial (P : Program K Γ Q) : Config K Γ Q := ⟨P.start, 0, fun _ => []⟩

noncomputable def Program.step (P : Program K Γ Q) (w : Word)
    (c : Config K Γ Q) : Option (Config K Γ Q) := by
  classical
  exact match P.code c.state (readInput w c.inputHead) with
  | .move direction q => some ⟨q, min (direction.apply c.inputHead) (w.length + 1), c.store⟩
  | .push k g q => some ⟨q, c.inputHead, Function.update c.store k (g :: c.store k)⟩
  | .pop k q => some ⟨q (c.store k).head?, c.inputHead,
      Function.update c.store k (c.store k).tail⟩
  | .halt => none

inductive Control (K Γ Q : Type) where
  | init
  | dispatch (state : Q)
  | push (stack : K) (symbol : Γ) (next : Q)
  | pop (stack : K) (next : Option Γ → Q)
  | take (stack : K) (next : Option Γ → Q)
  | back (next : Q)
  deriving Fintype

abbrev Alphabet (K Γ : Type) := Bool × (K → Option Γ)

noncomputable def action (P : Program K Γ Q) (q : Control K Γ Q)
    (input : InputSymbol) (b : Alphabet K Γ) : Option (Action (Alphabet K Γ) (Control K Γ Q)) := by
  classical
  exact match q with
  | .init => some ⟨.dispatch P.start, (true, b.2), .stay, .stay⟩
  | .dispatch state => match P.code state input with
      | .move direction next => some ⟨.dispatch next, b, direction, .stay⟩
      | .push k g next => some ⟨.push k g next, b, .stay, .stay⟩
      | .pop k next => some ⟨.pop k next, b, .stay, .stay⟩
      | .halt => none
  | .push k g next => match b.2 k with
      | some _ => some ⟨.push k g next, b, .stay, .right⟩
      | none => some ⟨.back next, (b.1, Function.update b.2 k (some g)), .stay, .left⟩
  | .pop k next => match b.2 k with
      | some _ => some ⟨.pop k next, b, .stay, .right⟩
      | none => if b.1 then some ⟨.dispatch (next none), b, .stay, .stay⟩
          else some ⟨.take k next, b, .stay, .left⟩
  | .take k next => some ⟨.back (next (b.2 k)), (b.1, Function.update b.2 k none), .stay, .left⟩
  | .back next => if b.1 then some ⟨.dispatch next, b, .stay, .stay⟩
      else some ⟨.back next, b, .stay, .left⟩

noncomputable def compile [Fintype K] [Fintype Γ] [Fintype Q]
    (P : Program K Γ Q) : Machine where
  Γ := Alphabet K Γ
  Q := Control K Γ Q
  blank := (false, fun _ => none)
  start := .init
  transition q i b := match action P q i b with
    | none => ∅
    | some a => {a}
  accept q := match q with
    | .dispatch state => P.accept state
    | _ => false

section Compilation

variable [Fintype K] [Fintype Γ] [Fintype Q] (P : Program K Γ Q)

lemma deterministic : (compile P).Deterministic := by
  intro q i b a ha a' ha'
  cases h : action P q i b with
  | none => exact (Finset.notMem_empty a (by simpa only [compile, h] using ha)).elim
  | some x =>
    have hx : a = x := Finset.mem_singleton.mp (by simpa only [compile, h] using ha)
    have hx' : a' = x := Finset.mem_singleton.mp (by simpa only [compile, h] using ha')
    exact hx.trans hx'.symm

lemma step_of_action (w : Word) (c : (compile P).Config)
    (a : Action (Alphabet K Γ) (Control K Γ Q))
    (h : action P c.state (readInput w c.inputHead) (c.tape c.workHead) = some a) :
    (compile P).Step w c ((compile P).execute w c a) := by
  exact ⟨a, by simp only [compile, h]; exact Finset.mem_singleton_self a, rfl⟩

def tape (store : K → List Γ) (i : ℕ) : Alphabet K Γ :=
  (decide (i = 0), fun k => (store k).reverse[i]?)

def located (q : Control K Γ Q) (inputHead workHead : ℕ) (store : K → List Γ) :
    (compile P).Config := ⟨q, inputHead, workHead, tape store⟩

def encode (c : Config K Γ Q) : (compile P).Config :=
  located P (.dispatch c.state) c.inputHead 0 c.store

lemma execute_unchanged (w : Word) (c : (compile P).Config)
    (q : Control K Γ Q) (inputMove workMove : Move) :
    (compile P).execute w c ⟨q, c.tape c.workHead, inputMove, workMove⟩ =
      ⟨q, min (inputMove.apply c.inputHead) (w.length + 1), workMove.apply c.workHead, c.tape⟩ := by
  simp [Machine.execute]

lemma init_step (w : Word) :
    (compile P).Step w (compile P).initial (encode P P.initial) := by
  have h := step_of_action P w (compile P).initial
    ⟨.dispatch P.start, (true, fun _ => none), .stay, .stay⟩ (by rfl)
  convert h using 1
  simp only [encode, Program.initial, located, Machine.execute, Machine.initial, compile,
    Move.apply, Nat.min_eq_left (by omega : 0 ≤ w.length + 1)]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [tape, Function.update_apply, hi]

lemma return_trace (w : Word) (q : Q) (inputHead pos bound : ℕ) (store : K → List Γ)
    (hi : inputHead ≤ w.length + 1) (hb : pos < bound) :
    Trace (compile P) w bound (located P (.back q) inputHead pos store)
      (located P (.dispatch q) inputHead 0 store) := by
  induction pos with
  | zero =>
    have h := step_of_action P w (located P (.back q) inputHead 0 store)
      ⟨.dispatch q, tape store 0, .stay, .stay⟩ (by simp [located, tape, action])
    have he : (compile P).Step w (located P (.back q) inputHead 0 store)
        (located P (.dispatch q) inputHead 0 store) := by
      simpa [execute_unchanged, located, Machine.execute, Move.apply, Nat.min_eq_left hi] using h
    exact Trace.single he hb hb
  | succ pos ih =>
    have h := step_of_action P w (located P (.back q) inputHead (pos + 1) store)
      ⟨.back q, tape store (pos + 1), .stay, .left⟩ (by simp [located, tape, action])
    have he : (compile P).Step w (located P (.back q) inputHead (pos + 1) store)
        (located P (.back q) inputHead pos store) := by
      simpa [execute_unchanged, located, Machine.execute, Move.apply, Nat.min_eq_left hi] using h
    exact (Trace.single he hb (by simpa [located] using Nat.lt_of_succ_lt hb)).trans
      (ih (by omega))

omit [Fintype K] [Fintype Γ] [Fintype Q] in
lemma getElem_reverse_push (xs : List Γ) (g : Γ) (i : ℕ) :
    (g :: xs).reverse[i]? = if i = xs.length then some g else xs.reverse[i]? := by
  by_cases he : i = xs.length
  · subst i
    simp [List.reverse_cons]
  · by_cases hi : i < xs.length
    · simp [List.reverse_cons, List.getElem?_append, hi, he]
    · have hs : ([g] : List Γ).length ≤ i - xs.length := by simp; omega
      simp [List.reverse_cons, List.getElem?_append, hi, he,
        List.getElem?_eq_none hs]

omit [Fintype K] [Fintype Γ] [Fintype Q] in
lemma tape_push (store : K → List Γ) (k : K) (g : Γ) :
    Function.update (tape store) (store k).length
      ((tape store (store k).length).1,
        Function.update (tape store (store k).length).2 k (some g)) =
      tape (Function.update store k (g :: store k)) := by
  funext i
  apply Prod.ext
  · by_cases hi : i = (store k).length <;> simp [Function.update_apply, tape, hi]
  · funext j
    by_cases hi : i = (store k).length <;> by_cases hj : j = k <;>
      simp [-List.reverse_cons, Function.update_apply, tape, hi, hj, getElem_reverse_push]

omit [Fintype K] [Fintype Γ] [Fintype Q] in
lemma tape_pop (store : K → List Γ) (k : K) (g : Γ) (xs : List Γ)
    (hk : store k = g :: xs) :
    Function.update (tape store) xs.length
      ((tape store xs.length).1, Function.update (tape store xs.length).2 k none) =
      tape (Function.update store k xs) := by
  funext i
  apply Prod.ext
  · by_cases hi : i = xs.length <;> simp [Function.update_apply, tape, hi]
  · funext j
    by_cases hi : i = xs.length <;> by_cases hj : j = k <;>
      simp [-List.reverse_cons, Function.update_apply, tape, hi, hj, hk, getElem_reverse_push]

lemma scan_trace (w : Word) (q : Control K Γ Q) (inputHead start stop bound : ℕ)
    (store : K → List Γ) (hi : inputHead ≤ w.length + 1) (hs : start ≤ stop)
    (hb : stop < bound)
    (ha : ∀ i < stop, action P q (readInput w inputHead) (tape store i) =
      some ⟨q, tape store i, .stay, .right⟩) :
    Trace (compile P) w bound (located P q inputHead start store)
      (located P q inputHead stop store) := by
  induction stop generalizing start with
  | zero =>
    have : start = 0 := by omega
    subst start
    exact Trace.refl hb
  | succ stop ih =>
    by_cases he : start = stop + 1
    · subst start
      exact Trace.refl hb
    · have ht := ih start (by omega) (by omega) (fun i hi => ha i (by omega))
      have h := step_of_action P w (located P q inputHead stop store)
        ⟨q, tape store stop, .stay, .right⟩ (ha stop (by omega))
      have hstep : (compile P).Step w (located P q inputHead stop store)
          (located P q inputHead (stop + 1) store) := by
        simpa [located, Machine.execute, Move.apply, Nat.min_eq_left hi] using h
      exact ht.trans (Trace.single hstep (by simpa [located] using Nat.lt_of_succ_lt hb) hb)

lemma push_trace (w : Word) (q next : Q) (inputHead bound : ℕ) (store : K → List Γ)
    (k : K) (g : Γ) (hi : inputHead ≤ w.length + 1) (hb : (store k).length < bound)
    (hc : P.code q (readInput w inputHead) = .push k g next) :
    Trace (compile P) w bound (located P (.dispatch q) inputHead 0 store)
      (located P (.dispatch next) inputHead 0 (Function.update store k (g :: store k))) := by
  have hstart := step_of_action P w (located P (.dispatch q) inputHead 0 store)
    ⟨.push k g next, tape store 0, .stay, .stay⟩ (by simp [located, action, hc])
  have hs : (compile P).Step w (located P (.dispatch q) inputHead 0 store)
      (located P (.push k g next) inputHead 0 store) := by
    simpa [located, Machine.execute, Move.apply, Nat.min_eq_left hi] using hstart
  have hscan := scan_trace P w (.push k g next) inputHead 0 (store k).length bound store
    hi (Nat.zero_le _) hb (by
      intro i hi
      have hil : i < (store k).reverse.length := by simpa using hi
      simp [action, tape, List.getElem?_eq_getElem hil])
  have hwrite := step_of_action P w (located P (.push k g next) inputHead (store k).length store)
    ⟨.back next, ((tape store (store k).length).1,
      Function.update (tape store (store k).length).2 k (some g)), .stay, .left⟩
    (by simp [located, action, tape])
  have hw : (compile P).Step w (located P (.push k g next) inputHead (store k).length store)
      (located P (.back next) inputHead ((store k).length - 1)
        (Function.update store k (g :: store k))) := by
    convert hwrite using 1
    simp only [located, Machine.execute, Move.apply, Nat.min_eq_left hi]
    congr 1
    exact (tape_push store k g).symm
  exact (Trace.single hs (by simp [located]; omega) (by simp [located]; omega)).trans
    (hscan.trans ((Trace.single hw hb (by simp [located]; omega)).trans
      (return_trace P w next inputHead ((store k).length - 1) bound
        (Function.update store k (g :: store k)) hi (by omega))))

lemma pop_trace (w : Word) (q : Q) (next : Option Γ → Q) (inputHead bound : ℕ)
    (store : K → List Γ) (k : K) (hi : inputHead ≤ w.length + 1)
    (hb : (store k).length < bound)
    (hc : P.code q (readInput w inputHead) = .pop k next) :
    Trace (compile P) w bound (located P (.dispatch q) inputHead 0 store)
      (located P (.dispatch (next (store k).head?)) inputHead 0
        (Function.update store k (store k).tail)) := by
  have hstart := step_of_action P w (located P (.dispatch q) inputHead 0 store)
    ⟨.pop k next, tape store 0, .stay, .stay⟩ (by simp [located, action, hc])
  have hs : (compile P).Step w (located P (.dispatch q) inputHead 0 store)
      (located P (.pop k next) inputHead 0 store) := by
    simpa [located, Machine.execute, Move.apply, Nat.min_eq_left hi] using hstart
  have hzero : 0 < bound := by omega
  cases hk : store k with
  | nil =>
    have hpop := step_of_action P w (located P (.pop k next) inputHead 0 store)
      ⟨.dispatch (next none), tape store 0, .stay, .stay⟩
      (by simp [located, action, tape, hk])
    have hp : (compile P).Step w (located P (.pop k next) inputHead 0 store)
        (located P (.dispatch (next none)) inputHead 0 store) := by
      simpa [located, Machine.execute, Move.apply, Nat.min_eq_left hi] using hpop
    have hu : Function.update store k [] = store := by
      rw [← hk, Function.update_eq_self]
    simpa [hk, hu] using (Trace.single hs hzero hzero).trans (Trace.single hp hzero hzero)
  | cons g xs =>
    have hscan := scan_trace P w (.pop k next) inputHead 0 (store k).length bound store
      hi (Nat.zero_le _) hb (by
        intro i hi
        have hil : i < (store k).reverse.length := by simpa using hi
        simp [action, tape, List.getElem?_eq_getElem hil])
    have hpop := step_of_action P w (located P (.pop k next) inputHead (store k).length store)
      ⟨.take k next, tape store (store k).length, .stay, .left⟩
      (by simp [located, action, tape, hk])
    have hp : (compile P).Step w (located P (.pop k next) inputHead (store k).length store)
        (located P (.take k next) inputHead xs.length store) := by
      simpa [located, Machine.execute, Move.apply, Nat.min_eq_left hi, hk] using hpop
    have htake := step_of_action P w (located P (.take k next) inputHead xs.length store)
      ⟨.back (next (some g)), ((tape store xs.length).1,
        Function.update (tape store xs.length).2 k none), .stay, .left⟩
      (by simp [located, action, tape, hk])
    have ht : (compile P).Step w (located P (.take k next) inputHead xs.length store)
        (located P (.back (next (some g))) inputHead (xs.length - 1)
          (Function.update store k xs)) := by
      convert htake using 1
      simp only [located, Machine.execute, Move.apply, Nat.min_eq_left hi]
      congr 1
      exact (tape_pop store k g xs hk).symm
    have hlen : xs.length < bound := by simp only [hk, List.length_cons] at hb; omega
    have hresult := (Trace.single hs hzero hzero).trans
      (hscan.trans ((Trace.single hp hb hlen).trans
        ((Trace.single ht hlen (by simp [located]; omega)).trans
          (return_trace P w (next (some g)) inputHead (xs.length - 1) bound
            (Function.update store k xs) hi (by omega)))))
    simpa [hk] using hresult

lemma move_trace (w : Word) (q next : Q) (direction : Move) (inputHead bound : ℕ)
    (store : K → List Γ) (hb : 0 < bound)
    (hc : P.code q (readInput w inputHead) = .move direction next) :
    Trace (compile P) w bound (located P (.dispatch q) inputHead 0 store)
      (located P (.dispatch next) (min (direction.apply inputHead) (w.length + 1)) 0 store) := by
  have h := step_of_action P w (located P (.dispatch q) inputHead 0 store)
    ⟨.dispatch next, tape store 0, direction, .stay⟩ (by simp [located, action, hc])
  have hs : (compile P).Step w (located P (.dispatch q) inputHead 0 store)
      (located P (.dispatch next) (min (direction.apply inputHead) (w.length + 1)) 0 store) := by
    simpa [located, Machine.execute, Move.apply] using h
  exact Trace.single hs hb hb

lemma halt_terminal (w : Word) (q : Q) (inputHead : ℕ) (store : K → List Γ)
    (hc : P.code q (readInput w inputHead) = .halt) :
    (compile P).Terminal w (located P (.dispatch q) inputHead 0 store) := by
  rintro d ⟨a, ha, _⟩
  have he : a ∈ (∅ : Finset (Action (compile P).Γ (compile P).Q)) := by
    simpa only [compile, located, action, hc] using ha
  exact Finset.notMem_empty a he

def Good (w : Word) (bound : ℕ) (c : Config K Γ Q) : Prop :=
  c.inputHead ≤ w.length + 1 ∧ ∀ k, (c.store k).length < bound

lemma step_trace (w : Word) (bound : ℕ) {c d : Config K Γ Q}
    (hb : 0 < bound) (hg : Good w bound c) (hs : P.step w c = some d) :
    Trace (compile P) w bound (encode P c) (encode P d) := by
  cases c with
  | mk q inputHead store =>
    rcases hg with ⟨hi, hstore⟩
    cases hc : P.code q (readInput w inputHead) with
    | halt => simp [Program.step, hc] at hs
    | move direction next =>
      simp only [Program.step, hc, Option.some.injEq] at hs
      subst d
      exact move_trace P w q next direction inputHead bound store hb hc
    | push k g next =>
      simp only [Program.step, hc, Option.some.injEq] at hs
      subst d
      exact push_trace P w q next inputHead bound store k g hi (hstore k) hc
    | pop k next =>
      simp only [Program.step, hc, Option.some.injEq] at hs
      subst d
      exact pop_trace P w q next inputHead bound store k hi (hstore k) hc

lemma halted_terminal (w : Word) (c : Config K Γ Q) (hc : P.step w c = none) :
    (compile P).Terminal w (encode P c) := by
  cases he : P.code c.state (readInput w c.inputHead) with
  | halt => exact halt_terminal P w c.state c.inputHead c.store he
  | move d q => simp [Program.step, he] at hc
  | push k g q => simp [Program.step, he] at hc
  | pop k q => simp [Program.step, he] at hc

def SafeStep (w : Word) (bound : ℕ) (c d : Config K Γ Q) : Prop :=
  P.step w c = some d ∧ Good w bound c ∧ Good w bound d

lemma path_trace (w : Word) (bound : ℕ) {n : ℕ} {c d : Config K Γ Q}
    (hb : 0 < bound) (h : Path (SafeStep P w bound) n c d) :
    Trace (compile P) w bound (encode P c) (encode P d) := by
  induction h with
  | nil => exact Trace.refl hb
  | cons he _ ih => exact (step_trace P w bound hb he.2.1 he.1).trans ih

lemma compile_correct (w : Word) (bound : ℕ) (c : Config K Γ Q) (hb : 0 < bound)
    (h : ∃ n, Path (SafeStep P w bound) n P.initial c) (hc : P.step w c = none) :
    (compile P).HaltsOn w ∧ (compile P).UsesSpace w bound ∧
      ((compile P).Accepts w ↔ P.accept c.state = true) := by
  obtain ⟨n, hn⟩ := h
  have ht := (Trace.single (init_step P w) hb hb).trans (path_trace P w bound hb hn)
  exact trace_decider (deterministic P) ht (halted_terminal P w c hc)

end Compilation

end

end Lax434930Proofs.SavitchProofs.StackMachine
