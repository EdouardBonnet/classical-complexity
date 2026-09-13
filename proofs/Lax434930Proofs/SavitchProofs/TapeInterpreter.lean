import Lax434930Proofs.SavitchProofs.StackMachine
import Lax434930Proofs.SavitchProofs.TapeZipper

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.TapeInterpreter

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open MachinePaths StackMachine
open scoped Classical

noncomputable section

def choose (M : Machine) (q : M.Q) (i : InputSymbol) (g : M.Γ) : Option (Action M.Γ M.Q) :=
  (M.transition q i g).toList.head?

lemma choose_mem (M : Machine) (q : M.Q) (i : InputSymbol) (g : M.Γ)
    (a : Action M.Γ M.Q) (h : choose M q i g = some a) : a ∈ M.transition q i g := by
  obtain ⟨xs, hx⟩ := List.head?_eq_some_iff.mp h
  apply Finset.mem_toList.mp
  rw [hx]
  exact List.mem_cons_self

lemma choose_action (M : Machine) (hd : M.Deterministic) (q : M.Q) (i : InputSymbol)
    (g : M.Γ) (a : Action M.Γ M.Q) (ha : a ∈ M.transition q i g) :
    choose M q i g = some a := by
  cases h : choose M q i g with
  | none =>
    have he : M.transition q i g = ∅ := by simpa [choose] using h
    exact (Finset.notMem_empty a (he ▸ ha)).elim
  | some b =>
    have hb := choose_mem M q i g b h
    obtain rfl := hd q i g a ha b hb
    rfl

inductive Control (M : Machine) where
  | run (q : M.Q) (current : M.Γ)
  | work (q : M.Q) (written : M.Γ) (direction : Move)
  | getRight (q : M.Q)
  | putRight (q : M.Q) (written current : M.Γ)
  deriving Fintype

variable {K Γ : Type} (M : Machine) (leftKey rightKey : K)
    (enc : M.Γ → Γ) (dec : Option Γ → M.Γ)

def program : Program K Γ (Control M) where
  start := .run M.start M.blank
  code q input := match q with
    | .run q current => match choose M q input current with
        | none => .halt
        | some a => .move a.inputMove (.work a.state a.write a.workMove)
    | .work q written .stay => .move .stay (.run q written)
    | .work q written .right => .push leftKey (enc written) (.getRight q)
    | .work q written .left => .pop leftKey (fun g => match g with
        | none => .run q written
        | some _ => .putRight q written (dec g))
    | .getRight q => .pop rightKey (fun g => .run q (dec g))
    | .putRight q written current => .push rightKey (enc written) (.run q current)
  accept q := match q with
    | .run q _ => M.accept q
    | _ => false

def memory (left right : List M.Γ) : K → List Γ :=
  Function.update (Function.update (fun _ => []) leftKey (left.map enc)) rightKey (right.map enc)

def point (q : Control M) (inputHead : ℕ) (left right : List M.Γ) : Config K Γ (Control M) :=
  ⟨q, inputHead, memory M leftKey rightKey enc left right⟩

def encode (v : TapeZipper.View M) : Config K Γ (Control M) :=
  point M leftKey rightKey enc (.run v.state v.current) v.inputHead v.left v.right

variable (hne : leftKey ≠ rightKey)

include hne in
lemma memory_left (left right : List M.Γ) :
    memory M leftKey rightKey enc left right leftKey = left.map enc := by
  simp [memory, hne]

lemma memory_right (left right : List M.Γ) :
    memory M leftKey rightKey enc left right rightKey = right.map enc := by simp [memory]

include hne in
lemma memory_push_left (left right : List M.Γ) (g : M.Γ) :
    Function.update (memory M leftKey rightKey enc left right) leftKey
      (enc g :: memory M leftKey rightKey enc left right leftKey) =
      memory M leftKey rightKey enc (g :: left) right := by
  funext j
  by_cases hl : j = leftKey <;> by_cases hr : j = rightKey <;> simp_all [memory, Function.update_apply]

lemma memory_push_right (left right : List M.Γ) (g : M.Γ) :
    Function.update (memory M leftKey rightKey enc left right) rightKey
      (enc g :: memory M leftKey rightKey enc left right rightKey) =
      memory M leftKey rightKey enc left (g :: right) := by simp [memory]

include hne in
lemma memory_pop_left (left right : List M.Γ) :
    Function.update (memory M leftKey rightKey enc left right) leftKey
      (left.map enc).tail =
      memory M leftKey rightKey enc left.tail right := by
  funext j
  by_cases hl : j = leftKey <;> by_cases hr : j = rightKey <;> simp_all [memory, Function.update_apply]

lemma memory_pop_right (left right : List M.Γ) :
    Function.update (memory M leftKey rightKey enc left right) rightKey
      (right.map enc).tail =
      memory M leftKey rightKey enc left right.tail := by simp [memory]

lemma point_good (w : Word) (bound : ℕ) (q : Control M) (inputHead : ℕ) (left right : List M.Γ)
    (hi : inputHead ≤ w.length + 1) (hb : 0 < bound)
    (hl : left.length < bound) (hr : right.length < bound) :
    StackMachine.Good w bound (point M leftKey rightKey enc q inputHead left right) := by
  refine ⟨hi, ?_⟩
  intro j
  by_cases hjl : j = leftKey <;> by_cases hjr : j = rightKey <;>
    simp_all [point, memory]

lemma encode_good (w : Word) (s : ℕ) (v : TapeZipper.View M)
    (hi : v.inputHead ≤ w.length + 1) (hv : v.cells ≤ s) :
    StackMachine.Good w (s + 1) (encode M leftKey rightKey enc v) := by
  apply point_good M leftKey rightKey enc w (s + 1) _ _ _ _ hi (by omega)
  · simp only [TapeZipper.View.cells] at hv; omega
  · simp only [TapeZipper.View.cells] at hv; omega

variable (hdec₀ : dec none = M.blank) (hdec : ∀ g, dec (some (enc g)) = g)

include hdec₀ hdec in
lemma decoded_head (xs : List M.Γ) : dec (xs.map enc).head? = xs.headD M.blank := by
  cases xs <;> simp [hdec₀, hdec]

include hne hdec₀ hdec in
lemma action_path (w : Word) (s : ℕ) (v : TapeZipper.View M) (a : Action M.Γ M.Q)
    (hi : v.inputHead ≤ w.length + 1) (hv : v.cells ≤ s)
    (ha : choose M v.state (readInput w v.inputHead) v.current = some a)
    (hv' : (TapeZipper.apply M w v a).cells ≤ s) :
    ∃ n, Path (SafeStep (program M leftKey rightKey enc dec) w (s + 1)) n
      (encode M leftKey rightKey enc v)
      (encode M leftKey rightKey enc (TapeZipper.apply M w v a)) := by
  let P := program M leftKey rightKey enc dec
  let nextInput := min (a.inputMove.apply v.inputHead) (w.length + 1)
  let d₁ := point M leftKey rightKey enc (.work a.state a.write a.workMove) nextInput v.left v.right
  have hi' : nextInput ≤ w.length + 1 := min_le_right _ _
  have hl : v.left.length < s + 1 := by simp only [TapeZipper.View.cells] at hv; omega
  have hr : v.right.length < s + 1 := by simp only [TapeZipper.View.cells] at hv; omega
  have hd₀ := encode_good M leftKey rightKey enc w s v hi hv
  have hd₁ : StackMachine.Good w (s + 1) d₁ :=
    point_good M leftKey rightKey enc w (s + 1) _ _ _ _ hi' (by omega) hl hr
  have hs₀ : SafeStep P w (s + 1) (encode M leftKey rightKey enc v) d₁ := by
    refine ⟨?_, hd₀, hd₁⟩
    simp [P, program, Program.step, encode, point, ha, d₁, nextInput]
  have hfinal := encode_good M leftKey rightKey enc w s (TapeZipper.apply M w v a)
    (by cases hm : a.workMove <;> cases hx : v.left <;> simp [TapeZipper.apply, hm, hx]) hv'
  cases hm : a.workMove with
  | stay =>
    have hs₁ : SafeStep P w (s + 1) d₁
        (encode M leftKey rightKey enc (TapeZipper.apply M w v a)) := by
      refine ⟨?_, hd₁, hfinal⟩
      simp [P, d₁, point, program, Program.step, hm, TapeZipper.apply, encode,
        Move.apply, nextInput]
    exact ⟨2, .cons hs₀ (.cons hs₁ (.nil _))⟩
  | right =>
    let d₂ := point M leftKey rightKey enc (.getRight a.state) nextInput (a.write :: v.left) v.right
    have hd₂ : StackMachine.Good w (s + 1) d₂ := by
      apply point_good M leftKey rightKey enc w (s + 1) _ _ _ _ hi' (by omega) _ hr
      simp only [List.length_cons, TapeZipper.View.cells] at *
      omega
    have hs₁ : SafeStep P w (s + 1) d₁ d₂ := by
      refine ⟨?_, hd₁, hd₂⟩
      simp only [P, program, Program.step, d₁, d₂, point, hm]
      rw [memory_push_left M leftKey rightKey enc hne]
    have hs₂ : SafeStep P w (s + 1) d₂
        (encode M leftKey rightKey enc (TapeZipper.apply M w v a)) := by
      refine ⟨?_, hd₂, hfinal⟩
      simp only [P, program, Program.step, d₂, point, memory_right, encode, TapeZipper.apply, hm]
      rw [decoded_head M enc dec hdec₀ hdec, memory_pop_right]
    exact ⟨3, .cons hs₀ (.cons hs₁ (.cons hs₂ (.nil _)))⟩
  | left =>
    cases hx : v.left with
    | nil =>
      have hs₁ : SafeStep P w (s + 1) d₁
          (encode M leftKey rightKey enc (TapeZipper.apply M w v a)) := by
        refine ⟨?_, hd₁, hfinal⟩
        simp only [P, program, Program.step, d₁, point, hm, memory_left M leftKey rightKey enc hne,
          hx, List.map_nil, List.head?_nil, encode, TapeZipper.apply]
        congr 2
        simpa using memory_pop_left M leftKey rightKey enc hne [] v.right
      exact ⟨2, .cons hs₀ (.cons hs₁ (.nil _))⟩
    | cons g xs =>
      let d₂ := point M leftKey rightKey enc (.putRight a.state a.write g) nextInput xs v.right
      have hd₂ : StackMachine.Good w (s + 1) d₂ := by
        apply point_good M leftKey rightKey enc w (s + 1) _ _ _ _ hi' (by omega) _ hr
        simp only [hx, List.length_cons] at hl
        omega
      have hs₁ : SafeStep P w (s + 1) d₁ d₂ := by
        refine ⟨?_, hd₁, hd₂⟩
        simp only [P, program, Program.step, d₁, d₂, point, hm,
          memory_left M leftKey rightKey enc hne, hx, List.map_cons, List.head?_cons, hdec]
        congr 2
        simpa using memory_pop_left M leftKey rightKey enc hne (g :: xs) v.right
      have hs₂ : SafeStep P w (s + 1) d₂
          (encode M leftKey rightKey enc (TapeZipper.apply M w v a)) := by
        refine ⟨?_, hd₂, hfinal⟩
        simp only [P, program, Program.step, d₂, point, encode, TapeZipper.apply, hm, hx]
        rw [memory_push_right]
      exact ⟨3, .cons hs₀ (.cons hs₁ (.cons hs₂ (.nil _)))⟩

lemma run_input_bound {w : Word} {n : ℕ} {c : M.Config} (hr : M.Run w n c) :
    c.inputHead ≤ w.length + 1 := by
  induction hr with
  | zero => exact Nat.zero_le _
  | succ _ hs _ =>
    obtain ⟨a, _, rfl⟩ := hs
    exact min_le_right _ _

include hne hdec₀ hdec in
lemma run_simulation (hd : M.Deterministic) (w : Word) (s : ℕ) (hs : M.UsesSpace w s)
    {n : ℕ} {c : M.Config} (hr : M.Run w n c) :
    ∃ v : TapeZipper.View M, v.expand = c ∧ v.cells ≤ s ∧
      ∃ t, Path (SafeStep (program M leftKey rightKey enc dec) w (s + 1)) t
        (program M leftKey rightKey enc dec).initial (encode M leftKey rightKey enc v) := by
  induction hr with
  | zero =>
    refine ⟨TapeZipper.initial M, TapeZipper.initial_expand M, ?_, 0, ?_⟩
    · have hb := hs 0 M.initial .zero
      change 1 ≤ s
      change 0 < s at hb
      omega
    · simpa [Program.initial, program, encode, point, TapeZipper.initial, memory] using
        (Path.nil (program M leftKey rightKey enc dec).initial)
  | @succ n c d hr he ih =>
    obtain ⟨v, hv, hcells, t, ht⟩ := ih
    obtain ⟨a, ha, rfl⟩ := he
    have hv' : (TapeZipper.apply M w v a).expand = M.execute w c a := by
      rw [TapeZipper.apply_expand, hv]
    have hhead : (TapeZipper.apply M w v a).left.length < s := by
      change (TapeZipper.apply M w v a).expand.workHead < s
      rw [hv']
      exact hs (n + 1) _ (.succ hr ⟨a, ha, rfl⟩)
    have hcells' := TapeZipper.cells_preserved M w v a s hcells hhead
    have hin : v.inputHead ≤ w.length + 1 := by
      change v.expand.inputHead ≤ w.length + 1
      rw [hv]
      exact run_input_bound M hr
    have hchoice : choose M v.state (readInput w v.inputHead) v.current = some a := by
      apply choose_action M hd _ _ _ a
      rw [← hv] at ha
      simpa only [TapeZipper.current_scanned] using! ha
    obtain ⟨l, hl⟩ := action_path M leftKey rightKey enc dec hne hdec₀ hdec w s v a
      hin hcells hchoice hcells'
    exact ⟨_, hv', hcells', t + l, ht.append hl⟩

lemma terminal_halts (w : Word) (v : TapeZipper.View M) (hv : M.Terminal w v.expand) :
    (program M leftKey rightKey enc dec).step w (encode M leftKey rightKey enc v) = none := by
  have hc : choose M v.state (readInput w v.inputHead) v.current = none := by
    cases h : choose M v.state (readInput w v.inputHead) v.current with
    | none => rfl
    | some a =>
      have ha := choose_mem M v.state (readInput w v.inputHead) v.current a h
      exact (hv (M.execute w v.expand a) ⟨a,
        by simpa only [TapeZipper.current_scanned] using! ha, rfl⟩).elim
  simp [program, Program.step, encode, point, hc]

include hne hdec₀ hdec in
lemma constructor_run (hd : M.Deterministic) (w : Word) (s : ℕ) (hs : M.UsesSpace w s)
    (hh : ∃ n c, M.Run w n c ∧ M.Terminal w c ∧ c.workHead + 1 = s) :
    ∃ v : TapeZipper.View M, v.cells ≤ s ∧ v.left.length + 1 = s ∧
      (program M leftKey rightKey enc dec).step w (encode M leftKey rightKey enc v) = none ∧
      ∃ t, Path (SafeStep (program M leftKey rightKey enc dec) w (s + 1)) t
        (program M leftKey rightKey enc dec).initial (encode M leftKey rightKey enc v) := by
  obtain ⟨n, c, hr, ht, hpos⟩ := hh
  obtain ⟨v, hv, hcells, hp⟩ := run_simulation M leftKey rightKey enc dec hne hdec₀ hdec hd w s hs hr
  refine ⟨v, hcells, ?_, terminal_halts M leftKey rightKey enc dec w v (hv ▸ ht), hp⟩
  have he : v.expand.workHead + 1 = s := by simpa [hv] using hpos
  exact he

end

end Lax434930Proofs.SavitchProofs.TapeInterpreter
