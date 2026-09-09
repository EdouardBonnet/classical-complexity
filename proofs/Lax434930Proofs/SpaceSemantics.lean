import Lax434930.SpaceMachines
import Lax434930.SpaceBounds
import Lax434930.LogarithmicSpace
import Mathlib.Tactic

namespace Lax434930Proofs.SpaceSemantics

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds

variable {M : Machine} {w : Word} {n s : ℕ} {c : M.Config}

/-- An input head has only length plus two possible positions, including both endmarkers. -/
theorem inputHead_le (hr : M.Run w n c) : c.inputHead ≤ w.length + 1 := by
  induction hr with
  | zero => exact Nat.zero_le _
  | succ _ hs _ =>
    obtain ⟨a, _, rfl⟩ := hs
    exact min_le_right _ _

/-- In n transitions a work head cannot have reached a cell to the right of n. -/
theorem workHead_le_time (hr : M.Run w n c) : c.workHead ≤ n := by
  induction hr with
  | zero => exact Nat.zero_le _
  | succ _ hs ih =>
    obtain ⟨a, _, rfl⟩ := hs
    change a.workMove.apply _ ≤ _
    cases a.workMove <;> simp only [Move.apply] <;> omega

/-- A bounded run cannot obtain information from the infinite tail of the work-tape function. -/
theorem unvisited_tail_blank (hb : M.UsesSpace w s) (hr : M.Run w n c)
    (i : ℕ) (hi : s ≤ i) : c.tape i = M.blank := by
  induction hr with
  | zero => rfl
  | @succ n c d hr hs ih =>
    obtain ⟨a, _, rfl⟩ := hs
    have hc := hb n c hr
    change Function.update c.tape c.workHead a.write i = M.blank
    rw [Function.update_of_ne (by omega : i ≠ c.workHead)]
    exact ih

/-- The space bound includes the initial scanned cell, even on the empty input. -/
theorem space_positive (hb : M.UsesSpace w s) : 0 < s :=
  hb 0 M.initial .zero

/-- The formal local determinism condition gives at most one successor configuration. -/
theorem deterministic_step (hd : M.Deterministic) {a b d : M.Config}
    (hab : M.Step w a b) (had : M.Step w a d) : b = d := by
  obtain ⟨x, hx, rfl⟩ := hab
  obtain ⟨y, hy, rfl⟩ := had
  rw [hd _ _ _ x hx y hy]

/-- An infinite path would yield a computation prefix of every length. -/
theorem not_infinite_path (hh : M.HaltsOn w) (path : ℕ → M.Config)
    (hzero : path 0 = M.initial) : ¬ ∀ k, M.Step w (path k) (path (k + 1)) := by
  intro hp
  have hr : ∀ k, M.Run w k (path k) := by
    intro k
    induction k with
    | zero => simpa only [hzero] using (Machine.Run.zero (M := M) (w := w))
    | succ k ih => exact .succ ih (hp k)
  obtain ⟨t, ht⟩ := hh
  have := ht (t + 1) (path (t + 1)) (hr (t + 1))
  omega

/-- A concrete finite decider that immediately returns the supplied bit. -/
def constantMachine (answer : Bool) : Machine where
  Γ := Unit
  Q := Unit
  blank := ()
  start := ()
  transition _ _ _ := ∅
  accept _ := answer

theorem constant_no_step (answer : Bool) (w : Word)
    (c d : (constantMachine answer).Config) : ¬ (constantMachine answer).Step w c d := by
  rintro ⟨a, ha, _⟩
  exact Finset.notMem_empty a ha

theorem constant_run (answer : Bool) (w : Word) (n : ℕ)
    (c : (constantMachine answer).Config) (h : (constantMachine answer).Run w n c) :
    n = 0 ∧ c = (constantMachine answer).initial := by
  cases h with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ hs => exact False.elim (constant_no_step _ _ _ _ hs)

theorem constant_decides (answer : Bool) :
    (constantMachine answer).Decides { _w : Word | answer = true } := by
  intro w
  constructor
  · exact ⟨0, fun n c h => (constant_run answer w n c h).1.le⟩
  · constructor
    · rintro ⟨n, c, _, _, h⟩
      exact h
    · intro h
      exact ⟨0, _, .zero, fun d => constant_no_step _ _ _ d, h⟩

/-- Empty and universal languages really have deterministic logarithmic-space deciders. -/
theorem constant_language_in_L (answer : Bool) :
    { _w : Word | answer = true } ∈ Lax434930.LogarithmicSpace.L := by
  refine ⟨1, by decide, constantMachine answer, ?_, constant_decides answer, ?_⟩
  · intro q i b a ha
    exact (Finset.notMem_empty a ha).elim
  · intro w n c hr
    obtain ⟨rfl, rfl⟩ := constant_run answer w n c hr
    simpa only [Machine.initial, one_mul, logSpace] using
      (Nat.log_pos (by decide : 1 < (2 : ℕ)) (by omega : 2 ≤ w.length + 2))

end Lax434930Proofs.SpaceSemantics
