import Lax434930.SpaceMachines
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SpacePaths

open Lax434930.PolynomialTime Lax434930.SpaceMachines

variable {α : Type} {R : α → α → Prop}

inductive Path (R : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Path R 0 a a
  | cons {n : ℕ} {a b c : α} : R a b → Path R n b c → Path R (n + 1) a c

lemma Path.append {r s : ℕ} {a b c : α}
    (h : Path R r a b) (g : Path R s b c) : Path R (r + s) a c := by
  induction h with
  | nil => simpa using g
  | cons he _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Path.cons he (ih g)

lemma Path.map {S : α → α → Prop} (hRS : ∀ a b, R a b → S a b)
    {n : ℕ} {a b : α} (h : Path R n a b) : Path S n a b := by
  induction h with
  | nil => exact .nil _
  | cons he _ ih => exact .cons (hRS _ _ he) ih

lemma Path.run {M : Machine} {w : Word} {n r : ℕ} {c d : M.Config}
    (h : Path (M.Step w) n c d) (hc : M.Run w r c) : M.Run w (r + n) d := by
  induction h generalizing r with
  | nil => simpa using hc
  | cons he _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (.succ hc he)

lemma run_path {M : Machine} {w : Word} {n : ℕ} {c : M.Config}
    (h : M.Run w n c) : Path (M.Step w) n M.initial c := by
  induction h with
  | zero => exact .nil _
  | succ _ he ih => exact ih.append (.cons he (.nil _))

lemma step_unique {M : Machine} (hd : M.Deterministic) {w : Word} {a b c : M.Config}
    (h : M.Step w a b) (g : M.Step w a c) : b = c := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := g
  rw [hd _ _ _ x hx y hy]

def Bounded (M : Machine) (w : Word) (bound : ℕ) (a b : M.Config) : Prop :=
  M.Step w a b ∧ a.workHead < bound ∧ b.workHead < bound

def Trace (M : Machine) (w : Word) (bound : ℕ) (a b : M.Config) : Prop :=
  a.workHead < bound ∧ ∃ n, Path (Bounded M w bound) n a b

lemma Trace.refl {M : Machine} {w : Word} {bound : ℕ} {a : M.Config}
    (ha : a.workHead < bound) : Trace M w bound a a := ⟨ha, 0, .nil _⟩

lemma Trace.single {M : Machine} {w : Word} {bound : ℕ} {a b : M.Config}
    (h : M.Step w a b) (ha : a.workHead < bound) (hb : b.workHead < bound) :
    Trace M w bound a b := ⟨ha, 1, .cons ⟨h, ha, hb⟩ (.nil _)⟩

lemma Trace.trans {M : Machine} {w : Word} {bound : ℕ} {a b c : M.Config}
    (h : Trace M w bound a b) (g : Trace M w bound b c) : Trace M w bound a c := by
  obtain ⟨ha, r, hr⟩ := h
  obtain ⟨_, s, hs⟩ := g
  exact ⟨ha, r + s, hr.append hs⟩

lemma terminal_path_bound {M : Machine} {w : Word} {bound n : ℕ} {a z : M.Config}
    (hd : M.Deterministic) (h : Path (Bounded M w bound) n a z)
    (ha : a.workHead < bound) (hz : M.Terminal w z) :
    ∀ m c, Path (M.Step w) m a c → m ≤ n ∧ c.workHead < bound := by
  induction h with
  | nil a =>
    intro m c hc
    cases hc with
    | nil => exact ⟨le_rfl, ha⟩
    | cons he _ => exact (hz _ he).elim
  | @cons n a b z he hrest ih =>
    intro m c hc
    cases hc with
    | nil => exact ⟨Nat.zero_le _, ha⟩
    | @cons m _ b' _ he' hc =>
      obtain rfl := step_unique hd he.1 he'
      obtain ⟨hm, hb⟩ := ih he.2.2 hz m c hc
      exact ⟨Nat.succ_le_succ hm, hb⟩

lemma terminal_path_unique {M : Machine} {w : Word} {n m : ℕ} {a z c : M.Config}
    (hd : M.Deterministic) (h : Path (M.Step w) n a z) (hz : M.Terminal w z)
    (hc : Path (M.Step w) m a c) (ht : M.Terminal w c) : z = c := by
  induction h generalizing m c with
  | nil =>
    cases hc with
    | nil => rfl
    | cons he _ => exact (hz _ he).elim
  | cons he _ ih =>
    cases hc with
    | nil => exact (ht _ he).elim
    | cons he' hc =>
      obtain rfl := step_unique hd he he'
      exact ih hz hc ht

lemma trace_decider {M : Machine} {w : Word} {bound : ℕ} {z : M.Config}
    (hd : M.Deterministic) (h : Trace M w bound M.initial z) (hz : M.Terminal w z) :
    M.HaltsOn w ∧ M.UsesSpace w bound ∧ (M.Accepts w ↔ M.accept z.state = true) := by
  obtain ⟨ha, n, hn⟩ := h
  have hr : M.Run w n z := by
    simpa using (hn.map (fun _ _ h => h.1)).run (Machine.Run.zero (M := M) (w := w))
  have hb := terminal_path_bound hd hn ha hz
  refine ⟨⟨n, fun m c hc => (hb m c (run_path hc)).1⟩,
    (fun m c hc => (hb m c (run_path hc)).2), ?_⟩
  constructor
  · rintro ⟨m, c, hc, ht, haccept⟩
    obtain rfl := terminal_path_unique hd (run_path hr) hz (run_path hc) ht
    exact haccept
  · intro haccept
    exact ⟨n, z, hr, hz, haccept⟩

end Lax434930Proofs.SpacePaths
