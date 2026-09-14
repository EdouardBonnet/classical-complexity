import Lax434930Proofs.InclusionAux.PolynomialConfigurationGraph

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ReachabilityTable

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930Proofs
open PolynomialConfigurations
open scoped Classical

noncomputable section

def lookup (table : Word) (v : ℕ) : Bool := table[v]?.getD false
def initial (size start : ℕ) : Word := (List.range size).map (fun v => decide (v = start))
def step (size : ℕ) (edge : ℕ → ℕ → Bool) (table : Word) : Word :=
  (List.range size).map (fun v => lookup table v ||
    (List.range size).any (fun u => lookup table u && edge u v))
def table (size : ℕ) (edge : ℕ → ℕ → Bool) (start rounds : ℕ) : Word :=
  (step size edge)^[rounds] (initial size start)

lemma lookup_map (size v : ℕ) (f : ℕ → Bool) (hv : v < size) :
    lookup ((List.range size).map f) v = f v := by
  simp [lookup, List.getElem?_map, List.getElem?_range, hv]

@[simp] lemma initial_length (size start : ℕ) : (initial size start).length = size := by simp [initial]
@[simp] lemma step_length (size : ℕ) (edge : ℕ → ℕ → Bool) (t : Word) : (step size edge t).length = size := by simp [step]

lemma lookup_step (size v : ℕ) (edge : ℕ → ℕ → Bool) (t : Word) (hv : v < size) :
    lookup (step size edge t) v = true ↔ lookup t v = true ∨
      ∃ u, u < size ∧ lookup t u = true ∧ edge u v = true := by
  rw [step, lookup_map _ _ _ hv]
  simp [List.any_eq_true, and_assoc]

inductive Walk (size : ℕ) (edge : ℕ → ℕ → Bool) (start : ℕ) : ℕ → ℕ → Prop
  | zero : Walk size edge start 0 start
  | succ {n u v} : Walk size edge start n u → v < size → edge u v = true →
      Walk size edge start (n + 1) v

lemma Walk.valid {size start n v : ℕ} {edge : ℕ → ℕ → Bool}
    (hstart : start < size) (h : Walk size edge start n v) : v < size := by
  cases h with | zero => exact hstart | succ _ hv _ => exact hv

lemma table_correct (size start rounds v : ℕ) (edge : ℕ → ℕ → Bool)
    (hstart : start < size) (hv : v < size) :
    lookup (table size edge start rounds) v = true ↔
      ∃ n, n ≤ rounds ∧ Walk size edge start n v := by
  induction rounds generalizing v with
  | zero =>
    simp only [table, Function.iterate_zero_apply, initial, lookup_map _ _ _ hv, decide_eq_true_eq,
      Nat.le_zero, exists_eq_left]
    constructor
    · rintro rfl; exact .zero
    · intro h; cases h; rfl
  | succ rounds ih =>
    rw [table, Function.iterate_succ_apply', lookup_step _ _ _ _ hv]
    change (lookup (table size edge start rounds) v = true ∨
      ∃ u, u < size ∧ lookup (table size edge start rounds) u = true ∧ edge u v = true) ↔ _
    constructor
    · rintro (h | ⟨u, hu, hreach, he⟩)
      · obtain ⟨n, hn, hwalk⟩ := (ih v hv).mp h
        exact ⟨n, by omega, hwalk⟩
      · obtain ⟨n, hn, hwalk⟩ := (ih u hu).mp hreach
        exact ⟨n + 1, by omega, .succ hwalk hv he⟩
    · rintro ⟨n, hn, hwalk⟩
      cases hwalk with
      | zero => exact Or.inl ((ih start hstart).mpr ⟨0, by omega, .zero⟩)
      | @succ n u v hwalk hv he =>
        have hu := hwalk.valid hstart
        exact Or.inr ⟨u, hu, (ih u hu).mpr ⟨n, by omega, hwalk⟩, he⟩

def graphEdge (M : Machine) (c : ℕ) (w : Word) (v u : ℕ) : Bool := decide (Edge M c w v u)

lemma walk_run (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word) {n v : ℕ}
    (h : Walk (vertexCount M c w.length) (graphEdge M c w) (startVertex M) n v) :
    M.Run w n (expand M c w.length v) := by
  induction h with
  | zero => rw [expand_start]; exact .zero
  | @succ n u v hwalk hv he ih =>
    have hu := hwalk.valid (startVertex_lt M c w.length hc)
    apply Machine.Run.succ ih
    exact (edge_iff_step M c hc w u v hu hv).mp (of_decide_eq_true he)

lemma run_walk (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word)
    (hs : M.UsesSpace w (c * Nat.log 2 (w.length + 2))) {n : ℕ} {d : M.Config}
    (hr : M.Run w n d) :
    ∃ v, v < vertexCount M c w.length ∧ expand M c w.length v = d ∧
      Walk (vertexCount M c w.length) (graphEdge M c w) (startVertex M) n v := by
  induction hr with
  | zero => exact ⟨startVertex M, startVertex_lt M c w.length hc, expand_start M c w.length, .zero⟩
  | @succ n d e hr he ih =>
    obtain ⟨u, hu, hud, hwalk⟩ := ih
    obtain ⟨v, hv, hve⟩ := pack_run M c hc w hs (.succ hr he)
    refine ⟨v, hv, hve, .succ hwalk hv ?_⟩
    change decide (Edge M c w u v) = true
    apply decide_eq_true
    apply (edge_iff_step M c hc w u v hu hv).mpr
    simpa [hud, hve] using he

def rounds (M : Machine) (c n : ℕ) : ℕ := (ConfigurationTime.logTimePolynomial M c).eval n
def resultTable (M : Machine) (c : ℕ) (w : Word) : Word :=
  table (vertexCount M c w.length) (graphEdge M c w) (startVertex M) (rounds M c w.length)
def answer (M : Machine) (c : ℕ) (w : Word) : Bool :=
  (List.range (vertexCount M c w.length)).any (fun v =>
    lookup (resultTable M c w) v && accepting M c w v)

lemma answer_correct (M : Machine) (c : ℕ) (hc : 0 < c) (A : Language)
    (hdec : M.Decides A) (hs : ∀ w, M.UsesSpace w (c * Nat.log 2 (w.length + 2))) (w : Word) :
    answer M c w = true ↔ w ∈ A := by
  rw [← (hdec w).2]
  simp only [answer, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨v, hv, htable, ha⟩
    obtain ⟨n, _, hwalk⟩ := (table_correct _ _ _ _ _ (startVertex_lt M c w.length hc) hv).mp htable
    exact ⟨n, expand M c w.length v, walk_run M c hc w hwalk, (accepting_true M c w v).mp ha⟩
  · rintro ⟨n, d, hr, ht, ha⟩
    obtain ⟨v, hv, hvd, hwalk⟩ := run_walk M c hc w (hs w) hr
    have hn := ConfigurationTime.logarithmic_space_branch_time M c (fun x => (hdec x).1) hs w n d hr
    refine ⟨v, hv, ?_, ?_⟩
    · exact (table_correct _ _ _ _ _ (startVertex_lt M c w.length hc) hv).mpr ⟨n, hn.le, hwalk⟩
    · apply (accepting_true M c w v).mpr
      simpa [hvd] using And.intro ht ha

end

end Lax434930Proofs.InclusionAux.ReachabilityTable
