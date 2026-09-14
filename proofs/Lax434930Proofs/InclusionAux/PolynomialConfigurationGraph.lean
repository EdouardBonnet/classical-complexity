import Lax434930Proofs.InclusionAux.PolynomialConfigurations

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.PolynomialConfigurations

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open scoped Classical

noncomputable section

lemma headBound_pos (c n : ℕ) (hc : 0 < c) : 0 < headBound c n := Nat.mul_pos hc (by omega)
lemma tapeBound_pos (M : Machine) (c n : ℕ) : 0 < tapeBound M c n := pow_pos (by omega) _

lemma inputIndex_lt (M : Machine) (n v : ℕ) : inputIndex M n v < n + 2 := Nat.mod_lt _ (by omega)
lemma workIndex_lt (M : Machine) (c n v : ℕ) (hc : 0 < c) : workIndex M c n v < headBound c n :=
  Nat.mod_lt _ (headBound_pos c n hc)

lemma tapeIndex_lt (M : Machine) (c n v : ℕ) (hc : 0 < c) (hv : v < vertexCount M c n) :
    tapeIndex M c n v < tapeBound M c n := by
  have hpos : 0 < Fintype.card M.Q * (n + 2) * headBound c n :=
    Nat.mul_pos (Nat.mul_pos (states_pos M) (by omega)) (headBound_pos c n hc)
  rw [tapeIndex, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rw [← Nat.mul_assoc]
  apply (Nat.div_lt_iff_lt_mul hpos).mpr
  simpa [vertexCount, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hv

def graphPolynomial (M : Machine) (c : ℕ) : Polynomial ℕ :=
  Polynomial.C (Fintype.card M.Q) * (Polynomial.X + Polynomial.C 2) *
    (Polynomial.C c * (Polynomial.X + Polynomial.C 2)) *
    (Polynomial.X + Polynomial.C 2) ^ (base M * c)

@[simp] lemma graphPolynomial_eval (M : Machine) (c n : ℕ) :
    (graphPolynomial M c).eval n = vertexCount M c n := by
  simp [graphPolynomial, vertexCount, headBound, tapeBound]

def startVertex (M : Machine) : ℕ := stateCode M M.start

lemma startVertex_lt (M : Machine) (c n : ℕ) (hc : 0 < c) : startVertex M < vertexCount M c n := by
  simpa [vertexCode, startVertex] using vertexCode_lt M c n (stateCode M M.start) 0 0 0
    (Fintype.equivFin M.Q M.start).isLt (by omega) (headBound_pos c n hc) (tapeBound_pos M c n)

lemma expand_start (M : Machine) (c n : ℕ) : expand M c n (startVertex M) = M.initial := by
  have hq : stateCode M M.start < Fintype.card M.Q := (Fintype.equivFin M.Q M.start).isLt
  simp [expand, startVertex, inputIndex, workIndex, tapeIndex, Nat.div_eq_of_lt hq,
    Machine.initial, tapeRead, symbolRead]
  funext i
  simp [tapeRead]

def tapeLimit (M : Machine) (c n : ℕ) : ℕ := tapeBound M c n + headBound c n

def actions (M : Machine) (c : ℕ) (w : Word) (v : ℕ) : Finset (Action M.Γ M.Q) :=
  M.transition (stateRead M v) (readInput w (inputIndex M w.length v))
    (tapeRead M (tapeIndex M c w.length v) (workIndex M c w.length v))

def Edge (M : Machine) (c : ℕ) (w : Word) (v u : ℕ) : Prop :=
  ∃ a ∈ actions M c w v,
    stateRead M u = a.state ∧
    inputIndex M w.length u = min (a.inputMove.apply (inputIndex M w.length v)) (w.length + 1) ∧
    workIndex M c w.length u = a.workMove.apply (workIndex M c w.length v) ∧
    ∀ i, i < tapeLimit M c w.length →
      tapeRead M (tapeIndex M c w.length u) i =
        if i = workIndex M c w.length v then a.write else tapeRead M (tapeIndex M c w.length v) i

lemma edge_iff_step (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word) (v u : ℕ)
    (hv : v < vertexCount M c w.length) (hu : u < vertexCount M c w.length) :
    Edge M c w v u ↔ M.Step w (expand M c w.length v) (expand M c w.length u) := by
  constructor
  · rintro ⟨a, ha, hq, hi, hh, ht⟩
    refine ⟨a, ha, ?_⟩
    dsimp [expand, Machine.execute]
    rw [hq, hi, hh]
    congr 1
    funext i
    by_cases hlim : i < tapeLimit M c w.length
    · simpa [Function.update_apply] using ht i hlim
    · have hhead : i ≠ workIndex M c w.length v := by
        have hh := workIndex_lt M c w.length v hc
        dsimp [tapeLimit] at hlim
        omega
      have ht₁ := tapeIndex_lt M c w.length v hc hv
      have ht₂ := tapeIndex_lt M c w.length u hc hu
      dsimp [tapeLimit] at hlim
      simp [Function.update_of_ne hhead, tapeRead_tail M _ i (by omega : tapeIndex M c w.length u ≤ i),
        tapeRead_tail M _ i (by omega : tapeIndex M c w.length v ≤ i)]
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, congrArg Configuration.state he, congrArg Configuration.inputHead he,
      congrArg Configuration.workHead he, ?_⟩
    intro i hi
    have ht := congrFun (congrArg Configuration.tape he) i
    simpa [expand, Machine.execute, Function.update_apply] using ht

lemma terminal_iff_empty (M : Machine) (c : ℕ) (w : Word) (v : ℕ) :
    M.Terminal w (expand M c w.length v) ↔ actions M c w v = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro a ha
    exact h (M.execute w (expand M c w.length v) a) ⟨a, ha, rfl⟩
  · intro h d hd
    obtain ⟨a, ha, _⟩ := hd
    change a ∈ actions M c w v at ha
    rw [h] at ha
    simpa using ha

def accepting (M : Machine) (c : ℕ) (w : Word) (v : ℕ) : Bool :=
  decide (actions M c w v = ∅) && M.accept (stateRead M v)

lemma accepting_true (M : Machine) (c : ℕ) (w : Word) (v : ℕ) :
    accepting M c w v = true ↔ M.Terminal w (expand M c w.length v) ∧
      M.accept (expand M c w.length v).state = true := by
  rw [terminal_iff_empty]
  simp [accepting, expand]

end

end Lax434930Proofs.InclusionAux.PolynomialConfigurations
