import Lax434930Proofs.InclusionAux.RadixTape
import Mathlib.Data.Fintype.EquivFin

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.PolynomialConfigurations

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930Proofs
open scoped Classical

noncomputable section

lemma alphabet_pos (M : Machine) : 0 < Fintype.card M.Γ := Fintype.card_pos_iff.mpr ⟨M.blank⟩
lemma states_pos (M : Machine) : 0 < Fintype.card M.Q := Fintype.card_pos_iff.mpr ⟨M.start⟩

def base (M : Machine) : ℕ := Fintype.card M.Γ + 1

def symbolCode (M : Machine) (g : M.Γ) : ℕ :=
  if g = M.blank then 0 else (Fintype.equivFin M.Γ g).val + 1

def symbolRead (M : Machine) (n : ℕ) : M.Γ :=
  if n = 0 then M.blank else
    (Fintype.equivFin M.Γ).symm ⟨(n - 1) % Fintype.card M.Γ, Nat.mod_lt _ (alphabet_pos M)⟩

@[simp] lemma symbolCode_blank (M : Machine) : symbolCode M M.blank = 0 := by simp [symbolCode]
@[simp] lemma symbolRead_zero (M : Machine) : symbolRead M 0 = M.blank := by simp [symbolRead]

lemma symbolCode_lt (M : Machine) (g : M.Γ) : symbolCode M g < base M := by
  have h := (Fintype.equivFin M.Γ g).isLt
  simp only [symbolCode, base]
  split <;> omega

@[simp] lemma symbolRead_code (M : Machine) (g : M.Γ) : symbolRead M (symbolCode M g) = g := by
  by_cases h : g = M.blank
  · subst g; simp
  · simp [symbolCode, h, symbolRead, Nat.mod_eq_of_lt (Fintype.equivFin M.Γ g).isLt]

def tapeCode (M : Machine) (tape : ℕ → M.Γ) (s : ℕ) : ℕ :=
  RadixTape.encode (base M) ((List.range s).map (fun i => symbolCode M (tape i)))

def tapeRead (M : Machine) (value i : ℕ) : M.Γ :=
  symbolRead M (value / base M ^ i % base M)

lemma tapeCode_lt (M : Machine) (tape : ℕ → M.Γ) (s : ℕ) : tapeCode M tape s < base M ^ s := by
  simpa [tapeCode] using RadixTape.encode_lt (base M) (by simp [base])
    ((List.range s).map (fun i => symbolCode M (tape i))) (by
      intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      exact symbolCode_lt M (tape i))

lemma tapeRead_code (M : Machine) (tape : ℕ → M.Γ) (s : ℕ)
    (htail : ∀ i, s ≤ i → tape i = M.blank) (i : ℕ) : tapeRead M (tapeCode M tape s) i = tape i := by
  have h := RadixTape.digit_encode (base M) (by simp [base])
    ((List.range s).map (fun j => symbolCode M (tape j))) (by
      intro d hd
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hd
      exact symbolCode_lt M (tape j)) i
  dsimp [tapeRead, tapeCode]
  rw [h]
  by_cases hi : i < s
  · simp [List.getElem?_map, List.getElem?_range, hi]
  · simp [List.getElem?_map, List.getElem?_range, hi, htail i (by omega)]

lemma tapeRead_tail (M : Machine) (value i : ℕ) (h : value ≤ i) : tapeRead M value i = M.blank := by
  rw [tapeRead, RadixTape.digit_zero _ _ _ (by have := alphabet_pos M; simp [base]; omega) h]
  exact symbolRead_zero M

def stateCode (M : Machine) (q : M.Q) : ℕ := (Fintype.equivFin M.Q q).val
def stateRead (M : Machine) (q : ℕ) : M.Q :=
  (Fintype.equivFin M.Q).symm ⟨q % Fintype.card M.Q, Nat.mod_lt _ (states_pos M)⟩

@[simp] lemma stateRead_code (M : Machine) (q : M.Q) : stateRead M (stateCode M q) = q := by
  simp [stateRead, stateCode, Nat.mod_eq_of_lt (Fintype.equivFin M.Q q).isLt]

def headBound (c n : ℕ) : ℕ := c * (n + 2)
def tapeBound (M : Machine) (c n : ℕ) : ℕ := (n + 2) ^ (base M * c)
def vertexCount (M : Machine) (c n : ℕ) : ℕ :=
  Fintype.card M.Q * (n + 2) * headBound c n * tapeBound M c n

def vertexCode (M : Machine) (c n : ℕ) (q i h tape : ℕ) : ℕ :=
  q + Fintype.card M.Q * (i + (n + 2) * (h + headBound c n * tape))

def inputIndex (M : Machine) (n v : ℕ) : ℕ := v / Fintype.card M.Q % (n + 2)
def workIndex (M : Machine) (c n v : ℕ) : ℕ := v / Fintype.card M.Q / (n + 2) % headBound c n
def tapeIndex (M : Machine) (c n v : ℕ) : ℕ := v / Fintype.card M.Q / (n + 2) / headBound c n

lemma indices_code (M : Machine) (c n q i h tape : ℕ)
    (hc : 0 < c) (hq : q < Fintype.card M.Q) (hi : i < n + 2) (hh : h < headBound c n) :
    vertexCode M c n q i h tape % Fintype.card M.Q = q ∧
    inputIndex M n (vertexCode M c n q i h tape) = i ∧
    workIndex M c n (vertexCode M c n q i h tape) = h ∧
    tapeIndex M c n (vertexCode M c n q i h tape) = tape := by
  have hhead : 0 < headBound c n := Nat.mul_pos hc (by omega)
  simp [vertexCode, inputIndex, workIndex, tapeIndex,
    Nat.add_mul_div_left _ _ (states_pos M), Nat.add_mul_div_left _ _ (by omega : 0 < n + 2),
    Nat.add_mul_div_left _ _ hhead, Nat.div_eq_of_lt hq, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hh,
    Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hh]

lemma vertexCode_lt (M : Machine) (c n q i h tape : ℕ)
    (hq : q < Fintype.card M.Q) (hi : i < n + 2) (hh : h < headBound c n)
    (ht : tape < tapeBound M c n) : vertexCode M c n q i h tape < vertexCount M c n := by
  have h₁ : h + headBound c n * tape < headBound c n * tapeBound M c n := by nlinarith
  have h₂ : i + (n + 2) * (h + headBound c n * tape) <
      (n + 2) * (headBound c n * tapeBound M c n) := by nlinarith
  dsimp [vertexCode, vertexCount]
  nlinarith

def expand (M : Machine) (c n v : ℕ) : M.Config :=
  ⟨stateRead M v, inputIndex M n v, workIndex M c n v, tapeRead M (tapeIndex M c n v)⟩

lemma pack_run (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word)
    (hs : M.UsesSpace w (c * Nat.log 2 (w.length + 2)))
    {k : ℕ} {d : M.Config} (hr : M.Run w k d) :
    ∃ v, v < vertexCount M c w.length ∧ expand M c w.length v = d := by
  let s := c * Nat.log 2 (w.length + 2)
  let t := tapeCode M d.tape s
  let v := vertexCode M c w.length (stateCode M d.state) d.inputHead d.workHead t
  have hq : stateCode M d.state < Fintype.card M.Q := (Fintype.equivFin M.Q d.state).isLt
  have hi : d.inputHead < w.length + 2 := by have := SpaceSemantics.inputHead_le hr; omega
  have hh : d.workHead < headBound c w.length :=
    (hs k d hr).trans_le (Nat.mul_le_mul_left c (Nat.log_le_self 2 (w.length + 2)))
  have ht : t < tapeBound M c w.length :=
    (tapeCode_lt M d.tape s).trans_le (RadixTape.log_power_bound (base M) c w.length)
  have hv := indices_code M c w.length (stateCode M d.state) d.inputHead d.workHead t hc hq hi hh
  refine ⟨v, vertexCode_lt M c w.length _ _ _ _ hq hi hh ht, ?_⟩
  have htape : tapeRead M t = d.tape := by
    funext i
    exact tapeRead_code M d.tape s (fun i hi => SpaceSemantics.unvisited_tail_blank hs hr i hi) i
  have hstate : stateRead M v = d.state := by
    dsimp [stateRead]
    change (Fintype.equivFin M.Q).symm ⟨v % Fintype.card M.Q, _⟩ = d.state
    have hfin : (⟨v % Fintype.card M.Q, Nat.mod_lt _ (states_pos M)⟩ : Fin (Fintype.card M.Q)) =
        Fintype.equivFin M.Q d.state := Fin.ext hv.1
    rw [hfin]
    exact (Fintype.equivFin M.Q).symm_apply_apply d.state
  change Configuration.mk (stateRead M v) (inputIndex M w.length v)
    (workIndex M c w.length v) (tapeRead M (tapeIndex M c w.length v)) = d
  have hinput : inputIndex M w.length v = d.inputHead := hv.2.1
  have hwork : workIndex M c w.length v = d.workHead := hv.2.2.1
  have htapeIndex : tapeIndex M c w.length v = t := hv.2.2.2
  rw [hstate, hinput, hwork, htapeIndex, htape]

end

end Lax434930Proofs.InclusionAux.PolynomialConfigurations
