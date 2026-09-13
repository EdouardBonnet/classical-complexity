import Lax434930Proofs.SavitchProofs.CountInput
import Lax434930Proofs.SavitchProofs.ParkMachine
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.UnaryPolynomial

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Exec Good assigned)
open StackMacros (Macro)
open scoped Classical

noncomputable section

def sumCode {m : ℕ} (coeff : ℕ → ℕ) : (count : ℕ) → count ≤ m + 1 → Code m
  | 0, _ => .assign (fun s => {s with value := none})
  | count + 1, h => .seq (sumCode coeff count (by omega)) (monomial count (by omega) (coeff count))

lemma sum_exec {m : ℕ} (coeff : ℕ → ℕ) (count : ℕ) (hcount : count ≤ m + 1)
    (n : ℕ) (w : Word) (bound : ℕ) (d : Data m) (hd : Good w bound d)
    (hn : d.store .input = List.replicate n ()) (ha : d.store .aux = [])
    (hc : ∀ k : Fin m, d.store (.counter k) = [])
    (hb : (∑ i ∈ Finset.range count, coeff i * n ^ i) + (d.store .output).length < bound) :
    Exec w bound (sumCode coeff count hcount) d
      (grown d (∑ i ∈ Finset.range count, coeff i * n ^ i)) := by
  induction count generalizing d with
  | zero => simpa [sumCode, grown_zero] using Exec.assign d (fun s => {s with value := none}) hd
  | succ count ih =>
    rw [Finset.sum_range_succ] at hb ⊢
    let total := ∑ i ∈ Finset.range count, coeff i * n ^ i
    have hs := ih (by omega) d hd hn ha hc (by change total + _ < bound; change total + _ + _ < bound at hb; omega)
    let de := grown d total
    have hen : de.store .input = List.replicate n () := by simpa [de, grown] using hn
    have hea : de.store .aux = [] := by simpa [de, grown] using ha
    have hec (k : Fin m) (_ : k.val < count) : de.store (.counter k) = [] := by simpa [de, grown] using hc k
    have heb : coeff count * n ^ count + (de.store .output).length < bound := by
      simpa [de, grown, total, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
    have hm := monomial_exec count (by omega) (coeff count) n w bound de hs.good.2 hen hea hec heb
    simpa only [de, grown_add] using! Exec.seq hs hm

def polynomialCode (p : Polynomial ℕ) : Code p.natDegree := sumCode p.coeff (p.natDegree + 1) le_rfl

lemma polynomial_exec (p : Polynomial ℕ) (n : ℕ) (w : Word) (bound : ℕ) (d : Data p.natDegree)
    (hd : Good w bound d) (hn : d.store .input = List.replicate n ())
    (ha : d.store .aux = []) (hc : ∀ k : Fin p.natDegree, d.store (.counter k) = [])
    (hb : p.eval n + (d.store .output).length < bound) :
    Exec w bound (polynomialCode p) d (grown d (p.eval n)) := by
  simpa only [Polynomial.eval_eq_sum_range] using!
    sum_exec p.coeff (p.natDegree + 1) le_rfl n w bound d hd hn ha hc
      (by simpa only [Polynomial.eval_eq_sum_range] using hb)

def padding (m : ℕ) : Macro (Register m) Unit Unit :=
  Macro.seq (Macro.copy .input .output .aux) (Macro.putWord .output [()])

def padded (m : ℕ) (w : Word) : Data m :=
  ⟨{initial m with input := .rightEnd}, w.length + 1,
    Function.update (countResult m w).store .output (List.replicate (w.length + 1) ())⟩

lemma padding_spec (m : ℕ) (w : Word) (bound : ℕ) (hb : w.length + 1 < bound) :
    (padding m).guard w bound (countResult m w) ∧
      (padding m).result w (countResult m w) = padded m w := by
  refine ⟨?_, ?_⟩
  · simpa [padding, Macro.seq, Macro.copy, Macro.putWord, countResult, Nat.add_comm] using hb
  · simp [padding, Macro.seq, Macro.copy, Macro.putWord, countResult, padded, initial,
      List.replicate_succ]

def constructorCode (p : Polynomial ℕ) : Code p.natDegree :=
  .seq (countCode p.natDegree) (.seq (padding p.natDegree).code (polynomialCode p))

def constructor (p : Polynomial ℕ) : Machine := ParkMachine.stackMachine (constructorCode p) (initial p.natDegree) .output

lemma constructor_execution (p : Polynomial ℕ) (w : Word) :
    (constructor p).HaltsOn w ∧ (constructor p).UsesSpace w (p.eval w.length + w.length + 2) ∧
      ∃ t c, (constructor p).Run w t c ∧ (constructor p).Terminal w c ∧
        c.workHead + 1 = p.eval w.length + w.length + 2 := by
  let bound := p.eval w.length + w.length + 2
  have hcount := count_exec p.natDegree w bound (by dsimp [bound]; omega)
  have hpad := padding_spec p.natDegree w bound (by dsimp [bound]; omega)
  have hp : Exec w bound (padding p.natDegree).code (countResult p.natDegree w) (padded p.natDegree w) := by
    rw [← hpad.2]
    exact (padding p.natDegree).correct w bound _ hcount.good.2 hpad.1
  have hpoly := polynomial_exec p w.length w bound (padded p.natDegree w) hp.good.2
    (by simp [padded, countResult]) (by simp [padded, countResult])
    (by intro k; simp [padded, countResult])
    (by simp [padded, bound]; omega)
  have he : Exec w bound (constructorCode p) ⟨initial p.natDegree, 0, fun _ => []⟩
      (grown (padded p.natDegree w) (p.eval w.length)) := .seq hcount (.seq hp hpoly)
  obtain ⟨hh, hs, t, c, hr, ht, hc⟩ := ParkMachine.stack_execution (constructorCode p) (initial p.natDegree)
    .output w bound (by dsimp [bound]; omega) _ he
  refine ⟨hh, hs, t, c, hr, ht, ?_⟩
  rw [hc]
  simp [grown, padded]
  omega

end

end Lax434930Proofs.SavitchProofs.UnaryPolynomial
