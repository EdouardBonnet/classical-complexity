import Lax434930Proofs.InclusionAux.TimeHelpers.OutputNumbers

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930.PolynomialTime Polynomial

variable {I : Type}

def Number.power (n : Number I) : ℕ → Number I
  | 0 => .constant 1
  | k + 1 => (Number.power n k).mul n

lemma Number.power_value (n : Number I) (k : ℕ) (a : I → Word) :
    (Number.power n k).value a = (n.value a) ^ k := by
  induction k <;> simp_all [power, Number.constant, Number.mul, pow_succ]

def Number.sum : List (Number I) → Number I
  | [] => .constant 0
  | n :: ns => n.add (Number.sum ns)

lemma Number.sum_value (ns : List (Number I)) (a : I → Word) :
    (Number.sum ns).value a = (ns.map (fun n => n.value a)).sum := by
  induction ns <;> simp_all [sum, Number.constant, Number.add]

noncomputable def Number.polynomial (p : Polynomial ℕ) (n : Number I) : Number I :=
  Number.sum (p.support.toList.map (fun k => (Number.constant (p.coeff k)).mul (n.power k)))

lemma Number.polynomial_value (p : Polynomial ℕ) (n : Number I) (a : I → Word) :
    (Number.polynomial p n).value a = p.eval (n.value a) := by
  simp [polynomial, Number.sum_value, List.map_map, Function.comp_def, Number.mul,
    Number.constant, Number.power_value, Polynomial.eval_eq_sum, Polynomial.sum]

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
