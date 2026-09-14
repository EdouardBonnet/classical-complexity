import Lax434930Proofs.CertificateProjection
import Lax434930Proofs.Certificates
import Lax434930Proofs.SavitchProofs.PolynomialConstructor

namespace Lax434930Proofs.InclusionAux.CertificateBudget

open Lax434930.PolynomialTime Lax434930.Certificates
open Lax434930Proofs Lax434930Proofs.SavitchProofs

lemma first_length (xs : Word) : 2 * (CertificateProjection.first xs).length ≤ xs.length := by
  fun_induction CertificateProjection.first xs <;> simp_all [CertificateProjection.first] <;> omega

lemma first_bounded (p : ℕ) (xs : Word) (h : xs.length = 2 * p + 1) :
    (CertificateProjection.first xs).length ≤ p := by
  have := first_length xs
  omega

def padded (p : ℕ) (ys : Word) : Word := pair ys (List.replicate (2 * (p - ys.length)) false)

lemma padded_length (p : ℕ) (ys : Word) (hy : ys.length ≤ p) :
    (padded p ys).length = 2 * p + 1 := by
  rw [padded, Certificates.pair_length]
  simp only [List.length_replicate]
  omega

lemma first_padded (p : ℕ) (ys : Word) : CertificateProjection.first (padded p ys) = ys :=
  CertificateProjection.first_pair _ _

open StackLanguage UnaryPolynomial

noncomputable def code (p : Polynomial ℕ) : UnaryPolynomial.Code p.natDegree :=
  .seq (countCode p.natDegree) (polynomialCode p)

noncomputable def result (p : Polynomial ℕ) (w : Word) : UnaryPolynomial.Data p.natDegree :=
  grown (countResult p.natDegree w) (p.eval w.length)

lemma execution (p : Polynomial ℕ) (w : Word) (bound : ℕ)
    (hn : w.length < bound) (hp : p.eval w.length < bound) :
    Exec w bound (code p) ⟨initial p.natDegree, 0, fun _ => []⟩ (result p w) := by
  have hc := count_exec p.natDegree w bound hn
  have he := polynomial_exec p w.length w bound (countResult p.natDegree w) hc.good.2
    (by simp [countResult]) (by simp [countResult]) (by intro k; simp [countResult])
    (by simpa [countResult] using hp)
  exact Exec.seq hc he

lemma result_output (p : Polynomial ℕ) (w : Word) :
    (result p w).store .output = List.replicate (p.eval w.length) () := by
  simp [result, grown, countResult]

end Lax434930Proofs.InclusionAux.CertificateBudget
