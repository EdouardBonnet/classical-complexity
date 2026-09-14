import Lax434930Proofs.InclusionAux.CertificatePreparation
import Lax434930Proofs.PolynomialComposition

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.CertificateMachine

open Turing Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs Lax434930Proofs.SavitchProofs
open StackLanguage (Exec Good assigned popped)
open scoped Classical

noncomputable section

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {f : Word → Bool} (M : TM2ComputableInPolyTime id Computability.encodeBool f)

def verifierInput (w xs : Word) : Word :=
  Lax434930.Certificates.pair w (CertificateProjection.first xs.reverse)

def answerStep (s : State M) (value : Option (Alphabet M)) : State M :=
  {s with flag := (value.map (VerifierRoutine.outputRead M)).getD false}

def finishCode (p : Polynomial ℕ) : Code M p :=
  .seq (prepareCode M p)
    (.seq (.assign (fun _ => verifierState M (VerifierRoutine.initialControl M)))
      (.seq (VerifierRoutine.code M (verifierKeys M p) (verifierState M) (readVerifier M))
        (.pop (fun _ => output M p) (answerStep M))))

lemma finish_execution (p : Polynomial ℕ) (w xs : Word) (bound : ℕ)
    (hd : Good w bound (guessed M p w xs))
    (hb : 2 * w.length + 1 + xs.length < bound)
    (ht : (verifierInput w xs).length +
      TM2Bounds.factor M.tm * M.time.eval (verifierInput w xs).length < bound) :
    ∃ e, Exec w bound (finishCode M p) (guessed M p w xs) e ∧
      e.state.flag = f (verifierInput w xs) := by
  have hp := prepare_execution M p w xs bound hd hb
  have hi := Exec.assign (prepared M p w xs)
    (fun _ => verifierState M (VerifierRoutine.initialControl M)) hp.good.2
  have he := VerifierRoutine.point_initial M (verifierKeys M p) (verifierState M)
    (verifierInput w xs) (prepared M p w xs) (prepared_verifier M p w xs)
  have hr := VerifierRoutine.execution M (verifierKeys M p) (verifierState M)
    (readVerifier M) (read_verifier M) (prepared M p w xs).store w (verifierInput w xs)
    bound 0 (by omega) (fun j _ => hp.good.2.2 j) ht
  rw [prepared_head] at he
  rw [he] at hr
  let d := VerifierRoutine.point M (verifierKeys M p) (verifierState M)
    (prepared M p w xs).store (VerifierRoutine.finalCfg M (f (verifierInput w xs))) 0
  have ha := Exec.pop d (fun _ => output M p) (answerStep M) hr.good.2
  refine ⟨_, .seq hp (.seq hi (.seq hr ha)), ?_⟩
  simp [popped, answerStep, d, output, VerifierRoutine.point_output]

def pairedBound (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 1 + width p

def spaceBound (p : Polynomial ℕ) : Polynomial ℕ :=
  pairedBound p + Polynomial.C (TM2Bounds.factor M.tm) * M.time.comp (pairedBound p) + Polynomial.C 1

@[simp] lemma pairedBound_eval (p : Polynomial ℕ) (n : ℕ) :
    (pairedBound p).eval n = 2 * n + 1 + (width p).eval n := by
  simp [pairedBound]

@[simp] lemma spaceBound_eval (p : Polynomial ℕ) (n : ℕ) :
    (spaceBound M p).eval n = (pairedBound p).eval n +
      TM2Bounds.factor M.tm * M.time.eval ((pairedBound p).eval n) + 1 := by
  simp [spaceBound, Polynomial.eval_comp]

lemma spaceBound_pos (p : Polynomial ℕ) (n : ℕ) : 0 < (spaceBound M p).eval n := by
  rw [spaceBound_eval]
  omega

lemma input_lt_bound (p : Polynomial ℕ) (n : ℕ) : n < (spaceBound M p).eval n := by
  rw [spaceBound_eval, pairedBound_eval]
  omega

lemma width_lt_bound (p : Polynomial ℕ) (n : ℕ) :
    (width p).eval n < (spaceBound M p).eval n := by
  rw [spaceBound_eval, pairedBound_eval]
  omega

lemma preparation_lt_bound (p : Polynomial ℕ) (n : ℕ) :
    2 * n + 1 + (width p).eval n < (spaceBound M p).eval n := by
  rw [spaceBound_eval, pairedBound_eval]
  omega

lemma verifier_length (p : Polynomial ℕ) (w xs : Word)
    (hx : xs.length = (width p).eval w.length) :
    (verifierInput w xs).length ≤ (pairedBound p).eval w.length := by
  rw [verifierInput, Certificates.pair_length, pairedBound_eval]
  have h := first_le xs
  omega

lemma verifier_lt_bound (p : Polynomial ℕ) (w xs : Word)
    (hx : xs.length = (width p).eval w.length) :
    (verifierInput w xs).length + TM2Bounds.factor M.tm * M.time.eval (verifierInput w xs).length <
      (spaceBound M p).eval w.length := by
  have hl := verifier_length p w xs hx
  have ht := PolynomialComposition.eval_mono M.time hl
  have hb := Nat.add_le_add hl (Nat.mul_le_mul_left (TM2Bounds.factor M.tm) ht)
  rw [spaceBound_eval]
  omega

end

end Lax434930Proofs.InclusionAux.CertificateMachine
