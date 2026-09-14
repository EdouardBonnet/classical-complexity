import Lax434930Proofs.InclusionAux.CertificateMachine

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.CertificateMachine

open Turing Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs Lax434930Proofs.SavitchProofs
open StackLanguage (Exec Good assigned)
open scoped Classical

noncomputable section

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {f : Word → Bool} (M : TM2ComputableInPolyTime id Computability.encodeBool f)

def parserTransition : User M → Alphabet M → User M × Option (Alphabet M) :=
  FirstDecoder.lifted (parserState M) (readParser M)
    (VerifierRoutine.inputSymbol M) (VerifierRoutine.inputRead M)

def parserStart (s : State M) : State M := {s with user := parserState M .tag}

def started (p : Polynomial ℕ) (w xs : Word) : Data M p :=
  assigned (guessed M p w xs) (parserStart M (guessed M p w xs).state)

def parsed (p : Polynomial ℕ) (w xs : Word) : Data M p :=
  StackTransducer.result (started M p w xs) (guess M p) (temporary M p) (parserTransition M)

def decoded (p : Polynomial ℕ) (w xs : Word) : Data M p :=
  StackRoutines.transferred (parsed M p w xs) (temporary M p) (input M p)

def prepared (p : Polynomial ℕ) (w xs : Word) : Data M p :=
  InputPairBuilder.paired (input M p) (VerifierRoutine.inputSymbol M) w (decoded M p w xs)

def prepareCode (p : Polynomial ℕ) : Code M p :=
  .seq (.assign (parserStart M))
    (.seq (StackTransducer.code (guess M p) (temporary M p) (parserTransition M))
      (.seq (StackRoutines.transfer (temporary M p) (input M p))
        (InputPairBuilder.code (input M p) (VerifierRoutine.inputSymbol M))))

@[simp] lemma parsed_temporary (p : Polynomial ℕ) (w xs : Word) :
    (parsed M p w xs).store (temporary M p) =
      (CertificateProjection.first xs.reverse).reverse.map (VerifierRoutine.inputSymbol M) := by
  have h := FirstDecoder.result_output (parserState M) (readParser M)
    (VerifierRoutine.inputSymbol M) (VerifierRoutine.inputRead M)
    (read_parser M) (VerifierRoutine.input_read M) (guess M p) (temporary M p) xs.reverse
    (started M p w xs) rfl (by simp [started, assigned])
  simpa [parsed, parserTransition, started, assigned] using h

@[simp] lemma parsed_verifier (p : Polynomial ℕ) (w xs : Word) (k : M.tm.K) :
    (parsed M p w xs).store ((verifierKeys M p).key k) = [] := by
  simp [parsed, StackTransducer.result, started, assigned, verifierKeys, temporary, guess,
    guessed, ChoiceProofs.GuessWord.result, supply]

@[simp] lemma decoded_input (p : Polynomial ℕ) (w xs : Word) :
    (decoded M p w xs).store (input M p) =
      (CertificateProjection.first xs.reverse).map (VerifierRoutine.inputSymbol M) := by
  simp [decoded, StackRoutines.transferred, input]

lemma decoded_verifier_other (p : Polynomial ℕ) (w xs : Word) (k : M.tm.K)
    (hk : k ≠ M.tm.k₀) : (decoded M p w xs).store ((verifierKeys M p).key k) = [] := by
  simp [decoded, StackRoutines.transferred, verifierKeys, temporary, input, hk,
    parsed, StackTransducer.result, started, assigned, guess, guessed,
    ChoiceProofs.GuessWord.result, supply]

@[simp] lemma decoded_head (p : Polynomial ℕ) (w xs : Word) :
    (decoded M p w xs).inputHead = w.length + 1 := rfl

@[simp] lemma prepared_head (p : Polynomial ℕ) (w xs : Word) :
    (prepared M p w xs).inputHead = 0 := rfl

lemma prepared_verifier (p : Polynomial ℕ) (w xs : Word) (k : M.tm.K) :
    (prepared M p w xs).store ((verifierKeys M p).key k) =
      (VerifierRoutine.initial M (Lax434930.Certificates.pair w
        (CertificateProjection.first xs.reverse))).stk k := by
  rw [VerifierRoutine.initial_stack]
  by_cases hk : k = M.tm.k₀
  · subst k
    change (prepared M p w xs).store (input M p) = _
    simp [prepared, InputPairBuilder.paired, InputPairBuilder.prefix_pair]
  · simpa [prepared, InputPairBuilder.paired, input, verifierKeys, hk] using
      decoded_verifier_other M p w xs k hk

lemma first_le (xs : Word) : (CertificateProjection.first xs.reverse).length ≤ xs.length := by
  have h := CertificateBudget.first_length xs.reverse
  simp only [List.length_reverse] at h
  omega

lemma prepare_execution (p : Polynomial ℕ) (w xs : Word) (bound : ℕ)
    (hd : Good w bound (guessed M p w xs))
    (hb : 2 * w.length + 1 + xs.length < bound) :
    Exec w bound (prepareCode M p) (guessed M p w xs) (prepared M p w xs) := by
  have hstart : Exec w bound (.assign (parserStart M)) (guessed M p w xs) (started M p w xs) :=
    .assign _ _ hd
  have hparse := StackTransducer.code_exec w bound (guess M p) (temporary M p)
    (by simp [guess, temporary]) (parserTransition M) (started M p w xs) hstart.good.2
    (by simp [started, assigned]; omega)
  have htrans := StackRoutines.transfer_exec w bound (temporary M p) (input M p)
    (by simp [temporary, input, verifierKeys]) (parsed M p w xs) hparse.good.2
    (by simp [input]; have h := first_le xs; omega)
  have hpair := InputPairBuilder.execution (input M p) (VerifierRoutine.inputSymbol M)
    w bound (decoded M p w xs) htrans.good.2 (decoded_head M p w xs)
    (by rw [decoded_input, List.length_map]; exact (Nat.add_le_add_left (first_le xs) _).trans_lt hb)
  exact .seq hstart (.seq hparse (.seq htrans hpair))

end

end Lax434930Proofs.InclusionAux.CertificateMachine
