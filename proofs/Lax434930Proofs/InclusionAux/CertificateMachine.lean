import Lax434930Proofs.InclusionAux.VerifierRoutine
import Lax434930Proofs.InclusionAux.FirstDecoder
import Lax434930Proofs.InclusionAux.InputPairBuilder
import Lax434930Proofs.InclusionAux.ChoiceProofs.GuessWordCorrectness

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.CertificateMachine

open Turing Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs Lax434930Proofs.SavitchProofs
open StackLanguage (Exec Good assigned)
open scoped Classical

noncomputable section

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {f : Word → Bool} (M : TM2ComputableInPolyTime id Computability.encodeBool f)

def width (p : Polynomial ℕ) : Polynomial ℕ := Polynomial.C 2 * p + Polynomial.C 1

@[simp] lemma width_eval (p : Polynomial ℕ) (n : ℕ) : (width p).eval n = 2 * p.eval n + 1 := by
  simp [width]

abbrev Alphabet := VerifierRoutine.Alphabet M
abbrev ConstructorState := StackRoutines.Control Unit Unit
abbrev User := ConstructorState ⊕ (VerifierRoutine.Control M ⊕ FirstDecoder.State)
abbrev State := StackRoutines.Control (Alphabet M) (User M)
abbrev Key (p : Polynomial ℕ) := UnaryPolynomial.Register (width p).natDegree ⊕ (M.tm.K ⊕ Fin 2)
abbrev Data (p : Polynomial ℕ) := StackRoutines.Data (K := Key M p) (Γ := Alphabet M) (σ := User M)
abbrev Code (p : Polynomial ℕ) := StackRoutines.Code (K := Key M p) (Γ := Alphabet M) (σ := User M)

def constructorKeys (p : Polynomial ℕ) : CommandEmbedding.KeyMap (UnaryPolynomial.Register (width p).natDegree) (Key M p) where
  key := Sum.inl
  read := fun j => match j with | .inl k => some k | .inr _ => none
  read_key _ := rfl
  key_read j k h := by cases j <;> simp_all

def verifierKeys (p : Polynomial ℕ) : CommandEmbedding.KeyMap M.tm.K (Key M p) where
  key k := .inr (.inl k)
  read := fun j => match j with | .inr (.inl k) => some k | _ => none
  read_key _ := rfl
  key_read j k h := by cases j with
    | inl j => simp at h
    | inr j => cases j <;> simp_all

def supply (p : Polynomial ℕ) : Key M p := .inl .output
def guess (p : Polynomial ℕ) : Key M p := .inr (.inr 0)
def temporary (p : Polynomial ℕ) : Key M p := .inr (.inr 1)
def input (p : Polynomial ℕ) : Key M p := (verifierKeys M p).key M.tm.k₀
def output (p : Polynomial ℕ) : Key M p := (verifierKeys M p).key M.tm.k₁

def constructorState (s : ConstructorState) : State M := ⟨.inl s, none, false, .leftEnd, none⟩
def readConstructor (s : State M) : ConstructorState :=
  match s.user with | .inl s => s | _ => UnaryPolynomial.initial 0

def verifierState (s : VerifierRoutine.Control M) : State M := ⟨.inr (.inl s), none, false, .leftEnd, none⟩
def readVerifier (s : State M) : VerifierRoutine.Control M :=
  match s.user with | .inr (.inl s) => s | _ => ⟨none, M.tm.initialState, none⟩

def parserState (s : FirstDecoder.State) : User M := .inr (.inr s)
def readParser (s : User M) : FirstDecoder.State :=
  match s with | .inr (.inr s) => s | _ => .tag

@[simp] lemma read_constructor (s : ConstructorState) : readConstructor M (constructorState M s) = s := rfl
@[simp] lemma read_verifier (s : VerifierRoutine.Control M) : readVerifier M (verifierState M s) = s := rfl
@[simp] lemma read_parser (s : FirstDecoder.State) : readParser M (parserState M s) = s := rfl

def initial (p : Polynomial ℕ) : Data M p :=
  ⟨constructorState M (UnaryPolynomial.initial (width p).natDegree), 0, fun _ => []⟩

def constructorCode (p : Polynomial ℕ) : Code M p :=
  CommandEmbedding.command (constructorKeys M p) (fun _ : Unit => (none : Alphabet M)) (fun _ => ())
    (constructorState M) (readConstructor M) (CertificateBudget.code (width p))

def constructed (p : Polynomial ℕ) (w : Word) : Data M p :=
  CommandEmbedding.data (constructorKeys M p) (fun _ : Unit => (none : Alphabet M))
    (constructorState M) (fun _ => []) (CertificateBudget.result (width p) w)

lemma constructor_execution (p : Polynomial ℕ) (w : Word) (bound : ℕ)
    (hn : w.length < bound) (hp : (width p).eval w.length < bound) :
    Exec w bound (constructorCode M p) (initial M p) (constructed M p w) := by
  have he := CertificateBudget.execution (width p) w bound hn hp
  have h := CommandEmbedding.execution (constructorKeys M p) (fun _ : Unit => (none : Alphabet M))
    (fun _ => ()) (constructorState M) (readConstructor M) (by rintro ⟨⟩; rfl)
    (read_constructor M) (fun _ => []) w bound (by intro j hj; simpa using (show 0 < bound by omega)) he
  have hi : CommandEmbedding.data (constructorKeys M p) (fun _ : Unit => (none : Alphabet M))
      (constructorState M) (fun _ => [])
      ⟨UnaryPolynomial.initial (width p).natDegree, 0, fun _ => []⟩ = initial M p := by
    dsimp [CommandEmbedding.data, initial]
    congr 1
    funext j
    cases j <;> rfl
  exact hi ▸ h

@[simp] lemma constructed_supply (p : Polynomial ℕ) (w : Word) :
    (constructed M p w).store (supply M p) = List.replicate ((width p).eval w.length) none := by
  simp [constructed, CommandEmbedding.data, CommandEmbedding.store, constructorKeys, supply,
    CertificateBudget.result_output]

@[simp] lemma constructed_other (p : Polynomial ℕ) (w : Word) (j : M.tm.K ⊕ Fin 2) :
    (constructed M p w).store (.inr j) = [] := rfl

@[simp] lemma constructed_head (p : Polynomial ℕ) (w : Word) :
    (constructed M p w).inputHead = w.length + 1 := rfl

def guessed (p : Polynomial ℕ) (w xs : Word) : Data M p :=
  ChoiceProofs.GuessWord.result (constructed M p w) (supply M p) (guess M p) (VerifierRoutine.inputSymbol M) xs

@[simp] lemma guessed_store (p : Polynomial ℕ) (w xs : Word) :
    (guessed M p w xs).store (guess M p) = xs.reverse.map (VerifierRoutine.inputSymbol M) := by
  simp [guessed, ChoiceProofs.GuessWord.result, guess]

@[simp] lemma guessed_verifier (p : Polynomial ℕ) (w xs : Word) (k : M.tm.K) :
    (guessed M p w xs).store ((verifierKeys M p).key k) = [] := by
  simp [guessed, ChoiceProofs.GuessWord.result, verifierKeys, guess, supply]

@[simp] lemma guessed_temporary (p : Polynomial ℕ) (w xs : Word) :
    (guessed M p w xs).store (temporary M p) = [] := by
  simp [guessed, ChoiceProofs.GuessWord.result, temporary, guess, supply]

@[simp] lemma guessed_head (p : Polynomial ℕ) (w xs : Word) :
    (guessed M p w xs).inputHead = w.length + 1 := rfl

end

end Lax434930Proofs.InclusionAux.CertificateMachine
