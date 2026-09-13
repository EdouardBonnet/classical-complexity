import Lax434930Proofs.SavitchProofs.QueryRegisters

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.GraphQuery

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open ConfigurationWords
open StackLanguage (Good Exec assigned)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine) (BΓ : Type)

def automatonStep (s : Context M BΓ) : Context M BΓ :=
  {s with user := setAutomaton s.user ((PatternAutomata.machine (graphPatterns M)).step s.user.query.automaton
    (readLetter (s.value.getD default), readLetter (s.other.getD default)))}

lemma automaton_fold (s : Context M BΓ) (xs ys : List (Letter M)) (hlen : xs.length = ys.length) :
    StackRoutines.pairFold (automatonStep M BΓ) (xs.map letter) (ys.map letter) s =
      {s with
        user := setAutomaton s.user ((PatternAutomata.machine (graphPatterns M)).evalFrom s.user.query.automaton (List.zip xs ys))
        value := none
        other := none} := by
  induction xs generalizing ys s with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    simp [hy, StackRoutines.pairFold, StackRoutines.withPair, DFA.evalFrom, setAutomaton]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hh : xs.length = ys.length := by simpa using hlen
      simp [StackRoutines.pairFold, ih _ _ hh, StackRoutines.withPair, automatonStep,
        DFA.evalFrom_cons, setAutomaton]

def automatonCode (src dst : Key) : GraphQuery.Macro M BΓ :=
  Macro.seq (Macro.assign fun s => {s with user := setAutomaton s.user (PatternAutomata.machine (graphPatterns M)).start})
    (Macro.seq (Macro.scanPairs src dst (automatonStep M BΓ))
      (Macro.assign fun s => {s with user := {s.user with
        answer := s.user.answer && decide (s.user.query.automaton ∈ (PatternAutomata.machine (graphPatterns M)).accept)}}))

lemma automatonCode_guard (w : Word) (bound : ℕ) (src dst : Key) (hne : src ≠ dst) (d : Data M BΓ) :
    (automatonCode M BΓ src dst).guard w bound d := by
  simp [automatonCode, Macro.seq, Macro.assign, Macro.scanPairs, hne]

lemma automatonCode_result (w : Word) (src dst : Key) (d : Data M BΓ) (xs ys : List (Letter M))
    (hsrc : d.store src = xs.map letter) (hdst : d.store dst = ys.map letter) (hlen : xs.length = ys.length) :
    (automatonCode M BΓ src dst).result w d =
      ⟨{d.state with
          user := {setAutomaton d.state.user ((PatternAutomata.machine (graphPatterns M)).eval (List.zip xs ys)) with
            answer := d.state.user.answer && decide (List.zip xs ys ∈ (PatternAutomata.machine (graphPatterns M)).accepts)}
          value := none
          other := none}, d.inputHead,
        Function.update (Function.update d.store src []) dst []⟩ := by
  simp [automatonCode, Macro.seq, Macro.assign, Macro.scanPairs, StackRoutines.scannedPairs,
    assigned, hsrc, hdst, automaton_fold M BΓ _ xs ys hlen, setAutomaton, DFA.mem_accepts, DFA.eval]
  funext k
  by_cases hs : k = src <;> by_cases ht : k = dst <;> simp_all [Function.update_apply]

end

end Lax434930Proofs.SavitchProofs.GraphQuery
