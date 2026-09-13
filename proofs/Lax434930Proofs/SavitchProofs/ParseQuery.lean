import Lax434930Proofs.SavitchProofs.QueryRegisters
import Lax434930Proofs.SavitchProofs.InputVisit

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.GraphQuery

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open ConfigurationWords
open StackLanguage (Good Exec assigned)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine) (BΓ : Type)

def parserStep (s : User M) (g : Alphabet M BΓ) : User M × Option (Alphabet M BΓ) :=
  let t := InputParser.step M s.query.parser (readLetter g)
  (setParser s t.1, t.2.map SearchProgram.bit)

lemma parser_run (s : User M) (xs : List (Letter M)) :
    StackTransducer.run (parserStep M BΓ) s (xs.map letter) =
      (setParser s (StackTransducer.run (InputParser.step M) s.query.parser xs).1,
        (StackTransducer.run (InputParser.step M) s.query.parser xs).2.map SearchProgram.bit) := by
  have h := StackTransducer.run_map (InputParser.step M) (parserStep M BΓ)
    (setParser s) letter SearchProgram.bit (by intros; simp [parserStep, setParser]) s.query.parser xs
  simpa [setParser] using h

def parseCode (src aux : Key) : GraphQuery.Macro M BΓ :=
  Macro.seq (Macro.assign fun s => {s with user := setParser s.user InputParser.start})
    (Macro.seq (StackTransducer.asMacro src aux (parserStep M BΓ)) (Macro.transfer aux src))

lemma parseCode_guard (w : Word) (bound : ℕ) (src aux : Key) (hne : src ≠ aux)
    (d : Data M BΓ) (xs : List (Letter M)) (hsrc : d.store src = xs.map letter)
    (haux : d.store aux = []) (hb : xs.length < bound) :
    (parseCode M BΓ src aux).guard w bound d := by
  have hlen := StackTransducer.output_length (InputParser.step M) InputParser.start xs
  simp only [parseCode, Macro.seq, Macro.assign, StackTransducer.asMacro, Macro.transfer,
    assigned, StackTransducer.result, hsrc, haux, parser_run, setParser]
  simp [hne, Ne.symm hne]
  omega

lemma parseCode_result (w : Word) (src aux : Key) (hne : src ≠ aux)
    (d : Data M BΓ) (xs : List (Letter M)) (hsrc : d.store src = xs.map letter)
    (haux : d.store aux = []) :
    (parseCode M BΓ src aux).result w d =
      ⟨{d.state with
          user := setParser d.state.user (StackTransducer.run (InputParser.step M) InputParser.start xs).1
          value := none
          other := none}, d.inputHead,
        Function.update d.store src ((inputBits M xs).map SearchProgram.bit)⟩ := by
  simp only [parseCode, Macro.seq, Macro.assign, StackTransducer.asMacro, Macro.transfer,
    assigned, StackTransducer.result, hsrc, haux, parser_run, setParser]
  simp [hne, Ne.symm hne, StackRoutines.transferred, List.map_reverse, (InputParser.run_correct M xs).2]
  funext k
  by_cases hs : k = src <;> by_cases ha : k = aux <;> simp_all [Function.update_apply]

def inputCheck (src aux : Key) : GraphQuery.Macro M BΓ :=
  InputRoutines.positionCheck src aux SearchProgram.bit SearchProgram.readBit (fun s => s.query.parser.desired)

lemma inputCheck_guard (w : Word) (bound : ℕ) (src aux : Key) (hne : src ≠ aux)
    (d : Data M BΓ) (xs : List Bool) (hsrc : d.store src = xs.map SearchProgram.bit) (haux : d.store aux = []) :
    (inputCheck M BΓ src aux).guard w bound d := by
  apply InputRoutines.positionCheck_guard w bound src aux hne _ _ SearchProgram.readBit_bit _ d haux
  simp [hsrc, List.map_map, Function.comp_def]

lemma inputCheck_result (w : Word) (src aux : Key) (d : Data M BΓ) (xs : List Bool)
    (hsrc : d.store src = xs.map SearchProgram.bit) :
    ((inputCheck M BΓ src aux).result w d).state.flag = true ↔
      BinaryCounter.value xs ≤ w.length + 1 ∧
        readInput w (BinaryCounter.value xs) = d.state.user.query.parser.desired := by
  rw [inputCheck, InputRoutines.positionCheck_result, hsrc]
  simp [List.map_map, Function.comp_def]

lemma inputCheck_user (w : Word) (src aux : Key) (d : Data M BΓ) :
    ((inputCheck M BΓ src aux).result w d).state.user = d.state.user := by
  simp [inputCheck, InputRoutines.positionCheck, InputRoutines.visit, InputRoutines.visitFrom,
    InputRoutines.rewind, InputRoutines.rewound, InputRoutines.visited, Macro.seq, Macro.assign, assigned]

lemma inputCheck_store (w : Word) (src aux : Key) (d : Data M BΓ) (k : Key) (hne : k ≠ src) :
    ((inputCheck M BΓ src aux).result w d).store k = d.store k := by
  simp [inputCheck, InputRoutines.positionCheck, InputRoutines.visit, InputRoutines.visitFrom,
    InputRoutines.rewind, InputRoutines.rewound, InputRoutines.visited, Macro.seq, Macro.assign, assigned, hne]

end

end Lax434930Proofs.SavitchProofs.GraphQuery
