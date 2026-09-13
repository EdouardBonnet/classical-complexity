import Lax434930Proofs.SavitchProofs.QueryRegisters

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.GraphQuery

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open ConfigurationWords
open StackLanguage (Good Exec assigned pushed)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine) (BΓ : Type)

def decoderStep (s : User M) (g : Alphabet M BΓ) : User M × Option (Alphabet M BΓ) :=
  let t := BitDecoder.step (Payload M) s.query.buffer (SearchProgram.readBit g)
  (setBuffer s t.1, t.2.map letter)

lemma decoder_run (s : User M) (xs : List Bool) :
    StackTransducer.run (decoderStep M BΓ) s (xs.map SearchProgram.bit) =
      (setBuffer s (StackTransducer.run (BitDecoder.step (Payload M)) s.query.buffer xs).1,
        (StackTransducer.run (BitDecoder.step (Payload M)) s.query.buffer xs).2.map letter) := by
  have h := StackTransducer.run_map (BitDecoder.step (Payload M)) (decoderStep M BΓ)
    (setBuffer s) SearchProgram.bit letter (by intros; simp [decoderStep, setBuffer]) s.query.buffer xs
  simpa [setBuffer] using h

def decodeCode (src aux : Key) : GraphQuery.Macro M BΓ :=
  Macro.seq (Macro.assign fun s => {s with user := setBuffer s.user (BitDecoder.empty _)})
    (Macro.seq (StackTransducer.asMacro src aux (decoderStep M BΓ))
      (Macro.seq (Macro.branch (fun s => decide (s.user.query.buffer.val ≠ []))
        (Macro.push aux (fun s => letter (FiniteCoding.decodeBlock (Payload M) s.user.query.buffer.val))) Macro.skip)
        (Macro.transfer aux src)))

lemma decodeCode_guard (w : Word) (bound : ℕ) (src aux : Key) (hne : src ≠ aux)
    (d : Data M BΓ) (xs : List Bool) (hsrc : d.store src = xs.map SearchProgram.bit)
    (haux : d.store aux = []) (hb : xs.length + 1 < bound) :
    (decodeCode M BΓ src aux).guard w bound d := by
  have hlen := StackTransducer.output_length (BitDecoder.step (Payload M)) (BitDecoder.empty _) xs
  simp only [decodeCode, Macro.seq, Macro.assign, StackTransducer.asMacro, Macro.branch,
    Macro.push, Macro.skip, Macro.transfer, assigned, StackTransducer.result, hsrc, haux, decoder_run, setBuffer]
  by_cases hbuf : (StackTransducer.run (BitDecoder.step (Payload M)) (BitDecoder.empty _) xs).1.val = []
  · simp [hbuf, hne, Ne.symm hne, setBuffer, StackRoutines.transferred]
    omega
  · simp [hbuf, hne, Ne.symm hne, setBuffer, pushed, StackRoutines.transferred]
    omega

lemma decodeCode_result (w : Word) (src aux : Key) (hne : src ≠ aux)
    (d : Data M BΓ) (xs : List Bool) (hsrc : d.store src = xs.map SearchProgram.bit)
    (haux : d.store aux = []) :
    (decodeCode M BΓ src aux).result w d =
      ⟨{d.state with
          user := setBuffer d.state.user (StackTransducer.run (BitDecoder.step (Payload M)) (BitDecoder.empty _) xs).1
          value := none
          other := none}, d.inputHead,
        Function.update d.store src ((FiniteCoding.decodeWord (Payload M) xs).map letter)⟩ := by
  rw [← BitDecoder.decode_correct]
  simp only [decodeCode, Macro.seq, Macro.assign, StackTransducer.asMacro, Macro.branch,
    Macro.push, Macro.skip, Macro.transfer, assigned, StackTransducer.result, hsrc, haux, decoder_run, setBuffer]
  by_cases hbuf : (StackTransducer.run (BitDecoder.step (Payload M)) (BitDecoder.empty _) xs).1.val = []
  all_goals
    simp [hbuf, hne, Ne.symm hne, setBuffer, pushed, StackRoutines.transferred,
      BitDecoder.decode, BitDecoder.flush, List.map_reverse, List.map_append]
    funext k
    by_cases hs : k = src <;> by_cases ha : k = aux <;>
      simp_all [Function.update_apply]

end

end Lax434930Proofs.SavitchProofs.GraphQuery
