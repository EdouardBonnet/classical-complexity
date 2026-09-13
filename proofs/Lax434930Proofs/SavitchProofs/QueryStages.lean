import Lax434930Proofs.SavitchProofs.DecodeQuery
import Lax434930Proofs.SavitchProofs.ParseQuery
import Lax434930Proofs.SavitchProofs.AutomatonQuery

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.GraphQuery

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open ConfigurationWords
open StackLanguage (Good Exec assigned)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine) (BΓ : Type)

def copyDecode (src : SearchProgram.Register) (dst : Scratch) : GraphQuery.Macro M BΓ :=
  Macro.seq (Macro.copy (SearchProgram.key src) (key dst) (key .aux)) (decodeCode M BΓ (key dst) (key .reverse))

lemma copyDecode_guard (w : Word) (bound : ℕ) (src : SearchProgram.Register) (dst : Scratch)
    (ha : dst ≠ .aux) (hr : dst ≠ .reverse) (d : Data M BΓ) (xs : List Bool)
    (hsrc : d.store (SearchProgram.key src) = xs.map SearchProgram.bit)
    (haux : d.store (key .aux) = []) (hrev : d.store (key .reverse) = []) (hb : xs.length + 1 < bound) :
    (copyDecode M BΓ src dst).guard w bound d := by
  dsimp only [key] at haux hrev
  refine ⟨by simp [Macro.copy, key, SearchProgram.key, ha, haux], ?_⟩
  apply decodeCode_guard M BΓ w bound (key dst) (key .reverse) (by simpa [key] using hr) _ xs
  · simp [Macro.copy, hsrc]
  · simp [Macro.copy, key, Ne.symm hr, hrev]
  · exact hb

lemma copyDecode_result (w : Word) (src : SearchProgram.Register) (dst : Scratch) (hr : dst ≠ .reverse)
    (d : Data M BΓ) (xs : List Bool) (hsrc : d.store (SearchProgram.key src) = xs.map SearchProgram.bit)
    (hrev : d.store (key .reverse) = []) :
    (copyDecode M BΓ src dst).result w d =
      ⟨{d.state with
          user := setBuffer d.state.user (StackTransducer.run (BitDecoder.step (Payload M)) (BitDecoder.empty _) xs).1
          value := none
          other := none}, d.inputHead,
        Function.update d.store (key dst) ((FiniteCoding.decodeWord (Payload M) xs).map letter)⟩ := by
  dsimp only [key] at hrev
  change (decodeCode M BΓ (key dst) (key .reverse)).result w _ = _
  rw [decodeCode_result M BΓ w (key dst) (key .reverse) (by simpa [key] using hr) _ xs
    (by simp [Macro.copy, hsrc]) (by simp [Macro.copy, key, Ne.symm hr, hrev])]
  simp [Macro.copy]
  funext k
  by_cases hk : k = key dst <;> simp [Function.update_apply, hk]

def checkWord (src : Scratch) : GraphQuery.Macro M BΓ :=
  Macro.seq (Macro.copy (key src) (key .temporary) (key .aux))
    (Macro.seq (parseCode M BΓ (key .temporary) (key .reverse))
      (Macro.seq (inputCheck M BΓ (key .temporary) (key .aux))
        (Macro.assign (fun s => {s with user := {s.user with answer := s.user.answer && s.flag}}))))

def parsedWord (d : Data M BΓ) (xs : List (Letter M)) : Data M BΓ :=
  ⟨{d.state with
      user := setParser d.state.user (StackTransducer.run (InputParser.step M) InputParser.start xs).1
      value := none
      other := none}, d.inputHead,
    Function.update d.store (key .temporary) ((inputBits M xs).map SearchProgram.bit)⟩

lemma checkWord_prefix (w : Word) (src : Scratch) (d : Data M BΓ) (xs : List (Letter M))
    (hsrc : d.store (key src) = xs.map letter) (hrev : d.store (key .reverse) = []) :
    (parseCode M BΓ (key .temporary) (key .reverse)).result w
      ((Macro.copy (key src) (key .temporary) (key .aux)).result w d) = parsedWord M BΓ d xs := by
  dsimp only [key] at hrev
  rw [parseCode_result M BΓ w _ _ (by simp [key]) _ xs
    (by simp [Macro.copy, hsrc]) (by simp [Macro.copy, key, hrev])]
  simp [parsedWord, Macro.copy]
  funext k
  by_cases hk : k = key .temporary <;> simp [Function.update_apply, hk]

lemma checkWord_guard (w : Word) (bound : ℕ) (src : Scratch)
    (ht : src ≠ .temporary) (ha : src ≠ .aux) (d : Data M BΓ) (xs : List (Letter M))
    (hsrc : d.store (key src) = xs.map letter) (haux : d.store (key .aux) = [])
    (hrev : d.store (key .reverse) = []) (hb : xs.length < bound) :
    (checkWord M BΓ src).guard w bound d := by
  dsimp only [key] at haux hrev
  change _ ∧ _ ∧ _ ∧ True
  refine ⟨by simp [Macro.copy, key, ht, ha, haux], ?_, ?_, trivial⟩
  · apply parseCode_guard M BΓ w bound _ _ (by simp [key]) _ xs
    · simp [Macro.copy, hsrc]
    · simp [Macro.copy, key, hrev]
    · exact hb
  · rw [checkWord_prefix M BΓ w src d xs hsrc hrev]
    apply inputCheck_guard M BΓ w bound _ _ (by simp [key]) _ (inputBits M xs)
    · simp [parsedWord]
    · simp [parsedWord, key, haux]

lemma checkWord_result (w : Word) (src : Scratch) (d : Data M BΓ) (xs : List (Letter M))
    (hsrc : d.store (key src) = xs.map letter) (hrev : d.store (key .reverse) = []) :
    let e := (checkWord M BΓ src).result w d
    e.state.user.phase = d.state.user.phase ∧
      e.state.user.answer = (d.state.user.answer && decide (ValidInput M w xs)) ∧
      (∀ k, k ≠ key .temporary → e.store k = d.store k) := by
  let dp := parsedWord M BΓ d xs
  let de := (inputCheck M BΓ (key .temporary) (key .aux)).result w dp
  have hu : de.state.user = dp.state.user := inputCheck_user M BΓ w _ _ dp
  have hf : de.state.flag = decide (ValidInput M w xs) := by
    apply Bool.eq_iff_iff.mpr
    rw [inputCheck_result M BΓ w _ _ dp (inputBits M xs) (by simp [dp, parsedWord])]
    simp [dp, parsedWord, setParser, (InputParser.run_correct M xs).1, ValidInput]
  have hs : ∀ k, k ≠ key .temporary → de.store k = d.store k := by
    intro k hk
    rw [inputCheck_store M BΓ w _ _ dp k hk]
    simp [dp, parsedWord, hk]
  have he : (checkWord M BΓ src).result w d =
      assigned de {de.state with user := {de.state.user with answer := de.state.user.answer && de.state.flag}} := by
    dsimp only [checkWord, Macro.seq, Macro.assign]
    rw [checkWord_prefix M BΓ w src d xs hsrc hrev]
  dsimp only
  rw [he]
  refine ⟨?_, ?_, hs⟩
  · simp [assigned, hu, dp, parsedWord, setParser]
  · simp [assigned, hu, hf, dp, parsedWord, setParser]

end

end Lax434930Proofs.SavitchProofs.GraphQuery
