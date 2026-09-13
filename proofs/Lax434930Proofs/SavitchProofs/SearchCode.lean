import Lax434930Proofs.SavitchProofs.SearchRegisters
import Lax434930Proofs.SavitchProofs.StackMacros

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.SearchProgram

open StackMacros
open scoped Classical

noncomputable section

variable {β ε δ : Type}

abbrev Routine (β ε δ : Type) := Macro (Key δ) (Alphabet β) (Control ε)

local infixr:60 " ⋙ₘ " => Macro.seq

def clearActive : Routine β ε δ :=
  Macro.clear (key .a) ⋙ₘ Macro.clear (key .b) ⋙ₘ
  Macro.clear (key .middle) ⋙ₘ Macro.clear (key .depth)

def saveFields : Routine β ε δ :=
  Macro.save (key .a) (key .frameA) (key .aux) (symbol .separator) ⋙ₘ
  Macro.save (key .b) (key .frameB) (key .aux) (symbol .separator) ⋙ₘ
  Macro.save (key .middle) (key .frameMiddle) (key .aux) (symbol .separator) ⋙ₘ
  Macro.save (key .depth) (key .frameDepth) (key .aux) (symbol .separator)

def restoreFields : Routine β ε δ :=
  Macro.restore (key .frameA) (key .a) (key .aux) (symbol .separator) ⋙ₘ
  Macro.restore (key .frameB) (key .b) (key .aux) (symbol .separator) ⋙ₘ
  Macro.restore (key .frameMiddle) (key .middle) (key .aux) (symbol .separator) ⋙ₘ
  Macro.restore (key .frameDepth) (key .depth) (key .aux) (symbol .separator)

def setPhase (p : Phase) : Routine β ε δ :=
  Macro.assign (fun s : Context β ε => {s with user := {s.user with phase := p}})

def returnValue (answer : Context β ε → Bool) : Routine β ε δ :=
  clearActive ⋙ₘ Macro.assign (fun s : Context β ε => {s with user := {s.user with phase := .ret, answer := answer s}})

def zeroMiddle : Routine β ε δ :=
  Macro.copyMap (key .width) (key .middle) (key .aux) (fun _ => bit false)

def nextMiddle : Routine β ε δ :=
  Macro.increment (key .middle) (key .aux) bit readBit ⋙ₘ
  Macro.assign (fun s : Context β ε => {s with user := {s.user with phase := .scan, overflow := s.flag}})

def descendLeft : Routine β ε δ :=
  saveFields ⋙ₘ Macro.push (key .kinds) (fun _ => symbol .leftTag) ⋙ₘ
  Macro.copy (key .middle) (key .b) (key .aux) ⋙ₘ Macro.clear (key .middle) ⋙ₘ setPhase .call

def descendRight : Routine β ε δ :=
  saveFields ⋙ₘ Macro.push (key .kinds) (fun _ => symbol .rightTag) ⋙ₘ
  Macro.copy (key .middle) (key .a) (key .aux) ⋙ₘ Macro.clear (key .middle) ⋙ₘ setPhase .call

def onCall (query : Routine β ε δ) : Routine β ε δ :=
  Macro.read (key .depth) ⋙ₘ Macro.branch (fun s => s.value.isSome)
    (zeroMiddle ⋙ₘ Macro.assign (fun s : Context β ε => {s with user := {s.user with phase := .scan, overflow := false}}))
    (query ⋙ₘ Macro.compare (key .a) (key .b) ⋙ₘ
      returnValue (fun s => s.user.answer || s.flag))

def onScan : Routine β ε δ :=
  Macro.branch (fun s => s.user.overflow) (returnValue (fun _ => false)) descendLeft

def resumeFrame : Routine β ε δ :=
  Macro.branch (fun s => s.user.answer)
    (Macro.branch (fun s => decide (s.other = some (symbol .leftTag)))
      descendRight (returnValue (fun _ => true)))
    nextMiddle

def onReturn : Routine β ε δ :=
  Macro.read (key .kinds) ⋙ₘ Macro.branch (fun s => s.value.isSome)
    (Macro.assign (fun s : Context β ε => {s with other := s.value}) ⋙ₘ restoreFields ⋙ₘ resumeFrame)
    (setPhase .done)

def popFrame : Routine β ε δ :=
  Macro.read (key .kinds) ⋙ₘ Macro.assign (fun s : Context β ε => {s with other := s.value}) ⋙ₘ restoreFields

def oneStep (query : Routine β ε δ) : Routine β ε δ :=
  Macro.branch (fun s => decide (s.user.phase = .call)) (onCall query)
    (Macro.branch (fun s => decide (s.user.phase = .scan)) onScan onReturn)

def running (s : Context β ε) : Bool := decide (s.user.phase ≠ .done)

def search (query : Routine β ε δ) : Code β ε δ :=
  .loop running (oneStep query).code

end

end Lax434930Proofs.SavitchProofs.SearchProgram
