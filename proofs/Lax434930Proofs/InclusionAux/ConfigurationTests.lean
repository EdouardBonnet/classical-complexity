import Lax434930Proofs.InclusionAux.PolynomialConfigurationGraph
import Lax434930Proofs.InclusionAux.TimeHelpers.BoundedCode

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ConfigurationPrograms

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open PolynomialConfigurations TimeHelpers.Streaming

noncomputable section

variable {I : Type}

def headNumber (c : ℕ) (n : Number I) : Number I := (Number.constant c).mul (n.add (.constant 2))
def tapeNumber (M : Machine) (c : ℕ) (n : Number I) : Number I := (n.add (.constant 2)).power (base M * c)
def countNumber (M : Machine) (c : ℕ) (n : Number I) : Number I :=
  (((Number.constant (Fintype.card M.Q)).mul (n.add (.constant 2))).mul (headNumber c n)).mul (tapeNumber M c n)
def limitNumber (M : Machine) (c : ℕ) (n : Number I) : Number I := (tapeNumber M c n).add (headNumber c n)
def inputNumber (M : Machine) (n v : Number I) : Number I := (v.div (.constant (Fintype.card M.Q))).mod (n.add (.constant 2))
def workNumber (M : Machine) (c : ℕ) (n v : Number I) : Number I :=
  ((v.div (.constant (Fintype.card M.Q))).div (n.add (.constant 2))).mod (headNumber c n)
def contentsNumber (M : Machine) (c : ℕ) (n v : Number I) : Number I :=
  ((v.div (.constant (Fintype.card M.Q))).div (n.add (.constant 2))).div (headNumber c n)

@[simp] lemma headNumber_value (c : ℕ) (n : Number I) (a : I → Word) :
    (headNumber c n).value a = headBound c (n.value a) := rfl
@[simp] lemma tapeNumber_value (M : Machine) (c : ℕ) (n : Number I) (a : I → Word) :
    (tapeNumber M c n).value a = tapeBound M c (n.value a) := by
  simp [tapeNumber, Number.power_value, Number.add, Number.constant, tapeBound]
@[simp] lemma countNumber_value (M : Machine) (c : ℕ) (n : Number I) (a : I → Word) :
    (countNumber M c n).value a = vertexCount M c (n.value a) := by
  simp [countNumber, Number.mul, Number.add, Number.constant, vertexCount]
@[simp] lemma limitNumber_value (M : Machine) (c : ℕ) (n : Number I) (a : I → Word) :
    (limitNumber M c n).value a = tapeLimit M c (n.value a) := by
  simp [limitNumber, Number.add, tapeLimit]
@[simp] lemma inputNumber_value (M : Machine) (n v : Number I) (a : I → Word) :
    (inputNumber M n v).value a = inputIndex M (n.value a) (v.value a) := rfl
@[simp] lemma workNumber_value (M : Machine) (c : ℕ) (n v : Number I) (a : I → Word) :
    (workNumber M c n v).value a = workIndex M c (n.value a) (v.value a) := rfl
@[simp] lemma contentsNumber_value (M : Machine) (c : ℕ) (n v : Number I) (a : I → Word) :
    (contentsNumber M c n v).value a = tapeIndex M c (n.value a) (v.value a) := rfl

def moveNumber : Move → Number I → Number I
  | .left, n => n.sub (.constant 1)
  | .stay, n => n
  | .right, n => n.add (.constant 1)

@[simp] lemma moveNumber_value (d : Move) (n : Number I) (a : I → Word) :
    (moveNumber d n).value a = d.apply (n.value a) := by cases d <;> rfl

lemma stateRead_eq (M : Machine) (v : ℕ) (q : M.Q) :
    stateRead M v = q ↔ v % Fintype.card M.Q = stateCode M q := by
  constructor
  · intro h
    simpa [stateCode, stateRead] using congrArg (stateCode M) h
  · intro h
    apply (Fintype.equivFin M.Q).injective
    apply Fin.ext
    simpa [stateRead, stateCode] using h

def stateIs (M : Machine) (v : Number I) (q : M.Q) : Test I :=
  Test.eq (v.mod (.constant (Fintype.card M.Q))) (.constant (stateCode M q))

@[simp] lemma stateIs_true (M : Machine) (v : Number I) (q : M.Q) (a : I → Word) :
    (stateIs M v q).value a = true ↔ stateRead M (v.value a) = q := by
  simp [stateIs, Test.eq_value, Number.mod, Number.constant, stateRead_eq]

def symbolNumber (M : Machine) (v : Number I) : Number I :=
  Number.choose (Test.eq v (.constant 0)) (.constant (Fintype.equivFin M.Γ M.blank).val)
    ((v.sub (.constant 1)).mod (.constant (Fintype.card M.Γ)))

@[simp] lemma symbolNumber_value (M : Machine) (v : Number I) (a : I → Word) :
    (symbolNumber M v).value a = (Fintype.equivFin M.Γ (symbolRead M (v.value a))).val := by
  simp [symbolNumber, Number.choose, Test.eq_value, Number.constant, Number.sub, Number.mod, symbolRead]
  split_ifs <;> simp

def tapeSymbol (M : Machine) (t i : Number I) : Number I :=
  symbolNumber M (t.digit (.constant (base M)) i)

@[simp] lemma tapeSymbol_value (M : Machine) (t i : Number I) (a : I → Word) :
    (tapeSymbol M t i).value a = (Fintype.equivFin M.Γ (tapeRead M (t.value a) (i.value a))).val := by
  simp [tapeSymbol, Number.digit_value, Number.constant, tapeRead]

lemma symbolIndex_eq (M : Machine) (g h : M.Γ) :
    (Fintype.equivFin M.Γ g).val = (Fintype.equivFin M.Γ h).val ↔ g = h := by
  constructor
  · intro h; exact (Fintype.equivFin M.Γ).injective (Fin.ext h)
  · rintro rfl; rfl

def inputIs (port : I) (index : Number I) : InputSymbol → Test I
  | .leftEnd => Test.eq index (.constant 0)
  | .rightEnd => Test.lt (Number.length port) index
  | .bit b => (Test.lt (.constant 0) index).and
      ((Test.lt index ((Number.length port).add (.constant 1))).and
        (if b then Test.input port (index.sub (.constant 1)) else (Test.input port (index.sub (.constant 1))).not))

@[simp] lemma inputIs_true (port : I) (index : Number I) (symbol : InputSymbol) (a : I → Word) :
    (inputIs port index symbol).value a = true ↔ readInput (a port) (index.value a) = symbol := by
  cases hindex : index.value a with
  | zero =>
    cases symbol <;> simp [inputIs, Test.eq_value, Test.lt, Test.and, Number.constant, Number.length,
      hindex, readInput]
  | succ i =>
    by_cases hi : i < (a port).length
    · have hget := List.getElem?_eq_getElem hi
      cases symbol with
      | leftEnd => simp [inputIs, Test.eq_value, Number.constant, hindex, readInput, hget]
      | rightEnd => simp [inputIs, Test.lt, Number.length, hindex, readInput, hget]; omega
      | bit b =>
        cases b <;> cases hbit : (a port)[i] <;>
          simp [inputIs, Test.lt, Test.and, Test.input, Test.not, Number.constant, Number.length,
            Number.add, Number.sub, hindex, readInput, hget, hbit, hi]
    · have hget : (a port)[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      cases symbol <;>
        simp [inputIs, Test.eq_value, Test.lt, Test.and, Number.constant, Number.length,
          Number.add, hindex, readInput, hget] <;> omega

def chooseTest (test yes no : Test I) : Test I where
  value a := if test.value a then yes.value a else no.value a
  code := Code.when test yes.code no.code
  correct a := by rw [Code.eval_when]; split <;> first | exact yes.correct a | exact no.correct a

end

end Lax434930Proofs.InclusionAux.ConfigurationPrograms
