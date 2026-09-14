import Lax434930Proofs.InclusionAux.ConfigurationTests

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ConfigurationPrograms

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open PolynomialConfigurations TimeHelpers.Streaming
open scoped Classical

noncomputable section

variable {I : Type}

def tapeTest (M : Machine) (limit before after head : Number I) (write : M.Γ) : Test I :=
  Test.forall limit (chooseTest (Test.eq (Number.length none) (head.rename some))
    (Test.eq (tapeSymbol M (after.rename some) (Number.length none))
      (.constant (Fintype.equivFin M.Γ write).val))
    (Test.eq (tapeSymbol M (after.rename some) (Number.length none))
      (tapeSymbol M (before.rename some) (Number.length none))))

lemma tapeTest_true (M : Machine) (limit before after head : Number I) (write : M.Γ) (a : I → Word) :
    (tapeTest M limit before after head write).value a = true ↔
      ∀ i, i < limit.value a → tapeRead M (after.value a) i =
        if i = head.value a then write else tapeRead M (before.value a) i := by
  rw [tapeTest, Test.forall_true]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  simp only [chooseTest, Test.eq_value, tapeSymbol_value, Number.rename, extend_some,
    Number.length, Number.constant, extend, Option.elim_none, List.length_replicate, decide_eq_true_eq]
  by_cases hh : i = head.value a <;> simp [hh, symbolIndex_eq]

def effectTest (M : Machine) (c : ℕ) (port : I) (before after : Number I) (action : Action M.Γ M.Q) : Test I :=
  let n := Number.length port
  (stateIs M after action.state).and
    ((Test.eq (inputNumber M n after)
      ((moveNumber action.inputMove (inputNumber M n before)).min (n.add (.constant 1)))).and
    ((Test.eq (workNumber M c n after) (moveNumber action.workMove (workNumber M c n before))).and
    (tapeTest M (limitNumber M c n) (contentsNumber M c n before) (contentsNumber M c n after)
      (workNumber M c n before) action.write)))

lemma effectTest_true (M : Machine) (c : ℕ) (port : I) (before after : Number I)
    (action : Action M.Γ M.Q) (a : I → Word) :
    (effectTest M c port before after action).value a = true ↔
      stateRead M (after.value a) = action.state ∧
      inputIndex M (a port).length (after.value a) =
        min (action.inputMove.apply (inputIndex M (a port).length (before.value a))) ((a port).length + 1) ∧
      workIndex M c (a port).length (after.value a) = action.workMove.apply (workIndex M c (a port).length (before.value a)) ∧
      ∀ i, i < tapeLimit M c (a port).length → tapeRead M (tapeIndex M c (a port).length (after.value a)) i =
        if i = workIndex M c (a port).length (before.value a) then action.write
        else tapeRead M (tapeIndex M c (a port).length (before.value a)) i := by
  simp only [effectTest, Test.and, Bool.and_eq_true, stateIs_true, Test.eq_value,
    decide_eq_true_eq, Number.min_value, moveNumber_value, inputNumber_value, workNumber_value,
    tapeTest_true, limitNumber_value, contentsNumber_value, Number.add, Number.constant, Number.length]

def observationTest (M : Machine) (c : ℕ) (port : I) (v : Number I)
    (f : M.Q → InputSymbol → M.Γ → Test I) : Test I :=
  Test.anyFinite (fun q : M.Q => (stateIs M v q).and
    (Test.anyFinite (fun input : InputSymbol => (inputIs port (inputNumber M (Number.length port) v) input).and
      (Test.anyFinite (fun g : M.Γ =>
        (Test.eq (tapeSymbol M (contentsNumber M c (Number.length port) v) (workNumber M c (Number.length port) v))
          (.constant (Fintype.equivFin M.Γ g).val)).and (f q input g))))))

lemma observationTest_true (M : Machine) (c : ℕ) (port : I) (v : Number I)
    (f : M.Q → InputSymbol → M.Γ → Test I) (a : I → Word) :
    (observationTest M c port v f).value a = true ↔
      (f (stateRead M (v.value a)) (readInput (a port) (inputIndex M (a port).length (v.value a)))
        (tapeRead M (tapeIndex M c (a port).length (v.value a)) (workIndex M c (a port).length (v.value a)))).value a = true := by
  simp only [observationTest, Test.anyFinite_true, Test.and, Bool.and_eq_true, stateIs_true,
    inputIs_true, Test.eq_value, tapeSymbol_value, Number.constant, Number.length,
    inputNumber_value, contentsNumber_value, workNumber_value, decide_eq_true_eq, symbolIndex_eq]
  simp

def edgeTest (M : Machine) (c : ℕ) (port : I) (before after : Number I) : Test I :=
  observationTest M c port before (fun q input g =>
    Test.anyList (M.transition q input g).toList (effectTest M c port before after))

lemma edgeTest_true (M : Machine) (c : ℕ) (port : I) (before after : Number I) (a : I → Word) :
    (edgeTest M c port before after).value a = true ↔ Edge M c (a port) (before.value a) (after.value a) := by
  rw [edgeTest, observationTest_true, Test.anyList_true]
  simp only [Finset.mem_toList, effectTest_true, Edge, actions]

def acceptingTest (M : Machine) (c : ℕ) (port : I) (v : Number I) : Test I :=
  observationTest M c port v (fun q input g => Test.constant (decide (M.transition q input g = ∅) && M.accept q))

lemma acceptingTest_value (M : Machine) (c : ℕ) (port : I) (v : Number I) (a : I → Word) :
    (acceptingTest M c port v).value a = accepting M c (a port) (v.value a) := by
  apply Bool.eq_iff_iff.mpr
  rw [acceptingTest, observationTest_true]
  rfl

end

end Lax434930Proofs.InclusionAux.ConfigurationPrograms
