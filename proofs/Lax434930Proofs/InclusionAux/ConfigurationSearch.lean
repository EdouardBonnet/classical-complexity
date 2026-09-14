import Lax434930Proofs.InclusionAux.TransitionTests
import Lax434930Proofs.InclusionAux.ReachabilityTable
import Lax434930Proofs.InclusionAux.TimeHelpers.BooleanComputer
import Lax434930.NondeterministicLogarithmicSpace

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ConfigurationPrograms

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930Proofs
open PolynomialConfigurations TimeHelpers.Streaming

noncomputable section

variable {I : Type}

def nextTest (M : Machine) (c : ℕ) (port table : I) (v : Number I) : Test I :=
  (Test.input table v).or
    (Test.exists (countNumber M c (Number.length port))
      ((Test.input (some table) (Number.length none)).and
        (edgeTest M c (some port) (Number.length none) (v.rename some))))

lemma nextTest_value (M : Machine) (c : ℕ) (port table : I) (v : Number I) (a : I → Word) :
    (nextTest M c port table v).value a =
      (ReachabilityTable.lookup (a table) (v.value a) ||
        (List.range (vertexCount M c (a port).length)).any (fun u =>
          ReachabilityTable.lookup (a table) u && ReachabilityTable.graphEdge M c (a port) u (v.value a))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [nextTest, Test.or, Bool.or_eq_true, Test.exists_true, countNumber_value,
    Test.and, Bool.and_eq_true, edgeTest_true, Number.rename, extend_some,
    Number.length, extend, Option.elim_some, Option.elim_none, List.length_replicate,
    Test.input, List.any_eq_true, List.mem_range, ReachabilityTable.lookup, ReachabilityTable.graphEdge,
    decide_eq_true_eq]

def initialCode (M : Machine) (c : ℕ) (port : I) : Code I :=
  Code.loop (countNumber M c (Number.length port))
    (Test.eq (Number.length none) (.constant (startVertex M))).code

lemma initialCode_eval (M : Machine) (c : ℕ) (port : I) (a : I → Word) :
    (initialCode M c port).eval a = ReachabilityTable.initial (vertexCount M c (a port).length) (startVertex M) := by
  simp [initialCode, Code.eval_loop, Test.correct, Test.eq_value, Number.length, Number.constant,
    extend, ReachabilityTable.initial, List.map_eq_flatMap]

def stepCode (M : Machine) (c : ℕ) (port table : I) : Code I :=
  Code.loop (countNumber M c (Number.length port))
    (nextTest M c (some port) (some table) (Number.length none)).code

lemma stepCode_eval (M : Machine) (c : ℕ) (port table : I) (a : I → Word) :
    (stepCode M c port table).eval a =
      ReachabilityTable.step (vertexCount M c (a port).length) (ReachabilityTable.graphEdge M c (a port)) (a table) := by
  simp only [stepCode, Code.eval_loop, Test.correct, nextTest_value]
  simp [countNumber_value, Number.length, extend, ReachabilityTable.step, List.map_eq_flatMap]

def roundNumber (M : Machine) (c : ℕ) (n : Number I) : Number I :=
  Number.polynomial (ConfigurationTime.logTimePolynomial M c) n

@[simp] lemma roundNumber_value (M : Machine) (c : ℕ) (n : Number I) (a : I → Word) :
    (roundNumber M c n).value a = ReachabilityTable.rounds M c (n.value a) := by
  simp [roundNumber, Number.polynomial_value, ReachabilityTable.rounds]

def tableCode (M : Machine) (c : ℕ) (port : I) : Code I :=
  Code.iterateValues (roundNumber M c (Number.length port)).code
    (countNumber M c (Number.length port)).code (initialCode M c port)
    (stepCode M c (some port) none)

lemma tableCode_eval (M : Machine) (c : ℕ) (port : I) (a : I → Word) :
    (tableCode M c port).eval a = ReachabilityTable.resultTable M c (a port) := by
  simp only [tableCode, Code.eval_iterateValues, Number.correct, List.length_replicate,
    roundNumber_value, countNumber_value, Number.length, initialCode_eval, stepCode_eval,
    extend, Option.elim_some, Option.elim_none]
  have hstep : ∀ acc : Word,
      (ReachabilityTable.step (vertexCount M c (a port).length) (ReachabilityTable.graphEdge M c (a port)) acc).take
        (vertexCount M c (a port).length) =
      ReachabilityTable.step (vertexCount M c (a port).length) (ReachabilityTable.graphEdge M c (a port)) acc := by
    intro acc
    apply List.take_of_length_le
    simp
  simp only [hstep]
  rfl

def terminalTest (M : Machine) (c : ℕ) (port table : I) : Test I :=
  Test.exists (countNumber M c (Number.length port))
    ((Test.input (some table) (Number.length none)).and
      (acceptingTest M c (some port) (Number.length none)))

lemma terminalTest_value (M : Machine) (c : ℕ) (port table : I) (a : I → Word) :
    (terminalTest M c port table).value a =
      (List.range (vertexCount M c (a port).length)).any (fun v =>
        ReachabilityTable.lookup (a table) v && accepting M c (a port) v) := by
  simp only [terminalTest, Test.exists, Test.and, Test.input, acceptingTest_value,
    countNumber_value, Number.length, extend, Option.elim_some, Option.elim_none,
    List.length_replicate, ReachabilityTable.lookup]

def resultCode (M : Machine) (c : ℕ) (port : I) : Code I :=
  .bind (tableCode M c port) (terminalTest M c (some port) none).code

lemma resultCode_eval (M : Machine) (c : ℕ) (port : I) (a : I → Word) :
    (resultCode M c port).eval a = [ReachabilityTable.answer M c (a port)] := by
  simp only [resultCode, Code.eval, Test.correct, terminalTest_value, tableCode_eval,
    extend, Option.elim_some, Option.elim_none, ReachabilityTable.answer]

lemma computer (M : Machine) (c : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool (ReachabilityTable.answer M c)) :=
  Code.boolean_computer (resultCode M c ()) (ReachabilityTable.answer M c)
    (fun w => resultCode_eval M c () (fun _ => w))

end

end Lax434930Proofs.InclusionAux.ConfigurationPrograms

namespace Lax434930Proofs.InclusionAux

open Lax434930.PolynomialTime Lax434930.NondeterministicLogarithmicSpace

lemma NL_subset_P : NL ⊆ P := by
  rintro A ⟨c, hc, M, hdec, hs⟩
  exact ⟨ReachabilityTable.answer M c, ReachabilityTable.answer_correct M c hc A hdec hs,
    ConfigurationPrograms.computer M c⟩

end Lax434930Proofs.InclusionAux
