import Lax434930Proofs.SavitchDefinitions.BoundedConfigurations
import Lax434930Proofs.SavitchDefinitions.Reachability
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
Vertices are configurations whose work tape has a fixed finite bound.
Edges are machine transitions. Acceptance is reachability from the initial
configuration to a terminal accepting configuration. The search predicate
replaces reachability by the recursive finite graph test.
-/

namespace Lax434930Proofs.SavitchDefinitions.ConfigurationGraph

open Lax434930.PolynomialTime Lax434930.SpaceMachines BoundedConfigurations Reachability

noncomputable def numbering (M : Machine) (n s : ℕ) :
    Config M n s ≃ Fin (Fintype.card (Config M n s)) := Fintype.equivFin _

noncomputable def graph (M : Machine) (w : Word) (s : ℕ) :
    Graph (Fintype.card (Config M w.length s)) := by
  classical
  exact fun a b => decide (M.Step w (expand ((numbering M w.length s).symm a))
    (expand ((numbering M w.length s).symm b)))

def AcceptsBounded (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∃ a b : Config M w.length s,
    expand a = M.initial ∧ M.Terminal w (expand b) ∧ M.accept b.state = true ∧
    Reachable (graph M w s) (numbering M w.length s a) (numbering M w.length s b)

def SearchAccepts (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∃ a b : Config M w.length s,
    expand a = M.initial ∧ M.Terminal w (expand b) ∧ M.accept b.state = true ∧
    search (graph M w s) (Nat.clog 2 (Fintype.card (Config M w.length s)))
      (numbering M w.length s a) (numbering M w.length s b) = true

end Lax434930Proofs.SavitchDefinitions.ConfigurationGraph
