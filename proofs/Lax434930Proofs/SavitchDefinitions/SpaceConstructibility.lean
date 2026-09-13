import Lax434930.SpaceBounds

set_option backward.isDefEq.respectTransparency false

/-!
A positive bound $s$ is fully space-constructible if a deterministic
machine, on each input of length $n$, halts at work position $s(n)-1$
without leaving the first $s(n)$ work cells. The input tape is read-only.
-/

namespace Lax434930Proofs.SavitchDefinitions.SpaceConstructibility

open Lax434930.PolynomialTime Lax434930.SpaceMachines

def Constructible (s : ℕ → ℕ) : Prop :=
  ∃ M : Machine, M.Deterministic ∧ ∀ w : Word,
    M.HaltsOn w ∧ M.UsesSpace w (s w.length) ∧
    ∃ (t : ℕ) (c : M.Config), M.Run w t c ∧ M.Terminal w c ∧
      c.workHead + 1 = s w.length

end Lax434930Proofs.SavitchDefinitions.SpaceConstructibility
