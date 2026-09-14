import Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs Lax434930Proofs.SavitchProofs.MachinePaths
open scoped Classical

noncomputable section

variable {K Γ Q : Type} [Fintype K] [Fintype Γ] [Fintype Q]
variable (P : Program K Γ Q) (w : Word) (bound : ℕ) (post : (compile P).Config → Prop)

lemma return_tree (q : Q) (inputHead pos : ℕ) (store : K → List Γ)
    (hi : inputHead ≤ w.length + 1) (hb : pos < bound)
    (ht : ExecutionTree (compile P) w bound post (located P (.dispatch q) inputHead 0 store)) :
    ExecutionTree (compile P) w bound post (located P (.back q) inputHead pos store) := by
  induction pos with
  | zero =>
    apply local_next P w bound post _
      ⟨.dispatch q, StackMachine.tape store 0, .stay, .stay⟩ hb
      (by intro b; simp [located, StackMachine.located, StackMachine.tape, StackMachine.action])
    simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi] using ht
  | succ pos ih =>
    have hh := ih (by omega)
    apply local_next P w bound post _
      ⟨.back q, StackMachine.tape store (pos + 1), .stay, .left⟩ hb
      (by intro b; simp [located, StackMachine.located, StackMachine.tape, StackMachine.action])
    simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi] using hh

lemma scan_tree (q : StackMachine.Control K Γ Q) (inputHead start stop : ℕ) (store : K → List Γ)
    (hi : inputHead ≤ w.length + 1) (hs : start ≤ stop) (hb : stop < bound)
    (ha : ∀ i < stop, ∀ b, StackMachine.action (P.resolve b) q (readInput w inputHead) (StackMachine.tape store i) =
      some ⟨q, StackMachine.tape store i, .stay, .right⟩)
    (ht : ExecutionTree (compile P) w bound post (located P q inputHead stop store)) :
    ExecutionTree (compile P) w bound post (located P q inputHead start store) := by
  induction stop generalizing start with
  | zero =>
    have : start = 0 := by omega
    subst start
    exact ht
  | succ stop ih =>
    by_cases he : start = stop + 1
    · subst start; exact ht
    · have hh : ExecutionTree (compile P) w bound post (located P q inputHead stop store) := by
        apply local_next P w bound post _
          ⟨q, StackMachine.tape store stop, .stay, .right⟩ (by change stop < bound; omega)
          (ha stop (by omega))
        simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi] using ht
      exact ih start (by omega) (by omega) (fun i hi b => ha i (by omega) b) hh

lemma move_tree (q next : Q) (direction : Move) (inputHead : ℕ) (store : K → List Γ)
    (hb : 0 < bound) (hc : P.code q (readInput w inputHead) = .move direction next)
    (ht : ExecutionTree (compile P) w bound post
      (located P (.dispatch next) (min (direction.apply inputHead) (w.length + 1)) 0 store)) :
    ExecutionTree (compile P) w bound post (located P (.dispatch q) inputHead 0 store) := by
  apply local_next P w bound post _ ⟨.dispatch next, StackMachine.tape store 0, direction, .stay⟩ hb
    (by intro b; simp [located, StackMachine.located, StackMachine.action, Program.resolve, hc, Instruction.resolve])
  simpa [located, StackMachine.located, Machine.execute, Move.apply] using ht

lemma push_tree (q next : Q) (inputHead : ℕ) (store : K → List Γ) (k : K) (g : Γ)
    (hi : inputHead ≤ w.length + 1) (hb : (store k).length < bound)
    (hc : P.code q (readInput w inputHead) = .push k g next)
    (ht : ExecutionTree (compile P) w bound post
      (located P (.dispatch next) inputHead 0 (Function.update store k (g :: store k)))) :
    ExecutionTree (compile P) w bound post (located P (.dispatch q) inputHead 0 store) := by
  have hback := return_tree P w bound post next inputHead ((store k).length - 1)
    (Function.update store k (g :: store k)) hi (by omega) ht
  have hwrite : ExecutionTree (compile P) w bound post
      (located P (.push k g next) inputHead (store k).length store) := by
    apply local_next P w bound post _
      ⟨.back next, ((StackMachine.tape store (store k).length).1,
        Function.update (StackMachine.tape store (store k).length).2 k (some g)), .stay, .left⟩ hb
      (by intro b; simp [located, StackMachine.located, StackMachine.action, StackMachine.tape])
    convert hback using 1
    simp only [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi]
    congr 1
    exact StackMachine.tape_push store k g
  have hscan := scan_tree P w bound post (.push k g next) inputHead 0 (store k).length store hi
    (Nat.zero_le _) hb (by
      intro i hi b
      have hir : i < (store k).reverse.length := by simpa using hi
      simp [StackMachine.action, StackMachine.tape, List.getElem?_eq_getElem hir]) hwrite
  apply local_next P w bound post _
    ⟨.push k g next, StackMachine.tape store 0, .stay, .stay⟩ (by change 0 < bound; omega)
    (by intro b; simp [located, StackMachine.located, StackMachine.action, Program.resolve, hc, Instruction.resolve])
  simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi] using hscan

lemma pop_tree (q : Q) (next : Option Γ → Q) (inputHead : ℕ)
    (store : K → List Γ) (k : K) (hi : inputHead ≤ w.length + 1)
    (hb : (store k).length < bound)
    (hc : P.code q (readInput w inputHead) = .pop k next)
    (ht : ExecutionTree (compile P) w bound post
      (located P (.dispatch (next (store k).head?)) inputHead 0
        (Function.update store k (store k).tail))) :
    ExecutionTree (compile P) w bound post (located P (.dispatch q) inputHead 0 store) := by
  have hzero : 0 < bound := by omega
  have hpop : ExecutionTree (compile P) w bound post
      (located P (.pop k next) inputHead 0 store) := by
    cases hk : store k with
    | nil =>
      have hu : Function.update store k [] = store := by
        rw [← hk, Function.update_eq_self]
      apply local_next P w bound post _
        ⟨.dispatch (next none), StackMachine.tape store 0, .stay, .stay⟩ hzero
        (by intro b; simp [located, StackMachine.located, StackMachine.action, StackMachine.tape, hk])
      simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi, hk, hu] using ht
    | cons g xs =>
      have hlen : xs.length < bound := by simp only [hk, List.length_cons] at hb; omega
      have hback := return_tree P w bound post (next (some g)) inputHead (xs.length - 1)
        (Function.update store k xs) hi (by omega) (by simpa only [hk, List.head?_cons, List.tail_cons] using ht)
      have htake : ExecutionTree (compile P) w bound post
          (located P (.take k next) inputHead xs.length store) := by
        apply local_next P w bound post _
          ⟨.back (next (some g)), ((StackMachine.tape store xs.length).1,
            Function.update (StackMachine.tape store xs.length).2 k none), .stay, .left⟩ hlen
          (by intro b; simp [located, StackMachine.located, StackMachine.action, StackMachine.tape, hk])
        convert hback using 1
        simp only [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi]
        congr 1
        exact StackMachine.tape_pop store k g xs hk
      have hleft : ExecutionTree (compile P) w bound post
          (located P (.pop k next) inputHead (store k).length store) := by
        apply local_next P w bound post _
          ⟨.take k next, StackMachine.tape store (store k).length, .stay, .left⟩ hb
          (by intro b; simp [located, StackMachine.located, StackMachine.action, StackMachine.tape, hk])
        simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi, hk] using htake
      exact scan_tree P w bound post (.pop k next) inputHead 0 (store k).length store hi
        (Nat.zero_le _) hb (by
          intro i hi b
          have hir : i < (store k).reverse.length := by simpa using hi
          simp [StackMachine.action, StackMachine.tape, List.getElem?_eq_getElem hir]) hleft
  apply local_next P w bound post _
    ⟨.pop k next, StackMachine.tape store 0, .stay, .stay⟩ hzero
    (by intro b; simp [located, StackMachine.located, StackMachine.action, Program.resolve, hc, Instruction.resolve])
  simpa [located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi] using hpop

lemma choose_tree (q : Q) (next : Bool → Q) (inputHead : ℕ) (store : K → List Γ)
    (hi : inputHead ≤ w.length + 1) (hb : 0 < bound)
    (hc : P.code q (readInput w inputHead) = .choose next)
    (ht : ∀ b, ExecutionTree (compile P) w bound post (located P (.dispatch (next b)) inputHead 0 store)) :
    ExecutionTree (compile P) w bound post (located P (.dispatch q) inputHead 0 store) := by
  let c := located P (.dispatch q) inputHead 0 store
  let a (b : Bool) : Action (StackMachine.Alphabet K Γ) (StackMachine.Control K Γ Q) :=
    ⟨.dispatch (next b), StackMachine.tape store 0, .stay, .stay⟩
  have ha (b : Bool) : StackMachine.action (P.resolve b) c.state (readInput w c.inputHead) (c.tape c.workHead) = some (a b) := by
    simp [c, a, located, StackMachine.located, StackMachine.action, Program.resolve, hc, Instruction.resolve]
  have he (b : Bool) : ExecutionTree (compile P) w bound post ((compile P).execute w c (a b)) := by
    simpa [c, a, located, StackMachine.located, Machine.execute, Move.apply, Nat.min_eq_left hi] using ht b
  apply ExecutionTree.branch hb ⟨a false, (mem_transition P _ _ _ _).mpr (Or.inl (ha false))⟩
  intro x hx
  rcases (mem_transition P _ _ _ _).mp hx with h | h
  · have hh : x = a false := Option.some.inj (h.symm.trans (ha false))
    exact hh ▸ he false
  · have hh : x = a true := Option.some.inj (h.symm.trans (ha true))
    exact hh ▸ he true

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.NondeterministicStack
