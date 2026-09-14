import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Sum
import Lean.Elab.Tactic.Omega

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false

/-!
Structured programs over the very same stacks and finite control as TM2.
The compiler uses a finite label type obtained from the syntax tree. Loops
jump back to their header; they do not allocate a runtime continuation stack.
The correctness theorem transfers a terminating structured execution to
actual TM2 steps, with no assumption of a compiler or composition theorem.
-/

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

open Turing

variable {K : Type} (Γ : K → Type) (σ : Type)

structure Store where
  state : σ
  stk : (k : K) → List (Γ k)

theorem Store.ext {s t : Store Γ σ} (hs : s.state = t.state) (hk : s.stk = t.stk) :
    s = t := by
  cases s
  cases t
  cases hs
  cases hk
  rfl

inductive Op
  | push (k : K) (f : σ → Γ k)
  | pop (k : K) (f : σ → Option (Γ k) → σ)
  | peek (k : K) (f : σ → Option (Γ k) → σ)
  | load (f : σ → σ)

inductive Program
  | atom (o : Op Γ σ)
  | seq (p q : Program)
  | branch (b : σ → Bool) (p q : Program)
  | loop (b : σ → Bool) (p : Program)

variable {Γ σ}

def Op.apply [DecidableEq K] (o : Op Γ σ) (s : Store Γ σ) : Store Γ σ :=
  match o with
  | .push k f => ⟨s.state, Function.update s.stk k (f s.state :: s.stk k)⟩
  | .pop k f => ⟨f s.state (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .peek k f => ⟨f s.state (s.stk k).head?, s.stk⟩
  | .load f => ⟨f s.state, s.stk⟩

def Labels : Program Γ σ → Type
  | .atom _ => Unit
  | .seq p q => Labels p ⊕ Labels q
  | .branch _ p q => Unit ⊕ (Labels p ⊕ Labels q)
  | .loop _ p => Unit ⊕ Labels p

instance labelsFintype (p : Program Γ σ) : Fintype (Labels p) :=
  match p with
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .seq p q => by
      letI := labelsFintype p
      letI := labelsFintype q
      exact inferInstanceAs (Fintype (Labels p ⊕ Labels q))
  | .branch _ p q => by
      letI := labelsFintype p
      letI := labelsFintype q
      exact inferInstanceAs (Fintype (Unit ⊕ (Labels p ⊕ Labels q)))
  | .loop _ p => by
      letI := labelsFintype p
      exact inferInstanceAs (Fintype (Unit ⊕ Labels p))

def entry : (p : Program Γ σ) → Labels p
  | .atom _ => ()
  | .seq p _ => .inl (entry p)
  | .branch _ _ _ | .loop _ _ => .inl ()

def jump {Λ : Type} (next : Option Λ) : TM2.Stmt Γ Λ σ :=
  match next with
  | none => .halt
  | some l => .goto (fun _ => l)

def Op.compile {Λ : Type} (o : Op Γ σ) (next : Option Λ) : TM2.Stmt Γ Λ σ :=
  match o with
  | .push k f => .push k f (jump next)
  | .pop k f => .pop k f (jump next)
  | .peek k f => .peek k f (jump next)
  | .load f => .load f (jump next)

def compile {Λ : Type} (p : Program Γ σ) (embed : Labels p → Λ)
    (next : Option Λ) : Labels p → TM2.Stmt Γ Λ σ :=
  match p with
  | .atom o => fun _ => o.compile next
  | .seq p q => Sum.elim
      (compile p (embed ∘ Sum.inl) (some (embed (.inr (entry q)))))
      (compile q (embed ∘ Sum.inr) next)
  | .branch b p q => Sum.elim
      (fun _ => .branch b (jump (some (embed (.inr (.inl (entry p))))))
        (jump (some (embed (.inr (.inr (entry q)))))))
      (Sum.elim (compile p (embed ∘ Sum.inr ∘ Sum.inl) next)
        (compile q (embed ∘ Sum.inr ∘ Sum.inr) next))
  | .loop b p => Sum.elim
      (fun _ => .branch b (jump (some (embed (.inr (entry p))))) (jump next))
      (compile p (embed ∘ Sum.inr) (some (embed (.inl ()))))

inductive Executes [DecidableEq K] :
    Program Γ σ → Store Γ σ → Store Γ σ → Nat → Prop
  | atom (o : Op Γ σ) (s : Store Γ σ) : Executes (.atom o) s (o.apply s) 1
  | seq {p q s u t a b} : Executes p s u a → Executes q u t b →
      Executes (.seq p q) s t (a + b)
  | branch_true {p q s t a} {b : σ → Bool} : b s.state = true →
      Executes p s t a → Executes (.branch b p q) s t (a + 1)
  | branch_false {p q s t a} {b : σ → Bool} : b s.state = false →
      Executes q s t a → Executes (.branch b p q) s t (a + 1)
  | loop_false {p s} {b : σ → Bool} : b s.state = false →
      Executes (.loop b p) s s 1
  | loop_true {p s u t a c} {b : σ → Bool} : b s.state = true →
      Executes p s u a → Executes (.loop b p) u t c →
      Executes (.loop b p) s t (a + c + 1)

def config {Λ : Type} (l : Option Λ) (s : Store Γ σ) : TM2.Cfg Γ Λ σ :=
  ⟨l, s.state, s.stk⟩

def Runs [DecidableEq K] {Λ : Type} (code : Λ → TM2.Stmt Γ Λ σ)
    (l : Option Λ) (s : Store Γ σ) (l' : Option Λ) (s' : Store Γ σ) (t : Nat) : Prop :=
  (fun c => c.bind (TM2.step code))^[t] (some (config l s)) = some (config l' s')

theorem runs_one [DecidableEq K] {Λ : Type} (code : Λ → TM2.Stmt Γ Λ σ)
    (l : Λ) (s : Store Γ σ) (l' : Option Λ) (s' : Store Γ σ)
    (h : TM2.stepAux (code l) s.state s.stk = config l' s') :
    Runs code (some l) s l' s' 1 := by
  simpa only [Runs, Function.iterate_one, Option.bind_some, config, TM2.step] using
    congrArg some h

theorem runs_trans [DecidableEq K] {Λ : Type} {code : Λ → TM2.Stmt Γ Λ σ}
    {l m n : Option Λ} {s u t : Store Γ σ} {a b : Nat}
    (h : Runs code l s m u a) (h' : Runs code m u n t b) :
    Runs code l s n t (a + b) := by
  unfold Runs at *
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

theorem stepAux_jump [DecidableEq K] {Λ : Type} (next : Option Λ)
    (s : Store Γ σ) : TM2.stepAux (jump next) s.state s.stk = config next s := by
  cases next <;> rfl

theorem stepAux_op [DecidableEq K] {Λ : Type} (o : Op Γ σ) (next : Option Λ)
    (s : Store Γ σ) :
    TM2.stepAux (o.compile next) s.state s.stk = config next (o.apply s) := by
  cases o <;> cases next <;> rfl

/-- Correctness under an arbitrary embedding of this program's labels into a
larger code array. This form supports nested loops and sequential composition. -/
theorem compile_correct [DecidableEq K] {p : Program Γ σ} {s t : Store Γ σ} {cost : Nat}
    (h : Executes p s t cost) {Λ : Type} (code : Λ → TM2.Stmt Γ Λ σ)
    (embed : Labels p → Λ) (next : Option Λ)
    (hc : ∀ l, code (embed l) = compile p embed next l) :
    Runs code (some (embed (entry p))) s next t cost := by
  revert embed next
  induction h with
  | atom o s =>
      intro embed next hc
      apply runs_one
      rw [hc]
      exact stepAux_op o next s
  | seq hp hq ihp ihq =>
      intro embed next hc
      exact runs_trans
        (ihp (embed ∘ Sum.inl) (some (embed (.inr (entry _)))) (fun l => hc (.inl l)))
        (ihq (embed ∘ Sum.inr) next (fun l => hc (.inr l)))
  | @branch_true p q s t a b hb hp ih =>
      intro embed next hc
      have hstart := runs_one code (embed (.inl ())) s
        (some (embed (.inr (.inl (entry p))))) s (by
          rw [hc]
          simp only [compile, Sum.elim_inl, TM2.stepAux, hb, Bool.cond_true]
          rfl)
      have hbody := ih (embed ∘ Sum.inr ∘ Sum.inl) next (fun l => hc (.inr (.inl l)))
      simpa only [Nat.add_comm 1] using! runs_trans hstart hbody
  | @branch_false p q s t a b hb hq ih =>
      intro embed next hc
      have hstart := runs_one code (embed (.inl ())) s
        (some (embed (.inr (.inr (entry q))))) s (by
          rw [hc]
          simp only [compile, Sum.elim_inl, TM2.stepAux, hb, Bool.cond_false]
          rfl)
      have hbody := ih (embed ∘ Sum.inr ∘ Sum.inr) next (fun l => hc (.inr (.inr l)))
      simpa only [Nat.add_comm 1] using! runs_trans hstart hbody
  | loop_false hb =>
      intro embed next hc
      apply runs_one
      rw [hc]
      simp only [compile, entry, Sum.elim_inl, TM2.stepAux, hb, Bool.cond_false]
      exact stepAux_jump next _
  | @loop_true p s u t a c b hb hp hloop ihp ihloop =>
      intro embed next hc
      have hstart := runs_one code (embed (.inl ())) s
        (some (embed (.inr (entry p)))) s (by
          rw [hc]
          simp only [compile, Sum.elim_inl, TM2.stepAux, hb, Bool.cond_true]
          rfl)
      have hbody := ihp (embed ∘ Sum.inr) (some (embed (.inl ()))) (fun l => hc (.inr l))
      have hrest := ihloop embed next hc
      simpa only [Nat.add_comm 1, Nat.add_assoc] using!
        runs_trans hstart (runs_trans hbody hrest)

/-- The actual finite machine obtained by compiling a structured program. -/
def machine [DecidableEq K] [Fintype K] [Fintype σ]
    (p : Program Γ σ) (input output : K) [Fintype (Γ input)] (initial : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Λ := Labels p
  main := entry p
  σ := σ
  initialState := initial
  m := compile p id none

/-- A terminating structured execution supplies a concrete TM2 time witness. -/
theorem machine_runs [DecidableEq K] [Fintype K] [Fintype σ]
    (p : Program Γ σ) (input output : K) [Fintype (Γ input)] (initial : σ)
    (s t : Store Γ σ) (cost : Nat) (h : Executes p s t cost) :
    Nonempty (StateTransition.EvalsToInTime (machine p input output initial).step
      (config (some (entry p)) s) (some (config none t)) cost) := by
  refine ⟨⟨⟨cost, ?_⟩, le_rfl⟩⟩
  exact compile_correct h (compile p id none) id none (fun _ => rfl)

def ioStore [DecidableEq K] (port : K) (initial : σ) (w : List (Γ port)) :
    Store Γ σ where
  state := initial
  stk k := if h : k = port then (by rw [h]; exact w) else []

/-- Transfer any polynomial bound on a structured program to the exact
bundled complexity notion used in the approved concepts. The hypothesis
includes cleanup of the work stacks and resetting finite control. -/
theorem program_polytime [DecidableEq K] [Fintype K] [Fintype σ]
    (p : Program Γ σ) (input output : K) [Fintype (Γ input)] (initial : σ)
    {α β : Type} (ea : α → List (Γ input)) (eb : β → List (Γ output))
    (f : α → β) (bound : Polynomial Nat)
    (h : ∀ a, ∃ t, t ≤ bound.eval (ea a).length ∧
      Executes p (ioStore input initial (ea a)) (ioStore output initial (eb (f a))) t) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  refine ⟨{ tm := machine p input output initial
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := bound
            outputsFun := ?_ }⟩
  intro a
  let t := Classical.choose (h a)
  have ht := Classical.choose_spec (h a)
  dsimp only [Equiv.refl, machine]
  refine ⟨⟨t, ?_⟩, ht.1⟩
  simp only [List.map_id_fun, Option.map_some]
  change Runs (compile p id none) (some (entry p)) (ioStore input initial (ea a))
    none (ioStore output initial (eb (f a))) t
  exact compile_correct ht.2 (compile p id none) id none (fun _ => rfl)

end Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
