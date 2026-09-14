import Lax434930Proofs.InclusionAux.CommandEmbedding
import Lax434930Proofs.StackSpaceInterpreter

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.VerifierRoutine

open Turing Lax434930.PolynomialTime
open Lax434930Proofs
open SavitchProofs.StackLanguage
open scoped Classical

noncomputable section

attribute [local instance] FinTM2.ΛFin

variable {f : Word → Bool} (M : TM2ComputableInPolyTime id Computability.encodeBool f)

abbrev Alphabet := HomogeneousStacks.Alphabet M.tm.Γ
abbrev Control := StackSpaceInterpreter.Control (Alphabet M) M.tm.Λ M.tm.σ

def inputSymbol (b : Bool) : Alphabet M := HomogeneousStacks.symbol M.tm.k₀ (M.inputAlphabet.symm b)
def outputSymbol (b : Bool) : Alphabet M := HomogeneousStacks.symbol M.tm.k₁ (M.outputAlphabet.symm b)

def inputRead (g : Alphabet M) : Bool := ((HomogeneousStacks.readSymbol M.tm.k₀ g).map M.inputAlphabet).getD false
def outputRead (g : Alphabet M) : Bool := ((HomogeneousStacks.readSymbol M.tm.k₁ g).map M.outputAlphabet).getD false

@[simp] lemma input_read (b : Bool) : inputRead M (inputSymbol M b) = b := by
  simp [inputRead, inputSymbol]

@[simp] lemma output_read (b : Bool) : outputRead M (outputSymbol M b) = b := by
  simp [outputRead, outputSymbol]

def initial (xs : Word) : TM2.Cfg (fun _ : M.tm.K => Alphabet M) M.tm.Λ M.tm.σ :=
  HomogeneousStacks.cfg (initList M.tm (xs.map M.inputAlphabet.symm))

def finalCfg (b : Bool) : TM2.Cfg (fun _ : M.tm.K => Alphabet M) M.tm.Λ M.tm.σ :=
  HomogeneousStacks.cfg (haltList M.tm [M.outputAlphabet.symm b])

lemma initial_stack (xs : Word) (k : M.tm.K) :
    (initial M xs).stk k = if k = M.tm.k₀ then xs.map (inputSymbol M) else [] := by
  by_cases hk : k = M.tm.k₀
  · subst k
    simp [initial, HomogeneousStacks.cfg, HomogeneousStacks.encodedStore,
      initList, inputSymbol, List.map_map, Function.comp_def]
  · simp [initial, HomogeneousStacks.cfg, HomogeneousStacks.encodedStore, initList, hk]

lemma final_stack (b : Bool) : (finalCfg M b).stk M.tm.k₁ = [outputSymbol M b] := by
  simp [finalCfg, HomogeneousStacks.cfg, HomogeneousStacks.encodedStore, haltList, outputSymbol]

variable {J τ : Type}

def instructions (l : M.tm.Λ) : TM2.Stmt (fun _ : M.tm.K => Alphabet M) M.tm.Λ M.tm.σ :=
  @HomogeneousStacks.statement M.tm.K M.tm.Λ M.tm.σ M.tm.Γ
    (fun a b => Classical.propDecidable (a = b)) (M.tm.m l)

def code (keys : CommandEmbedding.KeyMap M.tm.K J) (state : Control M → τ) (readState : τ → Control M) :
    Command J (Alphabet M) τ :=
  CommandEmbedding.command keys id id state readState
    (StackSpaceInterpreter.program (instructions M)
      Finset.univ.toList)

def point (keys : CommandEmbedding.KeyMap M.tm.K J) (state : Control M → τ)
    (frame : J → List (Alphabet M))
    (c : TM2.Cfg (fun _ : M.tm.K => Alphabet M) M.tm.Λ M.tm.σ) (i : ℕ) :
    Data J (Alphabet M) τ :=
  CommandEmbedding.data keys id state frame (StackSpaceInterpreter.encode c i)

def initialControl : Control M := ⟨some M.tm.main, M.tm.initialState, none⟩

lemma point_initial (keys : CommandEmbedding.KeyMap M.tm.K J) (state : Control M → τ)
    (xs : Word) (d : Data J (Alphabet M) τ)
    (h : ∀ k, d.store (keys.key k) = (initial M xs).stk k) :
    point M keys state d.store (initial M xs) d.inputHead =
      assigned d (state (initialControl M)) := by
  dsimp [point, CommandEmbedding.data, StackSpaceInterpreter.encode, assigned]
  congr 1
  funext j
  cases hr : keys.read j with
  | none => simp [CommandEmbedding.store, hr]
  | some k =>
    have hk := keys.key_read j k hr
    simp only [CommandEmbedding.store, hr, List.map_id_fun, List.map_id]
    exact (hk ▸ h k).symm

lemma point_output (keys : CommandEmbedding.KeyMap M.tm.K J) (state : Control M → τ)
    (frame : J → List (Alphabet M)) (b : Bool) (i : ℕ) :
    (point M keys state frame (finalCfg M b) i).store (keys.key M.tm.k₁) =
      [outputSymbol M b] := by
  simp [point, CommandEmbedding.data, StackSpaceInterpreter.encode,
    StackSpaceInterpreter.view, final_stack]

lemma execution (keys : CommandEmbedding.KeyMap M.tm.K J) (state : Control M → τ)
    (readState : τ → Control M) (hstate : ∀ s, readState (state s) = s)
    (frame : J → List (Alphabet M)) (w xs : Word) (bound i : ℕ)
    (hi : i ≤ w.length + 1)
    (hf : ∀ j, keys.read j = none → (frame j).length < bound)
    (hb : xs.length + TM2Bounds.factor M.tm * M.time.eval xs.length < bound) :
    Exec w bound (code M keys state readState)
      (point M keys state frame (initial M xs) i)
      (point M keys state frame (finalCfg M (f xs)) i) := by
  let h := M.outputsFun xs
  have hr : Time.Run (TM2.step M.tm.m) h.steps
      (initList M.tm (xs.map M.inputAlphabet.symm))
      (haltList M.tm [M.outputAlphabet.symm (f xs)]) := by
    exact Time.Run.of_iterate h.evals_in_steps
  have hmap := HomogeneousStacks.run_correct M.tm.m hr
  have hdec : M.tm.decidableEqK = (fun a b => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hmap
  have hbound : ∀ k, ((initial M xs).stk k).length + TM2Bounds.factor M.tm * h.steps < bound := by
    intro k
    have hlen : ((initial M xs).stk k).length ≤ xs.length := by
      rw [initial_stack]
      split <;> simp
    have ht : h.steps ≤ M.time.eval xs.length := h.steps_le_m
    exact (Nat.add_le_add hlen (Nat.mul_le_mul_left _ ht)).trans_lt hb
  have he := StackSpaceInterpreter.run_execution
    (instructions M) Finset.univ.toList
    (by intro l; simp) (TM2Bounds.factor M.tm)
    (fun l => by simp only [instructions, HomogeneousStacks.pushes_statement]; exact TM2Bounds.pushes_le_factor M.tm l)
    w bound i hi (n := h.steps) (c := initial M xs) (d := finalCfg M (f xs)) hmap rfl hbound
  exact CommandEmbedding.execution keys id id state readState (fun _ => rfl) hstate
    frame w bound hf he

end

end Lax434930Proofs.InclusionAux.VerifierRoutine
