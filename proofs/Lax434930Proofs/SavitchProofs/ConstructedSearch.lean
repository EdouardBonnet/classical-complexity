import Lax434930Proofs.SavitchProofs.SearchInitialization
import Lax434930Proofs.SavitchProofs.ProgramComposition
import Lax434930Proofs.SavitchProofs.TapeInterpreter
import Lax434930Proofs.SavitchDefinitions.SpaceConstructibility

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ConstructedSearch

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open ConfigurationWords GraphQuery
open scoped Classical

noncomputable section

def constructorSymbol (M B : Machine) (g : B.Γ) : GraphQuery.Alphabet M B.Γ := .inl (.inl g)

def readConstructor (M B : Machine) : Option (GraphQuery.Alphabet M B.Γ) → B.Γ
  | some (.inl (.inl g)) => g
  | _ => B.blank

def constructor (M B : Machine) : StackMachine.Program GraphQuery.Key (GraphQuery.Alphabet M B.Γ) (TapeInterpreter.Control B) :=
  TapeInterpreter.program B (key .constructorLeft) (key .constructorRight) (constructorSymbol M B) (readConstructor M B)

def initial (M B : Machine) : GraphQuery.Context M B.Γ :=
  ⟨⟨.call, false, false, GraphQuery.initial M⟩, none, false, .leftEnd, none⟩

def command (M B : Machine) : SearchProgram.Code (GraphQuery.Beta M B.Γ) (GraphQuery.State M) GraphQuery.Scratch :=
  .seq (initializeSearch M B.Γ).code (SearchProgram.search (procedure M B.Γ))

def machine (M B : Machine) : Machine :=
  ProgramComposition.machine (constructor M B) (command M B) (initial M B) (fun s => s.user.answer)

lemma deterministic (M B : Machine) : (machine M B).Deterministic := StackMachine.deterministic _

def encodingWidth (M : Machine) (s : ℕ) : ℕ := FiniteCoding.width (Payload M) * ((s + 1) + s + 2)

def spaceConstant (M : Machine) : ℕ := (5 * FiniteCoding.width (Payload M) + 2) ^ 2

lemma spaceConstant_pos (M : Machine) : 0 < spaceConstant M := by unfold spaceConstant; positivity

lemma width_pos (M : Machine) (s : ℕ) : 0 < encodingWidth M s :=
  Nat.mul_pos (FiniteCoding.width_pos _) (by omega)

lemma constructor_bound (M : Machine) (s : ℕ) : s + 1 ≤ SearchProgram.budget (encodingWidth M s) := by
  have hr := FiniteCoding.width_pos (Payload M)
  have hh := Nat.mul_le_mul_right ((s + 1) + s + 2) (show 1 ≤ FiniteCoding.width (Payload M) by omega)
  simp only [Nat.one_mul] at hh
  change (s + 1) + s + 2 ≤ encodingWidth M s at hh
  dsimp only [SearchProgram.budget]
  nlinarith

lemma quadratic (M : Machine) (s : ℕ) (hs : 0 < s) :
    SearchProgram.budget (encodingWidth M s) ≤ spaceConstant M * s ^ 2 := by
  have hh : encodingWidth M s ≤ 5 * FiniteCoding.width (Payload M) * s := by
    have h : (s + 1) + s + 2 ≤ 5 * s := by omega
    simpa [encodingWidth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left (FiniteCoding.width (Payload M)) h
  have h : encodingWidth M s + 2 ≤ (5 * FiniteCoding.width (Payload M) + 2) * s := by nlinarith
  calc
    SearchProgram.budget (encodingWidth M s) ≤ ((5 * FiniteCoding.width (Payload M) + 2) * s) ^ 2 :=
      Nat.pow_le_pow_left h 2
    _ = spaceConstant M * s ^ 2 := by unfold spaceConstant; ring

lemma execution (M B : Machine) (w : Word) (s : ℕ) (hdet : B.Deterministic)
    (hBspace : B.UsesSpace w s)
    (hBterminal : ∃ n c, B.Run w n c ∧ B.Terminal w c ∧ c.workHead + 1 = s)
    (hlog : logSpace w.length ≤ s) (hMspace : M.UsesSpace w s) :
    (machine M B).HaltsOn w ∧ (machine M B).UsesSpace w (SearchProgram.budget (encodingWidth M s)) ∧
      ((machine M B).Accepts w ↔ M.Accepts w) := by
  obtain ⟨v, _, hlen, hstop, t, hpath⟩ := TapeInterpreter.constructor_run B
    (key .constructorLeft) (key .constructorRight) (constructorSymbol M B) (readConstructor M B)
    (by decide) rfl (by intro g; rfl) hdet w s hBspace hBterminal
  let p := TapeInterpreter.encode B (key .constructorLeft) (key .constructorRight) (constructorSymbol M B) v
  let m := encodingWidth M s
  have hgood : StackMachine.Good w (s + 1) p :=
    ProgramComposition.path_good (constructor M B) w hpath (by
      constructor
      · exact Nat.zero_le _
      · intro k
        simp [StackMachine.Program.initial])
  have hpath' : ∃ n, MachinePaths.Path (StackMachine.SafeStep (constructor M B) w (SearchProgram.budget m)) n
      (constructor M B).initial p :=
    ⟨t, ProgramComposition.path_mono (constructor M B) w (constructor_bound M s) hpath⟩
  let d : GraphQuery.Data M B.Γ := ⟨initial M B, p.inputHead, p.store⟩
  have hd : StackLanguage.Good w (SearchProgram.budget m) d :=
    ⟨hgood.1, fun k => (hgood.2 k).trans_le (constructor_bound M s)⟩
  have haux : d.store (key .aux) = [] := by
    simp [d, p, TapeInterpreter.encode, TapeInterpreter.point, TapeInterpreter.memory, key]
  have hmain (r : SearchProgram.Register) : d.store (SearchProgram.key r) = [] := by
    simp [d, p, TapeInterpreter.encode, TapeInterpreter.point, TapeInterpreter.memory, key, SearchProgram.key]
  have hleft : (d.store (key .constructorLeft)).length + 1 = s := by
    simpa [d, p, TapeInterpreter.encode, TapeInterpreter.point, TapeInterpreter.memory, key] using hlen
  have hwidth : FiniteCoding.width (Payload M) * (2 * ((d.store (key .constructorLeft)).length + 1) + 3) = m := by
    rw [hleft]
    dsimp [m, encodingWidth]
    congr 1
    omega
  have hmBound : m < SearchProgram.budget m := by unfold SearchProgram.budget; nlinarith
  have hinit := initialize_spec M B.Γ w (SearchProgram.budget m) d haux hmain (by rw [hwidth]; exact hmBound)
  dsimp only at hinit
  rw [hwidth] at hinit
  have hi := (initializeSearch M B.Γ).correct w (SearchProgram.budget m) d hd hinit.1
  obtain ⟨e, he, _, hanswer⟩ := SearchProgram.search_call (procedure M B.Γ) (EncodedGraph.graph M)
    (query_correct M B.Γ) w m (EncodedGraph.first m) (EncodedGraph.last m) _ hi.good.2 hinit.2
  have hc : StackLanguage.Exec w (SearchProgram.budget m) (command M B) d e := .seq hi he
  have hresult := ProgramComposition.execution (constructor M B) (command M B) (initial M B)
    (fun q => q.user.answer) w (SearchProgram.budget m) (by unfold SearchProgram.budget; positivity)
    p e hpath' hstop hc
  refine ⟨hresult.1, hresult.2.1, hresult.2.2.trans ?_⟩
  change e.state.user.answer = true ↔ _
  rw [hanswer]
  exact EncodedGraph.search_correct M w (s + 1) s ((input_width w.length s hlog).trans' (by omega)) hMspace

end

end Lax434930Proofs.SavitchProofs.ConstructedSearch
