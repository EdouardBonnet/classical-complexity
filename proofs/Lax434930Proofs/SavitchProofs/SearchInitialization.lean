import Lax434930Proofs.SavitchProofs.GraphQuery
import Lax434930Proofs.SavitchProofs.UnaryExpansion

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.GraphQuery

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open ConfigurationWords
open StackLanguage (Good Exec assigned)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine) (BΓ : Type)

local infixr:55 " ⋙ₘ " => Macro.seq

def finishInitialization : GraphQuery.Macro M BΓ :=
  Macro.copy (SearchProgram.key .width) (SearchProgram.key .depth) (key .aux) ⋙ₘ
    Macro.copyMap (SearchProgram.key .width) (SearchProgram.key .a) (key .aux) (fun _ => SearchProgram.bit false) ⋙ₘ
    Macro.copyMap (SearchProgram.key .width) (SearchProgram.key .b) (key .aux) (fun _ => SearchProgram.bit true) ⋙ₘ
    Macro.assign (fun s => {s with user := {s.user with phase := .call}})

lemma finishInitialization_spec (w : Word) (bound m : ℕ) (d : Data M BΓ)
    (haux : d.store (key .aux) = [])
    (hready : ∀ r, d.store (SearchProgram.key r) = if r = .width then SearchProgram.unary m else []) :
    (finishInitialization M BΓ).guard w bound d ∧
      SearchProgram.Fits m (.call m (EncodedGraph.first m) (EncodedGraph.last m) [])
        ((finishInitialization M BΓ).result w d) := by
  have ha : d.store (.inr Scratch.aux) = [] := haux
  have hr (r : SearchProgram.Register) :
      d.store (.inl r) = if r = .width then SearchProgram.unary m else [] := hready r
  constructor
  · simp [finishInitialization, Macro.seq, Macro.copy, Macro.copyMap, Macro.assign, key, SearchProgram.key, ha]
  · refine ⟨rfl, ?_, trivial⟩
    intro r
    cases r <;>
      simp [finishInitialization, Macro.seq, Macro.copy, Macro.copyMap, Macro.assign, assigned,
        key, SearchProgram.key, hr, SearchProgram.store, SearchProgram.stackStore,
        SearchProgram.column, SearchProgram.unary, SearchProgram.word, EncodedGraph.first, EncodedGraph.last,
        BinaryCounter.word_zero, BinaryCounter.word_ones]

def initializeSearch : GraphQuery.Macro M BΓ :=
  Macro.copyMap (key .constructorLeft) (key .bound) (key .aux) (fun _ => SearchProgram.symbol .tally) ⋙ₘ
    Macro.appendCopies (key .bound) (SearchProgram.key .width) (key .aux) (2 * FiniteCoding.width (Payload M)) ⋙ₘ
    Macro.putWord (SearchProgram.key .width) (SearchProgram.unary (5 * FiniteCoding.width (Payload M))) ⋙ₘ
    finishInitialization M BΓ

lemma initialize_spec (w : Word) (bound : ℕ) (d : Data M BΓ)
    (haux : d.store (key .aux) = [])
    (hmain : ∀ r, d.store (SearchProgram.key r) = [])
    (hbound : FiniteCoding.width (Payload M) * (2 * ((d.store (key .constructorLeft)).length + 1) + 3) < bound) :
    let m := FiniteCoding.width (Payload M) * (2 * ((d.store (key .constructorLeft)).length + 1) + 3)
    (initializeSearch M BΓ).guard w bound d ∧
      SearchProgram.Fits m (.call m (EncodedGraph.first m) (EncodedGraph.last m) [])
        ((initializeSearch M BΓ).result w d) := by
  let r := FiniteCoding.width (Payload M)
  let len := (d.store (key .constructorLeft)).length
  let m := r * (2 * (len + 1) + 3)
  have hm : 2 * r * len + 5 * r = m := by dsimp [m]; ring
  let d0 := (Macro.copyMap (key .constructorLeft) (key .bound) (key .aux)
    (fun _ => SearchProgram.symbol .tally)).result w d
  have g0 : (Macro.copyMap (key .constructorLeft) (key .bound) (key .aux)
      (fun _ => SearchProgram.symbol .tally)).guard w bound d := by
    have ha : d.store (.inr Scratch.aux) = [] := haux
    simp [Macro.copyMap, key, ha]
  have h0src : d0.store (key .bound) = List.replicate len (SearchProgram.symbol .tally) := by
    simp [d0, Macro.copyMap, len, List.map_const']
  have h0aux : d0.store (key .aux) = [] := by
    dsimp [d0, Macro.copyMap]
    simpa [key] using haux
  have h0main (q : SearchProgram.Register) : d0.store (SearchProgram.key q) = [] := by
    dsimp [d0, Macro.copyMap]
    simpa [key, SearchProgram.key] using hmain q
  have hcopyBound : (2 * r) * len + (d0.store (SearchProgram.key .width)).length < bound := by
    rw [h0main]
    simp only [List.length_nil, Nat.add_zero]
    change m < bound at hbound
    omega
  obtain ⟨g1, h1⟩ := Macro.appendCopies_spec w bound (key .bound) (SearchProgram.key .width) (key .aux)
    (by simp [key, SearchProgram.key]) (by decide) (by simp [key, SearchProgram.key])
    (SearchProgram.symbol .tally) (2 * r) len d0 h0src h0aux hcopyBound
  let d1 := (Macro.appendCopies (key .bound) (SearchProgram.key .width) (key .aux) (2 * r)).result w d0
  change d1 = _ at h1
  have h1width : d1.store (SearchProgram.key .width) = SearchProgram.unary (2 * r * len) := by
    rw [h1]
    simp [h0main, SearchProgram.unary]
  let d2 := (Macro.putWord (SearchProgram.key .width) (SearchProgram.unary (5 * r))).result w d1
  have g2 : (Macro.putWord (SearchProgram.key .width) (SearchProgram.unary (5 * r))).guard w bound d1 := by
    simp only [Macro.putWord, SearchProgram.unary_length, h1width]
    change m < bound at hbound
    omega
  have h2width : d2.store (SearchProgram.key .width) = SearchProgram.unary m := by
    simp only [d2, Macro.putWord, Function.update_self, h1width, SearchProgram.unary]
    rw [← List.replicate_add]
    congr 1
    omega
  have h2aux : d2.store (key .aux) = [] := by
    dsimp only [d2, Macro.putWord]
    rw [h1]
    simpa [key, SearchProgram.key] using h0aux
  have hready (q : SearchProgram.Register) :
      d2.store (SearchProgram.key q) = if q = .width then SearchProgram.unary m else [] := by
    by_cases hq : q = .width
    · subst q
      simpa using h2width
    · dsimp only [d2, Macro.putWord]
      rw [h1]
      simpa [Function.update_apply, SearchProgram.key, hq] using h0main q
  obtain ⟨g3, h3⟩ := finishInitialization_spec M BΓ w bound m d2 h2aux hready
  exact ⟨⟨g0, g1, g2, g3⟩, h3⟩

end

end Lax434930Proofs.SavitchProofs.GraphQuery
