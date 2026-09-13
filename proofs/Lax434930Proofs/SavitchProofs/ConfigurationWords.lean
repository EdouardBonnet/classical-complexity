import Lax434930Proofs.SavitchProofs.FiniteCoding
import Lax434930Proofs.SavitchProofs.TapeZipper
import Lax434930Proofs.SavitchDefinitions.BoundedConfigurations

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ConfigurationWords

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open scoped Classical

noncomputable section

inductive Payload (M : Machine) where
  | header (state : M.Q) (input : InputSymbol)
  | bit (value : Bool)
  | split
  | cell (value : M.Γ) (head : Bool)
  | invalid
  deriving Fintype

instance (M : Machine) : Inhabited (Payload M) := ⟨.invalid⟩

abbrev Letter (M : Machine) := FiniteCoding.Letter (Payload M)

def header (M : Machine) (q : M.Q) (i : InputSymbol) : Letter M := .inr (.header q i)
def bit (M : Machine) (b : Bool) : Letter M := .inr (.bit b)
def split (M : Machine) : Letter M := .inr .split
def cell (M : Machine) (g : M.Γ) (h : Bool) : Letter M := .inr (.cell g h)

def row (M : Machine) (left : List M.Γ) (current : M.Γ) (right : List M.Γ) : List (Letter M) :=
  left.map (fun g => cell M g false) ++ cell M current true :: right.map (fun g => cell M g false)

def configuration (M : Machine) (q : M.Q) (i : InputSymbol) (input : List Bool)
    (left : List M.Γ) (current : M.Γ) (right : List M.Γ) : List (Letter M) :=
  header M q i :: (input.map (bit M) ++ split M :: row M left current right)

def view (M : Machine) (q : M.Q) (input : List Bool) (left : List M.Γ) (current : M.Γ) (right : List M.Γ) :
    TapeZipper.View M := ⟨q, BinaryCounter.value input, left.reverse, current, right⟩

@[simp] lemma view_tape (M : Machine) (q : M.Q) (input : List Bool) (left : List M.Γ) (current : M.Γ) (right) :
    (view M q input left current right).expand.tape = TapeZipper.contents M (left ++ current :: right) := by
  simp [view, TapeZipper.View.expand, TapeZipper.View.word]

@[simp] lemma view_head (M : Machine) (q : M.Q) (input : List Bool) (left : List M.Γ) (current : M.Γ) (right) :
    (view M q input left current right).expand.workHead = left.length := by simp [view, TapeZipper.View.expand]

@[simp] lemma row_length (M : Machine) (left : List M.Γ) (current : M.Γ) (right) :
    (row M left current right).length = left.length + 1 + right.length := by simp [row]; omega

@[simp] lemma configuration_length (M : Machine) (q : M.Q) (i : InputSymbol) (input : List Bool)
    (left : List M.Γ) (current : M.Γ) (right) :
    (configuration M q i input left current right).length = input.length + left.length + right.length + 3 := by
  simp [configuration]; omega

def inputBits (M : Machine) (xs : List (Letter M)) : List Bool :=
  match xs.head? with
  | some (.inr (.header _ _)) =>
      (xs.tail.takeWhile (fun x => decide (x ≠ split M))).map
        (fun x => match x with | .inr (.bit b) => b | _ => false)
  | _ => []

def desiredInput (M : Machine) (xs : List (Letter M)) : InputSymbol :=
  match xs.head? with
  | some (.inr (.header _ i)) => i
  | _ => .leftEnd

def ValidInput (M : Machine) (w : Word) (xs : List (Letter M)) : Prop :=
  BinaryCounter.value (inputBits M xs) ≤ w.length + 1 ∧
    readInput w (BinaryCounter.value (inputBits M xs)) = desiredInput M xs

lemma take_input (M : Machine) (input : List Bool) (tail : List (Letter M)) :
    ((input.map (bit M) ++ split M :: tail).takeWhile (fun x => decide (x ≠ split M))) = input.map (bit M) := by
  induction input with
  | nil => simp
  | cons b input ih => simpa [bit, split] using ih

@[simp] lemma inputBits_configuration (M : Machine) (q : M.Q) (i : InputSymbol) (input : List Bool)
    (left : List M.Γ) (current : M.Γ) (right) :
    inputBits M (configuration M q i input left current right) = input := by
  simp only [inputBits, configuration, header, List.head?_cons, List.tail_cons]
  rw [take_input]
  simp [List.map_map, bit, Function.comp_def]

@[simp] lemma desiredInput_configuration (M : Machine) (q : M.Q) (i : InputSymbol) (input : List Bool)
    (left : List M.Γ) (current : M.Γ) (right) :
    desiredInput M (configuration M q i input left current right) = i := rfl

lemma input_width (n s : ℕ) (h : logSpace n ≤ s) : n + 2 < 2 ^ (s + 1) := by
  exact (Nat.lt_log2_self (n := n + 2)).trans_le (Nat.pow_le_pow_right (by omega) (by
    change (n + 2).log2 + 1 ≤ s + 1
    simpa [logSpace, Nat.log2_eq_log_two] using Nat.add_le_add_right h 1))

def cellValue (M : Machine) : Letter M → M.Γ
  | .inr (.cell g _) => g
  | _ => M.blank

lemma row_injective (M : Machine) (left : List M.Γ) (current : M.Γ) (right : List M.Γ)
    (left' : List M.Γ) (current' : M.Γ) (right' : List M.Γ)
    (h : row M left current right = row M left' current' right') :
    left = left' ∧ current = current' ∧ right = right' := by
  induction left generalizing left' with
  | nil =>
    cases left' with
    | nil =>
      simp only [row, List.map_nil, List.nil_append, List.cons.injEq, cell, Sum.inr.injEq,
        Payload.cell.injEq, and_true] at h
      refine ⟨rfl, h.1, ?_⟩
      have hr := congrArg (List.map (cellValue M)) h.2
      simpa [List.map_map, cellValue, Function.comp_def] using hr
    | cons g left' => simp [row, cell] at h
  | cons g left ih =>
    cases left' with
    | nil => simp [row, cell] at h
    | cons g' left' =>
      simp only [row, List.map_cons, List.cons_append, List.cons.injEq] at h
      have hg : g = g' := by simpa [cell] using h.1
      have ht := ih left' h.2
      exact ⟨by simp [hg, ht.1], ht.2⟩

lemma configuration_injective (M : Machine) (q q' : M.Q) (i i' : InputSymbol) (input input' : List Bool)
    (left : List M.Γ) (current : M.Γ) (right : List M.Γ)
    (left' : List M.Γ) (current' : M.Γ) (right' : List M.Γ)
    (h : configuration M q i input left current right = configuration M q' i' input' left' current' right') :
    q = q' ∧ i = i' ∧ input = input' ∧ left = left' ∧ current = current' ∧ right = right' := by
  have hh := congrArg List.head? h
  simp only [configuration, List.head?_cons, Option.some.injEq, header, Sum.inr.injEq, Payload.header.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  have hi := congrArg (inputBits M) h
  simp only [inputBits_configuration] at hi
  subst input'
  have hr : row M left current right = row M left' current' right' := by simpa [configuration] using h
  exact ⟨rfl, rfl, rfl, row_injective M left current right left' current' right' hr⟩

def Represents (M : Machine) (xs : List (Letter M)) (c : M.Config) : Prop :=
  ∃ q i input left current right,
    xs = configuration M q i input left current right ∧ c = (view M q input left current right).expand

lemma representation_unique (M : Machine) (xs : List (Letter M)) (c d : M.Config)
    (hc : Represents M xs c) (hd : Represents M xs d) : c = d := by
  obtain ⟨q, i, input, left, current, right, hx, rfl⟩ := hc
  obtain ⟨q', i', input', left', current', right', hy, rfl⟩ := hd
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    configuration_injective M q q' i i' input input' left current right left' current' right' (hx.symm.trans hy)
  rfl

end

end Lax434930Proofs.SavitchProofs.ConfigurationWords
