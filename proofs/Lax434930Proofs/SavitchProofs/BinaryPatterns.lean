import Lax434930Proofs.SavitchProofs.TapePatterns
import Lax434930Proofs.SavitchProofs.InputRoutines

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ConfigurationWords

open Lax434930.PolynomialTime Lax434930.SpaceMachines PatternAutomata
open scoped Classical

noncomputable section

inductive InputChange where
  | same | up | down
  deriving DecidableEq, Fintype

def sameBit (M : Machine) (b : Bool) : Letter M × Letter M := (bit M b, bit M b)

def inputPattern (M : Machine) : InputChange → Pattern (Letter M × Letter M)
  | .same => [.star (Set.range (sameBit M))]
  | .up => [.star {(bit M true, bit M false)}, .one {(bit M false, bit M true)},
      .star (Set.range (sameBit M))]
  | .down => [.star {(bit M false, bit M true)}, .one {(bit M true, bit M false)},
      .star (Set.range (sameBit M))]

def InputRelation : InputChange → ℕ → ℕ → Prop
  | .same, n, n' => n' = n
  | .up, n, n' => n' = n + 1
  | .down, n, n' => n = n' + 1

lemma inputPattern_same (M : Machine) (xs : List (Letter M × Letter M)) :
    Matches (inputPattern M .same) xs ↔ ∃ bits : List Bool, xs = bits.map (sameBit M) := by
  simp only [inputPattern, matches_star_range, matches_empty]
  simp

lemma inputPattern_up (M : Machine) (xs : List (Letter M × Letter M)) :
    Matches (inputPattern M .up) xs ↔ ∃ (n : ℕ) (bits : List Bool),
      xs = List.replicate n (bit M true, bit M false) ++ (bit M false, bit M true) :: bits.map (sameBit M) := by
  simp only [inputPattern, matches_star_single, matches_one_single, matches_star_range, matches_empty]
  simp

lemma inputPattern_down (M : Machine) (xs : List (Letter M × Letter M)) :
    Matches (inputPattern M .down) xs ↔ ∃ (n : ℕ) (bits : List Bool),
      xs = List.replicate n (bit M false, bit M true) ++ (bit M true, bit M false) :: bits.map (sameBit M) := by
  simp only [inputPattern, matches_star_single, matches_one_single, matches_star_range, matches_empty]
  simp

lemma increment_prefix (n : ℕ) (xs : List Bool) :
    BinaryCounter.increment (List.replicate n true ++ false :: xs) = List.replicate n false ++ true :: xs := by
  induction n <;> simp [List.replicate_succ, BinaryCounter.increment, *]

lemma carry_prefix (n : ℕ) (xs : List Bool) :
    BinaryCounter.carry (List.replicate n true ++ false :: xs) = false := by
  induction n <;> simp [List.replicate_succ, BinaryCounter.carry, *]

lemma value_prefix (n : ℕ) (xs : List Bool) :
    BinaryCounter.value (List.replicate n false ++ true :: xs) =
      BinaryCounter.value (List.replicate n true ++ false :: xs) + 1 := by
  have h := BinaryCounter.increment_value (List.replicate n true ++ false :: xs)
  simpa [increment_prefix, carry_prefix] using h

lemma inputPattern_sound (M : Machine) (change : InputChange) (xs : List (Letter M × Letter M))
    (h : Matches (inputPattern M change) xs) :
    ∃ input input' : List Bool, xs.map Prod.fst = input.map (bit M) ∧ xs.map Prod.snd = input'.map (bit M) ∧
      InputRelation change (BinaryCounter.value input) (BinaryCounter.value input') := by
  cases change with
  | same =>
    obtain ⟨input, rfl⟩ := (inputPattern_same M xs).mp h
    exact ⟨input, input, by simp [sameBit, List.map_map, Function.comp_def],
      by simp [sameBit, List.map_map, Function.comp_def], rfl⟩
  | up =>
    obtain ⟨n, bits, rfl⟩ := (inputPattern_up M xs).mp h
    exact ⟨List.replicate n true ++ false :: bits, List.replicate n false ++ true :: bits,
      by simp [sameBit, List.map_map, Function.comp_def],
      by simp [sameBit, List.map_map, Function.comp_def], value_prefix n bits⟩
  | down =>
    obtain ⟨n, bits, rfl⟩ := (inputPattern_down M xs).mp h
    exact ⟨List.replicate n false ++ true :: bits, List.replicate n true ++ false :: bits,
      by simp [sameBit, List.map_map, Function.comp_def],
      by simp [sameBit, List.map_map, Function.comp_def], value_prefix n bits⟩

lemma zero_split (xs : List Bool) (h : BinaryCounter.carry xs = false) :
    ∃ n tail, xs = List.replicate n true ++ false :: tail := by
  induction xs with
  | nil => simp [BinaryCounter.carry] at h
  | cons b xs ih =>
    cases b with
    | false => exact ⟨0, xs, rfl⟩
    | true =>
      obtain ⟨n, tail, rfl⟩ := ih h
      exact ⟨n + 1, tail, by simp [List.replicate_succ]⟩

lemma inputPattern_complete (M : Machine) (change : InputChange) (k n n' : ℕ)
    (hn : n < 2 ^ k) (hn' : n' < 2 ^ k) (h : InputRelation change n n') :
    Matches (inputPattern M change)
      (List.zip ((BinaryCounter.word k n).map (bit M)) ((BinaryCounter.word k n').map (bit M))) := by
  cases change with
  | same =>
    subst n'
    let pairs := (BinaryCounter.word k n).map (sameBit M)
    have hp := zip_projections pairs
    simp only [pairs, List.map_map, sameBit, Function.comp_def] at hp
    rw [hp]
    exact (inputPattern_same M _).mpr ⟨_, rfl⟩
  | up =>
    change n' = n + 1 at h
    subst n'
    have hc : BinaryCounter.carry (BinaryCounter.word k n) = false := by
      rw [BinaryCounter.word_carry k n hn]
      simp [show n + 1 ≠ 2 ^ k by omega]
    obtain ⟨j, tail, hs⟩ := zero_split _ hc
    have ht : BinaryCounter.word k (n + 1) = List.replicate j false ++ true :: tail := by
      rw [← BinaryCounter.word_increment, hs, increment_prefix]
    let pairs := List.replicate j (bit M true, bit M false) ++ (bit M false, bit M true) :: tail.map (sameBit M)
    have hp := zip_projections pairs
    simp only [pairs, List.map_append, List.map_replicate, List.map_cons, List.map_map,
      sameBit, Function.comp_def] at hp
    rw [hs, ht]
    simp only [List.map_append, List.map_replicate, List.map_cons]
    rw [hp]
    exact (inputPattern_up M _).mpr ⟨j, tail, rfl⟩
  | down =>
    change n = n' + 1 at h
    subst n
    have hc : BinaryCounter.carry (BinaryCounter.word k n') = false := by
      rw [BinaryCounter.word_carry k n' hn']
      simp [show n' + 1 ≠ 2 ^ k by omega]
    obtain ⟨j, tail, hs⟩ := zero_split _ hc
    have ht : BinaryCounter.word k (n' + 1) = List.replicate j false ++ true :: tail := by
      rw [← BinaryCounter.word_increment, hs, increment_prefix]
    let pairs := List.replicate j (bit M false, bit M true) ++ (bit M true, bit M false) :: tail.map (sameBit M)
    have hp := zip_projections pairs
    simp only [pairs, List.map_append, List.map_replicate, List.map_cons, List.map_map,
      sameBit, Function.comp_def] at hp
    rw [hs, ht]
    simp only [List.map_append, List.map_replicate, List.map_cons]
    rw [hp]
    exact (inputPattern_down M _).mpr ⟨j, tail, rfl⟩

def inputChange : Move → InputSymbol → InputChange
  | .stay, _ => .same
  | .left, .leftEnd => .same
  | .left, _ => .down
  | .right, .rightEnd => .same
  | .right, _ => .up

lemma inputChange_iff (w : Word) (direction : Move) (n n' : ℕ)
    (hn : n ≤ w.length + 1) (hn' : n' ≤ w.length + 1) :
    InputRelation (inputChange direction (readInput w n)) n n' ↔
      n' = min (direction.apply n) (w.length + 1) := by
  cases direction with
  | stay => simp [inputChange, InputRelation, Move.apply, Nat.min_eq_left hn]
  | left =>
    cases hi : readInput w n with
    | leftEnd =>
      have hz := (InputRoutines.read_left w n).mp hi
      simp [inputChange, InputRelation, Move.apply, hz]
    | bit b =>
      have hz : n ≠ 0 := by intro hz; simp [hz, readInput] at hi
      simp only [inputChange, InputRelation, Move.apply]
      rw [Nat.min_eq_left (by omega)]
      omega
    | rightEnd =>
      have hz : n ≠ 0 := by intro hz; simp [hz, readInput] at hi
      simp only [inputChange, InputRelation, Move.apply]
      rw [Nat.min_eq_left (by omega)]
      omega
  | right =>
    cases hi : readInput w n with
    | leftEnd =>
      have hz := (InputRoutines.read_left w n).mp hi
      simp [inputChange, InputRelation, Move.apply, hz]
    | bit b =>
      have he : n < w.length + 1 := by
        by_contra h
        have hh := (InputRoutines.read_right w n).mpr (by omega)
        simp [hi] at hh
      simp [inputChange, InputRelation, Move.apply, Nat.min_eq_left (show n + 1 ≤ w.length + 1 by omega)]
    | rightEnd =>
      have he := (InputRoutines.read_right w n).mp hi
      have hh : n = w.length + 1 := by omega
      simp [inputChange, InputRelation, Move.apply, hh]

end

end Lax434930Proofs.SavitchProofs.ConfigurationWords
