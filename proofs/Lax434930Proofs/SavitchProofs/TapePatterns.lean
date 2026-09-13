import Lax434930Proofs.SavitchProofs.ConfigurationWords
import Lax434930Proofs.SavitchProofs.PatternAutomata

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ConfigurationWords

open Lax434930.SpaceMachines PatternAutomata
open scoped Classical

noncomputable section

def quiet (M : Machine) (g : M.Γ) : Letter M × Letter M := (cell M g false, cell M g false)
def entering (M : Machine) (g : M.Γ) : Letter M × Letter M := (cell M g false, cell M g true)

def stayPattern (M : Machine) (read write : M.Γ) : Pattern (Letter M × Letter M) :=
  [.star (Set.range (quiet M)), .one {(cell M read true, cell M write true)}, .star (Set.range (quiet M))]

def rightPattern (M : Machine) (read write : M.Γ) : Pattern (Letter M × Letter M) :=
  [.star (Set.range (quiet M)), .one {(cell M read true, cell M write false)},
    .one (Set.range (entering M)), .star (Set.range (quiet M))]

def leftPattern (M : Machine) (read write : M.Γ) : Pattern (Letter M × Letter M) :=
  [.star (Set.range (quiet M)), .one (Set.range (entering M)),
    .one {(cell M read true, cell M write false)}, .star (Set.range (quiet M))]

def leftBoundaryPattern (M : Machine) (read write : M.Γ) : Pattern (Letter M × Letter M) :=
  [.one {(cell M read true, cell M write true)}, .star (Set.range (quiet M))]

lemma stayPattern_matches (M : Machine) (read write : M.Γ) (xs : List (Letter M × Letter M)) :
    Matches (stayPattern M read write) xs ↔
      ∃ left right : List M.Γ,
        xs = left.map (quiet M) ++ (cell M read true, cell M write true) :: right.map (quiet M) := by
  simp only [stayPattern, matches_star_range, matches_one_single, matches_empty]
  simp

lemma rightPattern_matches (M : Machine) (read write : M.Γ) (xs : List (Letter M × Letter M)) :
    Matches (rightPattern M read write) xs ↔
      ∃ (left : List M.Γ) (g : M.Γ) (right : List M.Γ),
        xs = left.map (quiet M) ++ (cell M read true, cell M write false) :: entering M g :: right.map (quiet M) := by
  simp only [rightPattern, matches_star_range, matches_one_single, matches_one_range, matches_empty]
  simp

lemma leftPattern_matches (M : Machine) (read write : M.Γ) (xs : List (Letter M × Letter M)) :
    Matches (leftPattern M read write) xs ↔
      ∃ (left : List M.Γ) (g : M.Γ) (right : List M.Γ),
        xs = left.map (quiet M) ++ entering M g :: (cell M read true, cell M write false) :: right.map (quiet M) := by
  simp only [leftPattern, matches_star_range, matches_one_single, matches_one_range, matches_empty]
  simp

lemma leftBoundaryPattern_matches (M : Machine) (read write : M.Γ) (xs : List (Letter M × Letter M)) :
    Matches (leftBoundaryPattern M read write) xs ↔
      ∃ right : List M.Γ, xs = (cell M read true, cell M write true) :: right.map (quiet M) := by
  simp only [leftBoundaryPattern, matches_star_range, matches_one_single, matches_empty]
  simp

def workPatterns (M : Machine) (direction : Move) (read write : M.Γ) : List (Pattern (Letter M × Letter M)) :=
  match direction with
  | .stay => [stayPattern M read write]
  | .right => [rightPattern M read write]
  | .left => [leftBoundaryPattern M read write, leftPattern M read write]

def RowStep (M : Machine) (direction : Move) (read write : M.Γ) (xs ys : List (Letter M)) : Prop :=
  match direction with
  | .stay => ∃ left right, xs = row M left read right ∧ ys = row M left write right
  | .right => ∃ left g right, xs = row M left read (g :: right) ∧ ys = row M (left ++ [write]) g right
  | .left =>
      (∃ right, xs = row M [] read right ∧ ys = row M [] write right) ∨
      ∃ left g right, xs = row M (left ++ [g]) read right ∧ ys = row M left g (write :: right)

lemma zip_projections {α β : Type} (xs : List (α × β)) : List.zip (xs.map Prod.fst) (xs.map Prod.snd) = xs := by
  induction xs <;> simp [*]

lemma projections_zip {α β : Type} (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    (List.zip xs ys).map Prod.fst = xs ∧ (List.zip xs ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := by simpa using h.symm
    simp [hy]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have hh := ih ys (by simpa using h)
      simpa using hh

lemma workPatterns_sound (M : Machine) (direction : Move) (read write : M.Γ)
    (xs : List (Letter M × Letter M))
    (h : ∃ p ∈ workPatterns M direction read write, Matches p xs) :
    RowStep M direction read write (xs.map Prod.fst) (xs.map Prod.snd) := by
  cases direction with
  | stay =>
    simp only [workPatterns, List.mem_singleton] at h
    obtain ⟨_, rfl, hm⟩ := h
    obtain ⟨left, right, rfl⟩ := (stayPattern_matches M read write xs).mp hm
    exact ⟨left, right, by simp [row, quiet, List.map_map, Function.comp_def],
      by simp [row, quiet, List.map_map, Function.comp_def]⟩
  | right =>
    simp only [workPatterns, List.mem_singleton] at h
    obtain ⟨_, rfl, hm⟩ := h
    obtain ⟨left, g, right, rfl⟩ := (rightPattern_matches M read write xs).mp hm
    exact ⟨left, g, right, by simp [row, quiet, entering, List.map_map, Function.comp_def],
      by simp [row, quiet, entering, List.map_map, Function.comp_def, List.append_assoc]⟩
  | left =>
    obtain ⟨p, hp, hm⟩ := h
    simp only [workPatterns, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨right, rfl⟩ := (leftBoundaryPattern_matches M read write xs).mp hm
      exact Or.inl ⟨right, by simp [row, quiet, List.map_map, Function.comp_def],
        by simp [row, quiet, List.map_map, Function.comp_def]⟩
    · obtain ⟨left, g, right, rfl⟩ := (leftPattern_matches M read write xs).mp hm
      exact Or.inr ⟨left, g, right, by
          simp [row, quiet, entering, List.map_map, Function.comp_def, List.append_assoc],
        by simp [row, quiet, entering, List.map_map, Function.comp_def]⟩

lemma workPatterns_complete (M : Machine) (direction : Move) (read write : M.Γ)
    (xs ys : List (Letter M)) (h : RowStep M direction read write xs ys) :
    ∃ p ∈ workPatterns M direction read write, Matches p (List.zip xs ys) := by
  cases direction with
  | stay =>
    obtain ⟨left, right, rfl, rfl⟩ := h
    let pairs := left.map (quiet M) ++ (cell M read true, cell M write true) :: right.map (quiet M)
    have hp : List.zip (row M left read right) (row M left write right) = pairs := by
      simpa [pairs, row, quiet, List.map_map, Function.comp_def] using zip_projections pairs
    refine ⟨stayPattern M read write, by simp [workPatterns], ?_⟩
    rw [hp]
    exact (stayPattern_matches M read write pairs).mpr ⟨left, right, rfl⟩
  | right =>
    obtain ⟨left, g, right, rfl, rfl⟩ := h
    let pairs := left.map (quiet M) ++ (cell M read true, cell M write false) :: entering M g :: right.map (quiet M)
    have hp : List.zip (row M left read (g :: right)) (row M (left ++ [write]) g right) = pairs := by
      simpa [pairs, row, quiet, entering, List.map_map, Function.comp_def, List.append_assoc] using zip_projections pairs
    refine ⟨rightPattern M read write, by simp [workPatterns], ?_⟩
    rw [hp]
    exact (rightPattern_matches M read write pairs).mpr ⟨left, g, right, rfl⟩
  | left =>
    rcases h with ⟨right, rfl, rfl⟩ | ⟨left, g, right, rfl, rfl⟩
    · let pairs := (cell M read true, cell M write true) :: right.map (quiet M)
      have hp : List.zip (row M [] read right) (row M [] write right) = pairs := by
        simpa [pairs, row, quiet, List.map_map, Function.comp_def] using zip_projections pairs
      refine ⟨leftBoundaryPattern M read write, by simp [workPatterns], ?_⟩
      rw [hp]
      exact (leftBoundaryPattern_matches M read write pairs).mpr ⟨right, rfl⟩
    · let pairs := left.map (quiet M) ++ entering M g :: (cell M read true, cell M write false) :: right.map (quiet M)
      have hp : List.zip (row M (left ++ [g]) read right) (row M left g (write :: right)) = pairs := by
        simpa [pairs, row, quiet, entering, List.map_map, Function.comp_def, List.append_assoc] using zip_projections pairs
      refine ⟨leftPattern M read write, by simp [workPatterns], ?_⟩
      rw [hp]
      exact (leftPattern_matches M read write pairs).mpr ⟨left, g, right, rfl⟩

lemma workPatterns_iff (M : Machine) (direction : Move) (read write : M.Γ)
    (xs ys : List (Letter M)) (hlen : xs.length = ys.length) :
    (∃ p ∈ workPatterns M direction read write, Matches p (List.zip xs ys)) ↔
      RowStep M direction read write xs ys := by
  constructor
  · intro h
    have hh := workPatterns_sound M direction read write (List.zip xs ys) h
    simpa [(projections_zip xs ys hlen).1, (projections_zip xs ys hlen).2] using hh
  · exact workPatterns_complete M direction read write xs ys

lemma rowstep_execution (M : Machine) (w : Lax434930.PolynomialTime.Word) (q : M.Q)
    (input input' : List Bool) (read : M.Γ) (a : Action M.Γ M.Q)
    (hi : BinaryCounter.value input' = min (a.inputMove.apply (BinaryCounter.value input)) (w.length + 1))
    (xs ys : List (Letter M)) (h : RowStep M a.workMove read a.write xs ys) :
    ∃ left right left' current' right',
      xs = row M left read right ∧ ys = row M left' current' right' ∧
      (view M a.state input' left' current' right').expand =
        M.execute w (view M q input left read right).expand a := by
  cases hd : a.workMove with
  | stay =>
    rw [hd] at h
    obtain ⟨left, right, rfl, rfl⟩ := h
    refine ⟨left, right, left, a.write, right, rfl, rfl, ?_⟩
    rw [← TapeZipper.apply_expand]
    congr 1
    simp [view, TapeZipper.apply, hd, hi]
  | right =>
    rw [hd] at h
    obtain ⟨left, g, right, rfl, rfl⟩ := h
    refine ⟨left, g :: right, left ++ [a.write], g, right, rfl, rfl, ?_⟩
    rw [← TapeZipper.apply_expand]
    congr 1
    simp [view, TapeZipper.apply, hd, hi]
  | left =>
    rw [hd] at h
    rcases h with ⟨right, rfl, rfl⟩ | ⟨left, g, right, rfl, rfl⟩
    · refine ⟨[], right, [], a.write, right, rfl, rfl, ?_⟩
      rw [← TapeZipper.apply_expand]
      congr 1
      simp [view, TapeZipper.apply, hd, hi]
    · refine ⟨left ++ [g], right, left, g, a.write :: right, rfl, rfl, ?_⟩
      rw [← TapeZipper.apply_expand]
      congr 1
      simp [view, TapeZipper.apply, hd, hi]

end

end Lax434930Proofs.SavitchProofs.ConfigurationWords
