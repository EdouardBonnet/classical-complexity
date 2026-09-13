import Mathlib.Computability.DFA
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.PatternAutomata

open scoped Classical

noncomputable section

variable {α : Type}

inductive Piece (α : Type) where
  | one (allowed : Set α)
  | star (allowed : Set α)

abbrev Pattern (α : Type) := List (Piece α)

def Matches : Pattern α → List α → Prop
  | [], xs => xs = []
  | .one allowed :: p, xs => ∃ a ∈ allowed, ∃ tail, xs = a :: tail ∧ Matches p tail
  | .star allowed :: p, xs =>
      ∃ front tail, xs = front ++ tail ∧ (∀ a ∈ front, a ∈ allowed) ∧ Matches p tail

def nullable : Pattern α → Bool
  | [] => true
  | .one _ :: _ => false
  | .star _ :: p => nullable p

lemma matches_empty (xs : List α) : Matches [] xs ↔ xs = [] := Iff.rfl

def derivative (a : α) : Pattern α → Finset (Pattern α)
  | [] => ∅
  | .one allowed :: p => if a ∈ allowed then {p} else ∅
  | .star allowed :: p =>
      (if a ∈ allowed then {Piece.star allowed :: p} else ∅) ∪ derivative a p

lemma matches_nil (p : Pattern α) : Matches p [] ↔ nullable p = true := by
  induction p with
  | nil => simp [Matches, nullable]
  | cons piece p ih => cases piece <;> simp [Matches, nullable, ih]

lemma matches_cons (a : α) (xs : List α) (p : Pattern α) :
    Matches p (a :: xs) ↔ ∃ q ∈ derivative a p, Matches q xs := by
  induction p with
  | nil => simp [Matches, derivative]
  | cons piece p ih =>
    cases piece with
    | one allowed =>
      by_cases ha : a ∈ allowed <;> simp [Matches, derivative, ha]
    | star allowed =>
      constructor
      · rintro ⟨front, tail, hxs, hfront, htail⟩
        cases front with
        | nil =>
          simp only [List.nil_append] at hxs
          subst tail
          obtain ⟨q, hq, hmatch⟩ := ih.mp htail
          exact ⟨q, Finset.mem_union_right _ hq, hmatch⟩
        | cons b front =>
          simp only [List.cons_append, List.cons.injEq] at hxs
          obtain ⟨rfl, rfl⟩ := hxs
          have ha : a ∈ allowed := hfront a (by simp)
          refine ⟨.star allowed :: p, ?_, front, tail, rfl, ?_, htail⟩
          · simp [derivative, ha]
          · exact fun x hx => hfront x (List.mem_cons_of_mem a hx)
      · rintro ⟨q, hq, hmatch⟩
        simp only [derivative, Finset.mem_union] at hq
        rcases hq with hq | hq
        · have ha : a ∈ allowed := by
            by_contra ha
            simp [ha] at hq
          have he : q = Piece.star allowed :: p := by simpa [ha] using hq
          subst q
          obtain ⟨front, tail, rfl, hfront, htail⟩ := hmatch
          refine ⟨a :: front, tail, rfl, ?_, htail⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hfront x hx
        · exact ⟨[], a :: xs, rfl, by simp, ih.mpr ⟨q, hq, hmatch⟩⟩

lemma derivative_suffix (a : α) (p q : Pattern α) (hq : q ∈ derivative a p) : q <:+ p := by
  induction p with
  | nil => simp [derivative] at hq
  | cons piece p ih =>
    cases piece with
    | one allowed =>
      by_cases ha : a ∈ allowed
      · simp only [derivative, if_pos ha, Finset.mem_singleton] at hq
        subst q
        exact ⟨[.one allowed], rfl⟩
      · simp [derivative, ha] at hq
    | star allowed =>
      simp only [derivative, Finset.mem_union] at hq
      rcases hq with hq | hq
      · by_cases ha : a ∈ allowed
        · simp only [if_pos ha, Finset.mem_singleton] at hq
          subst q
          exact ⟨[], rfl⟩
        · simp [ha] at hq
      · exact (ih hq).trans ⟨[.star allowed], rfl⟩

abbrev Suffix (patterns : List (Pattern α)) := {p : Pattern α // p ∈ patterns.flatMap List.tails}

instance (patterns : List (Pattern α)) : Fintype (Suffix patterns) := inferInstance

lemma suffix_root (patterns : List (Pattern α)) (p : Pattern α) (hp : p ∈ patterns) :
    p ∈ patterns.flatMap List.tails :=
  List.mem_flatMap.mpr ⟨p, hp, (List.mem_tails p p).mpr ⟨[], rfl⟩⟩

lemma suffix_derivative (patterns : List (Pattern α)) (s : Suffix patterns) (a : α)
    (q : Pattern α) (hq : q ∈ derivative a s.val) : q ∈ patterns.flatMap List.tails := by
  obtain ⟨p, hp, hsp⟩ := List.mem_flatMap.mp s.property
  exact List.mem_flatMap.mpr ⟨p, hp, (List.mem_tails q p).mpr
    ((derivative_suffix a s.val q hq).trans ((List.mem_tails s.val p).mp hsp))⟩

def machine (patterns : List (Pattern α)) : DFA α (Set (Suffix patterns)) where
  start := {s | s.val ∈ patterns}
  step states a := {t | ∃ s ∈ states, t.val ∈ derivative a s.val}
  accept := {states | ∃ s ∈ states, nullable s.val = true}

lemma eval_correct (patterns : List (Pattern α)) (states : Set (Suffix patterns)) (xs : List α) :
    (machine patterns).evalFrom states xs ∈ (machine patterns).accept ↔
      ∃ s ∈ states, Matches s.val xs := by
  induction xs generalizing states with
  | nil => simp [DFA.evalFrom, machine, matches_nil]
  | cons a xs ih =>
    rw [DFA.evalFrom_cons, ih]
    constructor
    · rintro ⟨t, ⟨s, hs, ht⟩, hm⟩
      exact ⟨s, hs, (matches_cons a xs s.val).mpr ⟨t.val, ht, hm⟩⟩
    · rintro ⟨s, hs, hm⟩
      obtain ⟨q, hq, hmatch⟩ := (matches_cons a xs s.val).mp hm
      exact ⟨⟨q, suffix_derivative patterns s a q hq⟩, ⟨s, hs, hq⟩, hmatch⟩

lemma accepts_correct (patterns : List (Pattern α)) (xs : List α) :
    xs ∈ (machine patterns).accepts ↔ ∃ p ∈ patterns, Matches p xs := by
  rw [DFA.mem_accepts]
  change (machine patterns).evalFrom _ xs ∈ _ ↔ _
  rw [eval_correct]
  constructor
  · rintro ⟨p, hp, hm⟩
    exact ⟨p.val, hp, hm⟩
  · rintro ⟨p, hp, hm⟩
    exact ⟨⟨p, suffix_root patterns p hp⟩, hp, hm⟩

lemma matches_append (p q : Pattern α) (xs : List α) :
    Matches (p ++ q) xs ↔ ∃ front tail, xs = front ++ tail ∧ Matches p front ∧ Matches q tail := by
  induction p generalizing xs with
  | nil => simp [Matches]
  | cons piece p ih =>
    cases piece with
    | one allowed =>
      constructor
      · rintro ⟨a, ha, rest, rfl, hr⟩
        obtain ⟨front, tail, rfl, hf, ht⟩ := (ih _).mp hr
        exact ⟨a :: front, tail, rfl, ⟨a, ha, front, rfl, hf⟩, ht⟩
      · rintro ⟨front, tail, rfl, ⟨a, ha, rest, rfl, hr⟩, ht⟩
        exact ⟨a, ha, rest ++ tail, rfl, (ih _).mpr ⟨rest, tail, rfl, hr, ht⟩⟩
    | star allowed =>
      constructor
      · rintro ⟨start, rest, rfl, hs, hr⟩
        obtain ⟨front, tail, rfl, hf, ht⟩ := (ih _).mp hr
        exact ⟨start ++ front, tail, (List.append_assoc ..).symm,
          ⟨start, front, rfl, hs, hf⟩, ht⟩
      · rintro ⟨front, tail, rfl, ⟨start, rest, rfl, hs, hr⟩, ht⟩
        exact ⟨start, rest ++ tail, List.append_assoc .., hs,
          (ih _).mpr ⟨rest, tail, rfl, hr, ht⟩⟩

@[simp] lemma matches_one (allowed : Set α) (xs : List α) :
    Matches [.one allowed] xs ↔ ∃ a ∈ allowed, xs = [a] := by
  simp [Matches]

@[simp] lemma matches_star (allowed : Set α) (xs : List α) :
    Matches [.star allowed] xs ↔ ∀ a ∈ xs, a ∈ allowed := by
  simp [Matches]

lemma list_range {β : Type} (f : β → α) (xs : List α) :
    (∀ a ∈ xs, a ∈ Set.range f) ↔ ∃ ys : List β, xs = ys.map f := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := h a (by simp)
      obtain ⟨ys, rfl⟩ := ih.mp (fun x hx => h x (List.mem_cons_of_mem (f b) hx))
      exact ⟨b :: ys, rfl⟩
    · rintro ⟨ys, hys⟩
      intro x hx
      rw [hys] at hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact ⟨y, rfl⟩

lemma matches_star_range {β : Type} (f : β → α) (p : Pattern α) (xs : List α) :
    Matches (.star (Set.range f) :: p) xs ↔
      ∃ (ys : List β) (tail : List α), xs = ys.map f ++ tail ∧ Matches p tail := by
  constructor
  · rintro ⟨front, tail, rfl, hf, ht⟩
    obtain ⟨ys, rfl⟩ := (list_range f front).mp hf
    exact ⟨ys, tail, rfl, ht⟩
  · rintro ⟨ys, tail, rfl, ht⟩
    exact ⟨ys.map f, tail, rfl, (list_range f _).mpr ⟨ys, rfl⟩, ht⟩

lemma matches_one_range {β : Type} (f : β → α) (p : Pattern α) (xs : List α) :
    Matches (.one (Set.range f) :: p) xs ↔ ∃ b tail, xs = f b :: tail ∧ Matches p tail := by
  simp [Matches, Set.mem_range]

lemma matches_one_single (a : α) (p : Pattern α) (xs : List α) :
    Matches (.one {a} :: p) xs ↔ ∃ tail, xs = a :: tail ∧ Matches p tail := by
  simp [Matches]

lemma list_repeat (a : α) (xs : List α) (h : ∀ x ∈ xs, x = a) : xs = List.replicate xs.length a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.length_cons, List.replicate_succ]
    exact congrArg₂ List.cons hx ht

lemma matches_star_single (a : α) (p : Pattern α) (xs : List α) :
    Matches (.star {a} :: p) xs ↔
      ∃ n tail, xs = List.replicate n a ++ tail ∧ Matches p tail := by
  constructor
  · rintro ⟨front, tail, rfl, hf, ht⟩
    refine ⟨front.length, tail, ?_, ht⟩
    exact congrArg (· ++ tail) (list_repeat a front (by simpa using hf))
  · rintro ⟨n, tail, rfl, ht⟩
    refine ⟨List.replicate n a, tail, rfl, ?_, ht⟩
    intro x hx
    exact (List.mem_replicate.mp hx).2

end

end Lax434930Proofs.SavitchProofs.PatternAutomata
