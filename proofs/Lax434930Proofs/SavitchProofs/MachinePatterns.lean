import Lax434930Proofs.SavitchProofs.BinaryPatterns

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ConfigurationWords

open Lax434930.PolynomialTime Lax434930.SpaceMachines PatternAutomata
open scoped Classical

noncomputable section

def all (α : Type) [Fintype α] : List α := Finset.univ.toList

@[simp] lemma mem_all {α : Type} [Fintype α] (a : α) : a ∈ all α := by simp [all]

def ordinaryPattern (M : Machine) (q : M.Q) (i : InputSymbol) (a : Action M.Γ M.Q)
    (j : InputSymbol) (p : Pattern (Letter M × Letter M)) : Pattern (Letter M × Letter M) :=
  .one {(header M q i, header M a.state j)} ::
    (inputPattern M (inputChange a.inputMove i) ++ .one {(split M, split M)} :: p)

def ordinaryPatterns (M : Machine) : List (Pattern (Letter M × Letter M)) :=
  (all M.Q).flatMap fun q => (all InputSymbol).flatMap fun i =>
    (all M.Γ).flatMap fun read => (M.transition q i read).toList.flatMap fun a =>
      (all InputSymbol).flatMap fun j =>
        (workPatterns M a.workMove read a.write).map (ordinaryPattern M q i a j)

lemma mem_ordinaryPatterns (M : Machine) (p : Pattern (Letter M × Letter M)) :
    p ∈ ordinaryPatterns M ↔ ∃ q i read a, a ∈ M.transition q i read ∧
      ∃ j t, t ∈ workPatterns M a.workMove read a.write ∧ p = ordinaryPattern M q i a j t := by
  simp only [ordinaryPatterns, List.mem_flatMap, List.mem_map, mem_all, true_and, Finset.mem_toList]
  constructor
  · rintro ⟨q, i, read, a, ha, j, t, ht, hp⟩
    exact ⟨q, i, read, a, ha, j, t, ht, hp.symm⟩
  · rintro ⟨q, i, read, a, ha, j, t, ht, hp⟩
    exact ⟨q, i, read, a, ha, j, t, ht, hp.symm⟩

lemma ordinaryPattern_matches (M : Machine) (q : M.Q) (i : InputSymbol) (a : Action M.Γ M.Q)
    (j : InputSymbol) (p : Pattern (Letter M × Letter M)) (xs : List (Letter M × Letter M)) :
    Matches (ordinaryPattern M q i a j p) xs ↔ ∃ input tape,
      xs = (header M q i, header M a.state j) :: (input ++ (split M, split M) :: tape) ∧
      Matches (inputPattern M (inputChange a.inputMove i)) input ∧ Matches p tape := by
  simp only [ordinaryPattern, matches_one_single, matches_append]
  constructor
  · rintro ⟨_, rfl, input, _, rfl, hi, tape, rfl, ht⟩
    exact ⟨input, tape, rfl, hi, ht⟩
  · rintro ⟨input, tape, rfl, hi, ht⟩
    exact ⟨_, rfl, input, _, rfl, hi, tape, rfl, ht⟩

lemma ordinaryPatterns_sound (M : Machine) (w : Word) (xs : List (Letter M × Letter M))
    (h : ∃ p ∈ ordinaryPatterns M, Matches p xs)
    (hsrc : ValidInput M w (xs.map Prod.fst)) (hdst : ValidInput M w (xs.map Prod.snd)) :
    ∃ c d, Represents M (xs.map Prod.fst) c ∧ Represents M (xs.map Prod.snd) d ∧ M.Step w c d := by
  obtain ⟨p, hp, hm⟩ := h
  obtain ⟨q, i, read, a, ha, j, p, hwork, rfl⟩ := (mem_ordinaryPatterns M _).mp hp
  obtain ⟨input, tape, rfl, hi, ht⟩ := (ordinaryPattern_matches M q i a j p xs).mp hm
  obtain ⟨bits, bits', hbits, hbits', hrel⟩ := inputPattern_sound M _ input hi
  have hrow := workPatterns_sound M _ read a.write tape ⟨p, hwork, ht⟩
  have hinput : BinaryCounter.value bits' = min (a.inputMove.apply (BinaryCounter.value bits)) (w.length + 1) := by
    have hs : BinaryCounter.value bits ≤ w.length + 1 ∧ readInput w (BinaryCounter.value bits) = i := by
      simpa only [List.map_cons, List.map_append, hbits, ValidInput, inputBits, desiredInput,
        List.head?_cons, List.tail_cons, header, take_input, List.map_map, Function.comp_def, bit,
        List.map_id'] using hsrc
    have hd : BinaryCounter.value bits' ≤ w.length + 1 ∧ readInput w (BinaryCounter.value bits') = j := by
      simpa only [List.map_cons, List.map_append, hbits', ValidInput, inputBits, desiredInput,
        List.head?_cons, List.tail_cons, header, take_input, List.map_map, Function.comp_def, bit,
        List.map_id'] using hdst
    exact (inputChange_iff w a.inputMove _ _ hs.1 hd.1).mp (hs.2 ▸ hrel)
  obtain ⟨left, right, left', current', right', hs, hd, he⟩ :=
    rowstep_execution M w q bits bits' read a hinput _ _ hrow
  have hsource : ((header M q i, header M a.state j) :: (input ++ (split M, split M) :: tape)).map Prod.fst =
      configuration M q i bits left read right := by simp [configuration, hbits, hs]
  have htarget : ((header M q i, header M a.state j) :: (input ++ (split M, split M) :: tape)).map Prod.snd =
      configuration M a.state j bits' left' current' right' := by simp [configuration, hbits', hd]
  rw [hsource, htarget]
  refine ⟨(view M q bits left read right).expand, (view M a.state bits' left' current' right').expand,
    ⟨q, i, bits, left, read, right, rfl, rfl⟩,
    ⟨a.state, j, bits', left', current', right', rfl, rfl⟩, a, ?_, he⟩
  have hsinput : readInput w (BinaryCounter.value bits) = i := by
    rw [hsource] at hsrc
    simpa [ValidInput] using hsrc.2
  rw [TapeZipper.current_scanned]
  simpa [view, TapeZipper.View.expand, hsinput] using ha

def initialPattern (M : Machine) : Pattern (Letter M × Letter M) :=
  [.one {(.inl false, header M M.start .leftEnd)},
    .star {(.inl false, bit M false)}, .one {(.inl false, split M)},
    .one {(.inl false, cell M M.blank true)}, .star {(.inl false, cell M M.blank false)}]

lemma initialPattern_matches (M : Machine) (xs : List (Letter M × Letter M)) :
    Matches (initialPattern M) xs ↔ ∃ k t,
      xs = (.inl false, header M M.start .leftEnd) ::
        (List.replicate k (.inl false, bit M false) ++ (.inl false, split M) ::
          (.inl false, cell M M.blank true) :: List.replicate t (.inl false, cell M M.blank false)) := by
  simp only [initialPattern, matches_one_single, matches_star_single, matches_empty]
  simp

def terminalPattern (M : Machine) (q : M.Q) (i : InputSymbol) (read : M.Γ) : Pattern (Letter M × Letter M) :=
  [.one {(header M q i, .inl true)}, .star (Set.range (fun b => (bit M b, .inl true))),
    .one {(split M, .inl true)}, .star (Set.range (fun g => (cell M g false, .inl true))),
    .one {(cell M read true, .inl true)}, .star (Set.range (fun g => (cell M g false, .inl true)))]

def terminalPatterns (M : Machine) : List (Pattern (Letter M × Letter M)) :=
  (all M.Q).flatMap fun q => (all InputSymbol).flatMap fun i => (all M.Γ).flatMap fun read =>
    if M.accept q = true ∧ M.transition q i read = ∅ then [terminalPattern M q i read] else []

lemma mem_terminalPatterns (M : Machine) (p : Pattern (Letter M × Letter M)) :
    p ∈ terminalPatterns M ↔ ∃ q i read,
      M.accept q = true ∧ M.transition q i read = ∅ ∧ p = terminalPattern M q i read := by
  simp only [terminalPatterns, List.mem_flatMap, mem_all, true_and]
  apply exists_congr
  intro q
  apply exists_congr
  intro i
  apply exists_congr
  intro read
  by_cases h : M.accept q = true ∧ M.transition q i read = ∅
  · simp [h.1, h.2]
  · simp only [if_neg h, List.not_mem_nil, false_iff]
    exact fun hh => h ⟨hh.1, hh.2.1⟩

lemma terminalPattern_matches (M : Machine) (q : M.Q) (i : InputSymbol) (read : M.Γ)
    (xs : List (Letter M × Letter M)) : Matches (terminalPattern M q i read) xs ↔
      ∃ (input : List Bool) (left right : List M.Γ),
        xs = (header M q i, .inl true) ::
          (input.map (fun b => (bit M b, .inl true)) ++ (split M, .inl true) ::
            (left.map (fun g => (cell M g false, .inl true)) ++
              (cell M read true, .inl true) :: right.map (fun g => (cell M g false, .inl true)))) := by
  simp only [terminalPattern, matches_one_single, matches_star_range, matches_empty]
  simp

def graphPatterns (M : Machine) : List (Pattern (Letter M × Letter M)) :=
  initialPattern M :: (ordinaryPatterns M ++ terminalPatterns M)

lemma initialPattern_sound (M : Machine) (xs : List (Letter M × Letter M))
    (h : Matches (initialPattern M) xs) :
    (∃ n, xs.map Prod.fst = List.replicate (n + 1) (.inl false)) ∧
      Represents M (xs.map Prod.snd) M.initial := by
  obtain ⟨k, t, rfl⟩ := (initialPattern_matches M xs).mp h
  constructor
  · refine ⟨k + t + 2, ?_⟩
    simp only [List.map_cons, List.map_append, List.map_replicate]
    rw [← List.replicate_succ, ← List.replicate_succ, ← List.replicate_add, ← List.replicate_succ]
    congr 1
  · refine ⟨M.start, .leftEnd, List.replicate k false, [], M.blank, List.replicate t M.blank,
      by simp [configuration, row], ?_⟩
    have hv : view M M.start (List.replicate k false) [] M.blank (List.replicate t M.blank) =
        TapeZipper.padded M t := by
      simp [view, TapeZipper.padded, ← BinaryCounter.word_zero, BinaryCounter.word_value]
    rw [hv, TapeZipper.padded_expand]

lemma terminalPatterns_sound (M : Machine) (w : Word) (xs : List (Letter M × Letter M))
    (h : ∃ p ∈ terminalPatterns M, Matches p xs) (hi : ValidInput M w (xs.map Prod.fst)) :
    ∃ c, Represents M (xs.map Prod.fst) c ∧ M.Terminal w c ∧ M.accept c.state = true := by
  obtain ⟨p, hp, hm⟩ := h
  obtain ⟨q, i, read, haccept, hhalt, rfl⟩ := (mem_terminalPatterns M p).mp hp
  obtain ⟨bits, left, right, rfl⟩ := (terminalPattern_matches M q i read xs).mp hm
  have hs : ((header M q i, (.inl true : Letter M)) ::
      (bits.map (fun b => (bit M b, .inl true)) ++ (split M, .inl true) ::
        (left.map (fun g => (cell M g false, .inl true)) ++
          (cell M read true, .inl true) :: right.map (fun g => (cell M g false, .inl true))))).map Prod.fst =
      configuration M q i bits left read right := by
    simp [configuration, row, List.map_map, Function.comp_def]
  rw [hs] at hi ⊢
  have hin : readInput w (BinaryCounter.value bits) = i := by simpa [ValidInput] using hi.2
  refine ⟨(view M q bits left read right).expand, ⟨q, i, bits, left, read, right, rfl, rfl⟩, ?_, haccept⟩
  intro d hd
  obtain ⟨a, ha, _⟩ := hd
  rw [TapeZipper.current_scanned] at ha
  simpa [view, TapeZipper.View.expand, hin, hhalt] using ha

lemma graphPatterns_sound (M : Machine) (w : Word) (xs ys : List (Letter M))
    (hlen : xs.length = ys.length)
    (h : ∃ p ∈ graphPatterns M, Matches p (List.zip xs ys))
    (hsrc : ValidInput M w xs) (hdst : ValidInput M w ys) :
    Represents M ys M.initial ∨
      (∃ c d, Represents M xs c ∧ Represents M ys d ∧ M.Step w c d) ∨
      (∃ c, Represents M xs c ∧ M.Terminal w c ∧ M.accept c.state = true) := by
  obtain ⟨p, hp, hm⟩ := h
  simp only [graphPatterns, List.mem_cons, List.mem_append] at hp
  have he := projections_zip xs ys hlen
  rcases hp with rfl | hp | hp
  · exact Or.inl (by simpa [he.2] using (initialPattern_sound M _ hm).2)
  · refine Or.inr (Or.inl ?_)
    simpa only [he.1, he.2] using ordinaryPatterns_sound M w _ ⟨p, hp, hm⟩
      (by simpa only [he.1] using hsrc) (by simpa only [he.2] using hdst)
  · refine Or.inr (Or.inr ?_)
    simpa only [he.1] using terminalPatterns_sound M w _ ⟨p, hp, hm⟩ (by simpa only [he.1] using hsrc)

end

end Lax434930Proofs.SavitchProofs.ConfigurationWords
