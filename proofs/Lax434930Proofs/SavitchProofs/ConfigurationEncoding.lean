import Lax434930Proofs.SavitchProofs.MachinePatterns

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.ConfigurationWords

open Lax434930.PolynomialTime Lax434930.SpaceMachines PatternAutomata
open scoped Classical

noncomputable section

def canonical (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M) : List (Letter M) :=
  configuration M v.state (readInput w v.inputHead) (BinaryCounter.word k v.inputHead)
    v.left.reverse v.current v.right

lemma canonical_represents (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M)
    (hi : v.inputHead < 2 ^ k) : Represents M (canonical M w k v) v.expand := by
  refine ⟨v.state, readInput w v.inputHead, BinaryCounter.word k v.inputHead,
    v.left.reverse, v.current, v.right, rfl, ?_⟩
  congr 1
  simp [view, BinaryCounter.word_value, Nat.mod_eq_of_lt hi]

lemma canonical_input (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M)
    (hi : v.inputHead < 2 ^ k) (hb : v.inputHead ≤ w.length + 1) :
    ValidInput M w (canonical M w k v) := by
  simp [canonical, ValidInput, BinaryCounter.word_value, Nat.mod_eq_of_lt hi, hb]

@[simp] lemma canonical_length (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M) :
    (canonical M w k v).length = k + v.cells + 2 := by
  simp [canonical, TapeZipper.View.cells]
  omega

lemma apply_rowstep (M : Machine) (w : Word) (v : TapeZipper.View M) (a : Action M.Γ M.Q)
    (hh : (TapeZipper.apply M w v a).left.length < v.cells) :
    RowStep M a.workMove v.current a.write
      (row M v.left.reverse v.current v.right)
      (row M (TapeZipper.apply M w v a).left.reverse
        (TapeZipper.apply M w v a).current (TapeZipper.apply M w v a).right) := by
  cases v with
  | mk state inputHead left current right =>
    cases hd : a.workMove with
    | stay => exact ⟨left.reverse, right, rfl, by simp [TapeZipper.apply, hd]⟩
    | left =>
      cases left with
      | nil => exact Or.inl ⟨right, rfl, by simp [TapeZipper.apply, hd]⟩
      | cons g left =>
        exact Or.inr ⟨left.reverse, g, right, by simp, by simp [TapeZipper.apply, hd]⟩
    | right =>
      cases right with
      | nil => simp [TapeZipper.apply, hd, TapeZipper.View.cells] at hh
      | cons g right =>
        exact ⟨left.reverse, g, right, rfl, by simp [TapeZipper.apply, hd]⟩

lemma canonical_step (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M) (a : Action M.Γ M.Q)
    (ha : a ∈ M.transition v.state (readInput w v.inputHead) v.current)
    (hi : v.inputHead ≤ w.length + 1) (hk : w.length + 1 < 2 ^ k)
    (hh : (TapeZipper.apply M w v a).left.length < v.cells) :
    ∃ p ∈ graphPatterns M,
      Matches p (List.zip (canonical M w k v) (canonical M w k (TapeZipper.apply M w v a))) := by
  let v' := TapeZipper.apply M w v a
  have hn' : v'.inputHead ≤ w.length + 1 := by
    cases hd : a.workMove <;> simp [v', TapeZipper.apply, hd] <;> split <;> simp
  have hr := apply_rowstep M w v a hh
  obtain ⟨p, hp, hm⟩ := workPatterns_complete M a.workMove v.current a.write _ _ hr
  have hstate : v'.state = a.state := by
    cases hd : a.workMove <;> simp [v', TapeZipper.apply, hd] <;> split <;> rfl
  have hhead : v'.inputHead = min (a.inputMove.apply v.inputHead) (w.length + 1) := by
    cases hd : a.workMove <;> simp [v', TapeZipper.apply, hd] <;> split <;> rfl
  have hinput := inputPattern_complete M (inputChange a.inputMove (readInput w v.inputHead)) k
    v.inputHead v'.inputHead (hi.trans_lt hk) (hn'.trans_lt hk)
    ((inputChange_iff w a.inputMove _ _ hi hn').mpr hhead)
  refine ⟨ordinaryPattern M v.state (readInput w v.inputHead) a (readInput w v'.inputHead) p, ?_, ?_⟩
  · apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact (mem_ordinaryPatterns M _).mpr ⟨_, _, _, a, ha, _, p, hp, rfl⟩
  · apply (ordinaryPattern_matches M _ _ _ _ _ _).mpr
    refine ⟨List.zip ((BinaryCounter.word k v.inputHead).map (bit M))
        ((BinaryCounter.word k v'.inputHead).map (bit M)),
      List.zip (row M v.left.reverse v.current v.right) (row M v'.left.reverse v'.current v'.right),
      ?_, hinput, hm⟩
    change (TapeZipper.apply M w v a).state = a.state at hstate
    simp only [canonical, configuration, List.zip_cons_cons, hstate]
    rw [List.zip_append (by simp)]
    rfl

lemma initial_complete (M : Machine) (w : Word) (k t : ℕ) :
    ∃ p ∈ graphPatterns M, Matches p (List.zip (List.replicate (k + t + 3) (.inl false))
      (canonical M w k (TapeZipper.padded M t))) := by
  let pairs : List (Letter M × Letter M) := (.inl false, header M M.start .leftEnd) ::
    (List.replicate k (.inl false, bit M false) ++ (.inl false, split M) ::
      (.inl false, cell M M.blank true) :: List.replicate t (.inl false, cell M M.blank false))
  have hsrc : pairs.map Prod.fst = List.replicate (k + t + 3) (.inl false) := by
    simp only [pairs, List.map_cons, List.map_append, List.map_replicate]
    rw [← List.replicate_succ, ← List.replicate_succ, ← List.replicate_add, ← List.replicate_succ]
    congr 1
  have hdst : pairs.map Prod.snd = canonical M w k (TapeZipper.padded M t) := by
    simp [pairs, canonical, configuration, row, TapeZipper.padded, BinaryCounter.word_zero, readInput]
  refine ⟨initialPattern M, by simp [graphPatterns], ?_⟩
  rw [← hsrc, ← hdst, zip_projections]
  exact (initialPattern_matches M pairs).mpr ⟨k, t, rfl⟩

lemma terminal_complete (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M)
    (hhalt : M.Terminal w v.expand) (haccept : M.accept v.state = true) :
    ∃ p ∈ graphPatterns M, Matches p (List.zip (canonical M w k v)
      (List.replicate (k + v.cells + 2) (.inl true))) := by
  have htrans : M.transition v.state (readInput w v.inputHead) v.current = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro a ha
    exact hhalt (M.execute w v.expand a) ⟨a, by simpa [TapeZipper.current_scanned] using! ha, rfl⟩
  let bits := BinaryCounter.word k v.inputHead
  let pairs : List (Letter M × Letter M) := (header M v.state (readInput w v.inputHead), .inl true) ::
    (bits.map (fun b => (bit M b, .inl true)) ++ (split M, .inl true) ::
      (v.left.reverse.map (fun g => (cell M g false, .inl true)) ++
        (cell M v.current true, .inl true) :: v.right.map (fun g => (cell M g false, .inl true))))
  have hsrc : pairs.map Prod.fst = canonical M w k v := by
    simp [pairs, bits, canonical, configuration, row, List.map_map, Function.comp_def]
  have hdst : pairs.map Prod.snd = List.replicate (k + v.cells + 2) (.inl true) := by
    have hconst : ∀ x ∈ pairs.map Prod.snd, x = .inl true := by
      simp [pairs, List.map_map, Function.comp_def]
    have hlen := congrArg List.length hsrc
    simp only [List.length_map, canonical_length] at hlen
    have hrep := list_repeat (.inl true) (pairs.map Prod.snd) hconst
    simpa only [List.length_map, hlen] using hrep
  refine ⟨terminalPattern M v.state (readInput w v.inputHead) v.current, ?_, ?_⟩
  · apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact (mem_terminalPatterns M _).mpr ⟨_, _, _, haccept, htrans, rfl⟩
  · rw [← hsrc, ← hdst, zip_projections]
    exact (terminalPattern_matches M _ _ _ pairs).mpr ⟨bits, v.left.reverse, v.right, rfl⟩

end

end Lax434930Proofs.SavitchProofs.ConfigurationWords
