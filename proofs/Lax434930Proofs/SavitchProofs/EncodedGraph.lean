import Lax434930Proofs.SavitchProofs.ConfigurationEncoding
import Lax434930Proofs.SavitchProofs.Configurations
import Lax434930Proofs.SavitchProofs.ShortPaths

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.EncodedGraph

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930Proofs.SavitchDefinitions.Reachability
open ConfigurationWords
open scoped Classical

noncomputable section

def decode (M : Machine) (m : ℕ) (a : Fin (2 ^ m)) : List (Letter M) :=
  FiniteCoding.decodeWord (Payload M) (BinaryCounter.word m a.val)

def query (M : Machine) (w : Word) (xs ys : List Bool) : Bool :=
  let source := FiniteCoding.decodeWord (Payload M) xs
  let target := FiniteCoding.decodeWord (Payload M) ys
  decide (List.zip source target ∈ (PatternAutomata.machine (graphPatterns M)).accepts ∧
    ValidInput M w source ∧ ValidInput M w target)

def graph (M : Machine) (w : Word) (m : ℕ) : Graph (2 ^ m) :=
  fun a b => query M w (BinaryCounter.word m a.val) (BinaryCounter.word m b.val)

lemma edge_iff (M : Machine) (w : Word) (m : ℕ) (a b : Fin (2 ^ m)) :
    graph M w m a b = true ↔
      (∃ p ∈ graphPatterns M, PatternAutomata.Matches p (List.zip (decode M m a) (decode M m b))) ∧
      ValidInput M w (decode M m a) ∧ ValidInput M w (decode M m b) := by
  simp only [graph, query, decide_eq_true_eq, PatternAutomata.accepts_correct, decode]

def first (m : ℕ) : Fin (2 ^ m) := ⟨0, by positivity⟩
def last (m : ℕ) : Fin (2 ^ m) := ⟨2 ^ m - 1, by
  have : 0 < 2 ^ m := by positivity
  omega⟩

lemma decode_first (M : Machine) (n : ℕ) :
    decode M (FiniteCoding.width (Payload M) * n) (first _) = List.replicate n (.inl false) := by
  simp [decode, first, BinaryCounter.word_zero, FiniteCoding.decodeWord_special]

lemma decode_last (M : Machine) (n : ℕ) :
    decode M (FiniteCoding.width (Payload M) * n) (last _) = List.replicate n (.inl true) := by
  simp [decode, last, BinaryCounter.word_ones, FiniteCoding.decodeWord_special]

lemma special_not_represents (M : Machine) (n : ℕ) (b : Bool) (c : M.Config) :
    ¬ Represents M (List.replicate n (.inl b)) c := by
  rintro ⟨q, i, bits, left, current, right, h, _⟩
  cases n <;> simp [configuration, header, List.replicate_succ] at h

lemma decode_length (M : Machine) (m : ℕ) (a b : Fin (2 ^ m)) :
    (decode M m a).length = (decode M m b).length :=
  FiniteCoding.decodeWord_length_eq (Payload M) (by simp)

lemma graph_sound (M : Machine) (w : Word) (m : ℕ) (a b : Fin (2 ^ m))
    (h : graph M w m a b = true) :
    Represents M (decode M m b) M.initial ∨
      (∃ c d, Represents M (decode M m a) c ∧ Represents M (decode M m b) d ∧ M.Step w c d) ∨
      (∃ c, Represents M (decode M m a) c ∧ M.Terminal w c ∧ M.accept c.state = true) := by
  obtain ⟨hp, hs, ht⟩ := (edge_iff M w m a b).mp h
  exact graphPatterns_sound M w _ _ (decode_length M m a b) hp hs ht

lemma reachable_invariant (M : Machine) (w : Word) (n : ℕ)
    (b : Fin (2 ^ (FiniteCoding.width (Payload M) * n)))
    (h : Reachable (graph M w _) (first _) b) :
    b = first _ ∨ (∃ t c, M.Run w t c ∧ Represents M (decode M _ b) c) ∨ M.Accepts w := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b d h he ih =>
    rcases graph_sound M w _ b d he with hi | ⟨c, c', hc, hc', hs⟩ | ⟨c, hc, ht, ha⟩
    · exact Or.inr (Or.inl ⟨0, M.initial, .zero, hi⟩)
    · rcases ih with rfl | ⟨t, c₀, hr, hrep⟩ | ha
      · rw [decode_first] at hc
        exact (special_not_represents M n false c hc).elim
      · obtain rfl := representation_unique M _ c₀ c hrep hc
        exact Or.inr (Or.inl ⟨t + 1, c', .succ hr hs, hc'⟩)
      · exact Or.inr (Or.inr ha)
    · rcases ih with rfl | ⟨t, c₀, hr, hrep⟩ | ha'
      · rw [decode_first] at hc
        exact (special_not_represents M n false c hc).elim
      · obtain rfl := representation_unique M _ c₀ c hrep hc
        exact Or.inr (Or.inr ⟨t, _, hr, ht, ha⟩)
      · exact Or.inr (Or.inr ha')

lemma reachable_sound (M : Machine) (w : Word) (n : ℕ) (hn : 0 < n)
    (h : Reachable (graph M w (FiniteCoding.width (Payload M) * n)) (first _) (last _)) : M.Accepts w := by
  rcases reachable_invariant M w n _ h with he | ⟨t, c, _, hc⟩ | ha
  · have hh := congrArg (decode M (FiniteCoding.width (Payload M) * n)) he
    rw [decode_first, decode_last] at hh
    cases n with
    | zero => omega
    | succ n => simp [List.replicate_succ] at hh
  · rw [decode_last] at hc
    exact (special_not_represents M n true c hc).elim
  · exact ha

def vertex (M : Machine) (m : ℕ) (xs : List (Letter M))
    (hlen : FiniteCoding.width (Payload M) * xs.length = m) : Fin (2 ^ m) :=
  ⟨BinaryCounter.value (FiniteCoding.encodeWord (Payload M) xs), by
    have h := BinaryCounter.value_lt (FiniteCoding.encodeWord (Payload M) xs)
    simpa only [FiniteCoding.encodeWord_length, hlen] using h⟩

lemma decode_vertex (M : Machine) (m : ℕ) (xs : List (Letter M))
    (hlen : FiniteCoding.width (Payload M) * xs.length = m) :
    decode M m (vertex M m xs hlen) = xs := by
  have hh : (FiniteCoding.encodeWord (Payload M) xs).length = m := by
    simpa only [FiniteCoding.encodeWord_length] using hlen
  simp only [decode, vertex]
  rw [← hh, BinaryCounter.word_of_value, FiniteCoding.decodeWord_encodeWord]

lemma special_input (M : Machine) (w : Word) (n : ℕ) (b : Bool) :
    ValidInput M w (List.replicate n (.inl b)) := by
  cases n <;> simp [ValidInput, inputBits, desiredInput, BinaryCounter.value, readInput, List.replicate_succ]

lemma encoded_run (M : Machine) (w : Word) (k s : ℕ) (hk : w.length + 1 < 2 ^ k)
    (hspace : M.UsesSpace w s) (t : ℕ) (c : M.Config) (hr : M.Run w t c) :
    ∃ v : TapeZipper.View M, ∃ a : Fin (2 ^ (FiniteCoding.width (Payload M) * (k + s + 2))),
      v.cells = s ∧ v.expand = c ∧ decode M _ a = canonical M w k v ∧
        Reachable (graph M w _) (first _) a := by
  have hs : 0 < s := hspace 0 M.initial .zero
  let m := FiniteCoding.width (Payload M) * (k + s + 2)
  induction hr with
  | zero =>
    let v := TapeZipper.padded M (s - 1)
    have hv : v.cells = s := by simp [v]; omega
    let a := vertex M m (canonical M w k v) (by simp [m, hv])
    have hd : decode M m a = canonical M w k v := decode_vertex M m _ _
    refine ⟨v, a, hv, TapeZipper.padded_expand M _, hd, Relation.ReflTransGen.single ?_⟩
    apply (edge_iff M w m _ _).mpr
    change _ ∧ _ ∧ _
    rw [hd]
    have hfirst : decode M m (first m) = List.replicate (k + (s - 1) + 3) (.inl false) := by
      rw [decode_first]
      congr 1
      omega
    rw [hfirst]
    exact ⟨initial_complete M w k (s - 1), special_input M w _ false,
      canonical_input M w k v (by simp [v, TapeZipper.padded]) (by simp [v, TapeZipper.padded])⟩
  | @succ t c d hr he ih =>
    obtain ⟨v, a, hv, hvc, hdecode, hpath⟩ := ih
    obtain ⟨action, haction, hd⟩ := he
    let v' := TapeZipper.apply M w v action
    have hvd : v'.expand = d := by rw [TapeZipper.apply_expand, hvc, hd]
    have hhead : v'.left.length < v.cells := by
      rw [hv]
      have hh := hspace (t + 1) d (.succ hr ⟨action, haction, hd⟩)
      simpa only [← hvd, TapeZipper.View.expand] using hh
    have hv' : v'.cells = s := (TapeZipper.cells_eq M w v action hhead).trans hv
    let b := vertex M m (canonical M w k v') (by simp [m, hv'])
    have hdecode' : decode M m b = canonical M w k v' := decode_vertex M m _ _
    have hi : v.inputHead ≤ w.length + 1 := by simpa only [← hvc, TapeZipper.View.expand] using input_bound hr
    have hi' : v'.inputHead ≤ w.length + 1 := by
      simpa only [← hvd, TapeZipper.View.expand] using input_bound (.succ hr ⟨action, haction, hd⟩)
    refine ⟨v', b, hv', hvd, hdecode', hpath.tail ?_⟩
    apply (edge_iff M w m a b).mpr
    rw [hdecode, hdecode']
    have ha : action ∈ M.transition v.state (readInput w v.inputHead) v.current := by
      rw [← hvc, TapeZipper.current_scanned] at haction
      exact haction
    exact ⟨canonical_step M w k v action ha hi hk hhead,
      canonical_input M w k v (hi.trans_lt hk) hi, canonical_input M w k v' (hi'.trans_lt hk) hi'⟩

lemma reachable_complete (M : Machine) (w : Word) (k s : ℕ) (hk : w.length + 1 < 2 ^ k)
    (hspace : M.UsesSpace w s) (h : M.Accepts w) :
    Reachable (graph M w (FiniteCoding.width (Payload M) * (k + s + 2))) (first _) (last _) := by
  obtain ⟨t, c, hr, ht, ha⟩ := h
  obtain ⟨v, a, hv, hvc, hd, hp⟩ := encoded_run M w k s hk hspace t c hr
  refine hp.tail ((edge_iff M w _ _ _).mpr ?_)
  rw [hd, decode_last]
  have hi : v.inputHead ≤ w.length + 1 := by simpa only [← hvc, TapeZipper.View.expand] using input_bound hr
  refine ⟨?_, canonical_input M w k v (hi.trans_lt hk) hi, special_input M w _ true⟩
  simpa only [hv] using terminal_complete M w k v (by simpa only [← hvc] using ht)
    (by change M.accept v.expand.state = true; rw [hvc]; exact ha)

lemma search_correct (M : Machine) (w : Word) (k s : ℕ) (hk : w.length + 1 < 2 ^ k)
    (hspace : M.UsesSpace w s) :
    let m := FiniteCoding.width (Payload M) * (k + s + 2)
    search (graph M w m) m (first m) (last m) = true ↔ M.Accepts w := by
  dsimp only
  rw [recursive_reachability]
  constructor
  · rintro ⟨t, _, ht⟩
    exact reachable_sound M w _ (by omega) (walk_reachable ht)
  · intro ha
    obtain ⟨t, ht, hw⟩ := (short_paths _ _ _).mp (reachable_complete M w k s hk hspace ha)
    exact ⟨t, Nat.le_of_lt ht, hw⟩

end

end Lax434930Proofs.SavitchProofs.EncodedGraph
