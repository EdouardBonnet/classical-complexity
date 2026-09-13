import Lax434930Proofs.SavitchProofs.FiniteCoding
import Lax434930Proofs.SavitchProofs.StackTransducer

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.BitDecoder

open FiniteCoding
open StackTransducer (run)
open scoped Classical

noncomputable section

variable (α : Type) [Fintype α]

abbrev Buffer := {xs : List Bool // xs.length < width α}

instance : Fintype (Buffer α) := (List.finite_length_lt Bool (width α)).fintype

def empty : Buffer α := ⟨[], width_pos α⟩

variable [Inhabited α]

def step (buf : Buffer α) (b : Bool) : Buffer α × Option (Letter α) :=
  if h : (buf.val ++ [b]).length = width α then (empty α, some (decodeBlock α (buf.val ++ [b])))
  else (⟨buf.val ++ [b], by have hb := buf.property; simp only [List.length_append, List.length_singleton] at *; omega⟩, none)

lemma run_prefix (buf : Buffer α) (xs : List Bool) (h : buf.val.length + xs.length < width α) :
    run (step α) buf xs = (⟨buf.val ++ xs, by simpa using h⟩, []) := by
  induction xs generalizing buf with
  | nil =>
    apply Prod.ext
    · apply Subtype.ext
      simp [run]
    · rfl
  | cons b xs ih =>
    have hb : (buf.val ++ [b]).length < width α := by
      simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *
      omega
    let next : Buffer α := ⟨buf.val ++ [b], hb⟩
    have hs : step α buf b = (next, none) := by rw [step, dif_neg (ne_of_lt hb)]
    have hr : next.val.length + xs.length < width α := by
      simp only [next, List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *
      omega
    have hh := ih next hr
    rw [run, hs]
    simpa [next, List.append_assoc] using hh

lemma run_block (buf : Buffer α) (xs : List Bool) (hn : xs ≠ [])
    (h : buf.val.length + xs.length = width α) :
    run (step α) buf xs = (empty α, [decodeBlock α (buf.val ++ xs)]) := by
  obtain ⟨ys, b, rfl⟩ : ∃ ys b, xs = ys ++ [b] :=
    ⟨xs.dropLast, xs.getLast hn, (List.dropLast_append_getLast hn).symm⟩
  have hb : buf.val.length + ys.length < width α := by
    simp only [List.length_append, List.length_singleton] at h
    omega
  let next : Buffer α := ⟨buf.val ++ ys, by simpa using hb⟩
  have hs : step α next b = (empty α, some (decodeBlock α (buf.val ++ (ys ++ [b])))) := by
    have hh : (next.val ++ [b]).length = width α := by simpa [next, List.length_append] using h
    rw [step, dif_pos hh]
    simp [next, List.append_assoc]
  rw [StackTransducer.run_append, run_prefix α buf ys hb]
  change ((run (step α) next [b]).1, [] ++ (run (step α) next [b]).2) = _
  simp [run, hs]

def flush (buf : Buffer α) : List (Letter α) :=
  if buf.val = [] then [] else [decodeBlock α buf.val]

def decode (xs : List Bool) : List (Letter α) :=
  (run (step α) (empty α) xs).2 ++ flush α (run (step α) (empty α) xs).1

lemma decode_correct (xs : List Bool) : decode α xs = decodeWord α xs := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    by_cases hn : xs = []
    · subst xs
      simp [decode, run, empty, flush]
    · by_cases hs : xs.length < width α
      · have hr := run_prefix α (empty α) xs (by simpa [empty] using hs)
        rw [decode, hr, FiniteCoding.decodeWord, if_neg hn]
        simp [flush, empty, hn, List.take_of_length_le (Nat.le_of_lt hs),
          List.drop_eq_nil_of_le (Nat.le_of_lt hs)]
      · have hw : width α ≤ xs.length := by omega
        have hp := width_pos α
        have htake : (xs.take (width α)).length = width α := by simp [List.length_take, Nat.min_eq_left hw]
        have hne : xs.take (width α) ≠ [] := by intro hh; simp [hh] at htake; omega
        have hr := run_block α (empty α) (xs.take (width α)) hne (by simpa [empty] using htake)
        have hrec := ih (xs.drop (width α)) (by
          change (xs.drop (width α)).length < xs.length
          simp only [List.length_drop]
          omega)
        have he : run (step α) (empty α) xs =
            ((run (step α) (empty α) (xs.drop (width α))).1,
              [decodeBlock α (xs.take (width α))] ++ (run (step α) (empty α) (xs.drop (width α))).2) := by
          conv_lhs => rw [← List.take_append_drop (width α) xs, StackTransducer.run_append, hr]
          simp [empty]
        rw [decode, he]
        change decodeBlock α (xs.take (width α)) :: decode α (xs.drop (width α)) = _
        rw [hrec]
        conv_rhs => rw [FiniteCoding.decodeWord, if_neg hn]

lemma run_accounting (buf : Buffer α) (xs : List Bool) :
    (run (step α) buf xs).2.length * width α + (run (step α) buf xs).1.val.length =
      buf.val.length + xs.length := by
  induction xs generalizing buf with
  | nil => simp [run]
  | cons b xs ih =>
    by_cases hh : (buf.val ++ [b]).length = width α
    · have hs : step α buf b = (empty α, some (decodeBlock α (buf.val ++ [b]))) := by simp [step, hh]
      have ht := ih (empty α)
      simp only [show (empty α).val.length = 0 from rfl, Nat.zero_add] at ht
      simp only [List.length_append, List.length_singleton] at hh
      simp [run, hs, Nat.add_mul]
      omega
    · have hb : (buf.val ++ [b]).length < width α := by
        have := buf.property
        simp only [List.length_append, List.length_singleton] at *
        omega
      let next : Buffer α := ⟨buf.val ++ [b], hb⟩
      have hs : step α buf b = (next, none) := by rw [step, dif_neg hh]
      have ht := ih next
      change (run (step α) next xs).2.length * width α +
        (run (step α) next xs).1.val.length = (buf.val ++ [b]).length + xs.length at ht
      simp only [List.length_append, List.length_singleton] at ht
      simp [run, hs]
      omega

end

end Lax434930Proofs.SavitchProofs.BitDecoder
