import Lax434930Proofs.SavitchProofs.BinaryWords
import Mathlib.Data.Set.Finite.List

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.FiniteCoding

open scoped Classical

noncomputable section

variable (α : Type) [Fintype α]

abbrev Letter := Sum Bool α

def width : ℕ := Fintype.card α + 2

lemma width_pos : 0 < width α := by simp [width]

lemma payload_bound : Fintype.card α + 1 < 2 ^ width α := by
  have h : Fintype.card α + 2 < 2 ^ (Fintype.card α + 2) := Nat.lt_two_pow_self
  simp only [width]
  omega

def number : Letter α → ℕ
  | .inl false => 0
  | .inl true => 2 ^ width α - 1
  | .inr a => (Fintype.equivFin α a).val + 1

lemma number_lt (a : Letter α) : number α a < 2 ^ width α := by
  have hp := payload_bound α
  cases a with
  | inl b => cases b <;> simp [number] <;> omega
  | inr a => have := (Fintype.equivFin α a).isLt; simp only [number]; omega

variable [Inhabited α]

def decode (n : ℕ) : Letter α :=
  if n = 0 then .inl false
  else if n = 2 ^ width α - 1 then .inl true
  else if h : n - 1 < Fintype.card α then .inr ((Fintype.equivFin α).symm ⟨n - 1, h⟩)
  else .inr default

lemma decode_number (a : Letter α) : decode α (number α a) = a := by
  have hp := payload_bound α
  cases a with
  | inl b => cases b <;> simp [number, decode, show 2 ^ width α - 1 ≠ 0 by omega]
  | inr a =>
    have hb := (Fintype.equivFin α a).isLt
    have hn : (Fintype.equivFin α a).val + 1 ≠ 2 ^ width α - 1 := by omega
    simp [number, decode, hn, hb]

def encode (a : Letter α) : List Bool := BinaryCounter.word (width α) (number α a)
def decodeBlock (xs : List Bool) : Letter α := decode α (BinaryCounter.value xs)

@[simp] lemma encode_length (a : Letter α) : (encode α a).length = width α := by simp [encode]

@[simp] lemma decode_encode (a : Letter α) : decodeBlock α (encode α a) = a := by
  simp [encode, decodeBlock, BinaryCounter.word_value, Nat.mod_eq_of_lt (number_lt α a), decode_number]

lemma encode_injective : Function.Injective (encode α) :=
  Function.LeftInverse.injective (decode_encode α)

@[simp] lemma encode_zero : encode α (.inl false) = List.replicate (width α) false := by
  simp [encode, number, BinaryCounter.word_zero]

@[simp] lemma encode_one : encode α (.inl true) = List.replicate (width α) true := by
  simp [encode, number, BinaryCounter.word_ones]

def encodeWord (xs : List (Letter α)) : List Bool := xs.flatMap (encode α)

@[simp] lemma encodeWord_length (xs : List (Letter α)) :
    (encodeWord α xs).length = width α * xs.length := by
  induction xs with
  | nil => simp [encodeWord]
  | cons a xs ih =>
    change (encode α a ++ encodeWord α xs).length = width α * (xs.length + 1)
    rw [List.length_append, encode_length, ih, Nat.mul_add, Nat.mul_one]
    omega

def decodeWord (xs : List Bool) : List (Letter α) :=
  if xs = [] then [] else decodeBlock α (xs.take (width α)) :: decodeWord (xs.drop (width α))
termination_by xs.length
decreasing_by
  have := width_pos α
  have : 0 < xs.length := List.length_pos_iff.mpr (by assumption)
  change (xs.drop (width α)).length < xs.length
  simp only [List.length_drop]
  omega

@[simp] lemma decodeWord_nil : decodeWord α [] = [] := by rw [decodeWord]; simp

lemma decodeWord_cons_block (a : Letter α) (xs : List Bool) :
    decodeWord α (encode α a ++ xs) = a :: decodeWord α xs := by
  have hn : encode α a ++ xs ≠ [] := by
    have hlen := encode_length α a
    have hp := width_pos α
    intro hh
    have := congrArg List.length hh
    simp at this
    omega
  rw [decodeWord, if_neg hn]
  simp [List.take_append, List.drop_append]

@[simp] lemma decodeWord_encodeWord (xs : List (Letter α)) :
    decodeWord α (encodeWord α xs) = xs := by
  induction xs with
  | nil => simp [encodeWord]
  | cons a xs ih =>
    change decodeWord α (encode α a ++ encodeWord α xs) = a :: xs
    rw [decodeWord_cons_block, ih]

lemma encodeWord_special (n : ℕ) (b : Bool) :
    encodeWord α (List.replicate n (.inl b)) = List.replicate (width α * n) b := by
  induction n with
  | zero => simp [encodeWord]
  | succ n ih =>
    change encode α (.inl b) ++ encodeWord α (List.replicate n (.inl b)) = _
    rw [ih]
    cases b <;> simp [← List.replicate_add, Nat.mul_succ, Nat.add_comm]

lemma decodeWord_special (n : ℕ) (b : Bool) :
    decodeWord α (List.replicate (width α * n) b) = List.replicate n (.inl b) := by
  rw [← encodeWord_special, decodeWord_encodeWord]

lemma decodeWord_length_le (xs : List Bool) : (decodeWord α xs).length ≤ xs.length := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    rw [decodeWord]
    split
    · simp_all
    · have hp := width_pos α
      have hn : 0 < xs.length := List.length_pos_iff.mpr (by assumption)
      have hh := ih (xs.drop (width α)) (by change (xs.drop (width α)).length < xs.length; simp only [List.length_drop]; omega)
      simp only [List.length_cons]
      simp only [List.length_drop] at hh
      omega

lemma decodeWord_length_eq {xs ys : List Bool} (h : xs.length = ys.length) :
    (decodeWord α xs).length = (decodeWord α ys).length := by
  induction xs using (measure List.length).wf.induction generalizing ys with
  | h xs ih =>
    by_cases hx : xs = []
    · subst xs
      have hy : ys = [] := by simpa using h.symm
      simp [hy]
    · have hy : ys ≠ [] := by intro he; simp [he] at h; exact hx (by simpa using h)
      have hp := width_pos α
      have hn : 0 < xs.length := List.length_pos_iff.mpr hx
      conv_lhs => rw [decodeWord, if_neg hx]
      conv_rhs => rw [decodeWord, if_neg hy]
      simp only [List.length_cons]
      exact congrArg (· + 1) (ih (xs.drop (width α)) (by change (xs.drop (width α)).length < xs.length; simp only [List.length_drop]; omega)
        (by simp only [List.length_drop, h]))

end

end Lax434930Proofs.SavitchProofs.FiniteCoding
