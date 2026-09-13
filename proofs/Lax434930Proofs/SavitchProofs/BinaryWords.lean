import Lax434930Proofs.SavitchProofs.BinaryCounter

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.BinaryCounter

def word : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => decide (n % 2 = 1) :: word k (n / 2)

@[simp] lemma word_length (k n : ℕ) : (word k n).length = k := by
  induction k generalizing n <;> simp [word, *]

lemma value_injective {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hv : value xs = value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c ys =>
      have htail : xs.length = ys.length := by simpa using hlen
      cases b <;> cases c <;> simp only [value, Bool.toNat_false, Bool.toNat_true] at hv
      · exact congrArg (false :: ·) (ih htail (by omega))
      · omega
      · omega
      · exact congrArg (true :: ·) (ih htail (by omega))

lemma word_value (k n : ℕ) : value (word k n) = n % 2 ^ k := by
  induction k generalizing n with
  | zero => simp [word, value, Nat.mod_one]
  | succ k ih =>
    have hb : (decide (n % 2 = 1)).toNat = n % 2 := by
      have := Nat.mod_lt n (by decide : 0 < 2)
      by_cases h : n % 2 = 1 <;> simp [h] <;> omega
    simp only [word, value, ih, hb]
    have hdiv := Nat.mod_add_div (n % (2 * 2 ^ k)) 2
    have hmod : n % (2 * 2 ^ k) % 2 = n % 2 := Nat.mod_mul_right_mod n 2 (2 ^ k)
    rw [hmod, Nat.mod_mul_right_div_self] at hdiv
    simpa [pow_succ, Nat.mul_comm] using hdiv

lemma word_zero (k : ℕ) : word k 0 = List.replicate k false := by
  induction k <;> simp [word, List.replicate_succ, *]

lemma word_mod (k n : ℕ) : word k (n % 2 ^ k) = word k n := by
  apply value_injective (by simp)
  simp [word_value]

lemma word_of_value (xs : List Bool) : word xs.length (value xs) = xs := by
  apply value_injective (by simp)
  simp [word_value, Nat.mod_eq_of_lt (value_lt xs)]

lemma word_increment (k n : ℕ) : increment (word k n) = word k (n + 1) := by
  apply value_injective (by simp [increment_length])
  have hi := increment_value (word k n)
  have hb := value_lt (increment (word k n))
  simp only [word_length, word_value, increment_length] at hi hb
  have hmod := congrArg (· % 2 ^ k) hi
  cases hc : carry (word k n) <;>
    simpa [hc, word_value, Nat.mod_eq_of_lt hb, Nat.add_mod, Nat.mod_mod] using hmod

lemma word_carry (k n : ℕ) (hn : n < 2 ^ k) :
    carry (word k n) = decide (n + 1 = 2 ^ k) := by
  have hi := increment_value (word k n)
  have hb := value_lt (increment (word k n))
  simp only [word_length, word_value, Nat.mod_eq_of_lt hn, increment_length] at hi hb
  cases hc : carry (word k n)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hi
    simp [show n + 1 ≠ 2 ^ k by omega]
  · simp only [hc, ↓reduceIte] at hi
    simp [show n + 1 = 2 ^ k by omega]

lemma word_eq_iff (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    word k x = word k y ↔ x = y := by
  constructor
  · intro h
    have := congrArg value h
    simpa [word_value, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this
  · rintro rfl; rfl

lemma ones_value (k : ℕ) : value (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, value, pow_succ] <;> omega

lemma word_ones (k : ℕ) : word k (2 ^ k - 1) = List.replicate k true := by
  apply value_injective (by simp)
  rw [word_value, Nat.mod_eq_of_lt (Nat.sub_lt (by positivity) (by decide : 0 < 1))]
  have := ones_value k
  omega

lemma complement_value (xs : List Bool) : value (xs.map Bool.not) + value xs + 1 = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [value, pow_succ] <;> omega

lemma word_complement (k n : ℕ) (hn : n < 2 ^ k) :
    (word k n).map Bool.not = word k (2 ^ k - 1 - n) := by
  apply value_injective (by simp)
  have hb : 2 ^ k - 1 - n < 2 ^ k := by
    have hp : 0 < 2 ^ k := by positivity
    omega
  rw [word_value, Nat.mod_eq_of_lt hb]
  have h := complement_value (word k n)
  simp only [word_length, word_value, Nat.mod_eq_of_lt hn] at h
  omega

lemma decrement_word (k n : ℕ) (hn : n < 2 ^ k) :
    (increment ((word k n).map Bool.not)).map Bool.not =
      word k (if n = 0 then 2 ^ k - 1 else n - 1) := by
  rw [word_complement k n hn, word_increment]
  by_cases hzero : n = 0
  · subst n
    have hp : 0 < 2 ^ k := by positivity
    have he : 2 ^ k - 1 - 0 + 1 = 2 ^ k := by omega
    rw [he, ← word_mod, Nat.mod_self, word_complement k 0 hp]
    simp
  · have hb : 2 ^ k - 1 - n + 1 < 2 ^ k := by omega
    rw [word_complement k _ hb]
    congr 1
    simp only [if_neg hzero]
    omega

lemma decrement_carry (k n : ℕ) (hn : n < 2 ^ k) :
    carry ((word k n).map Bool.not) = decide (n = 0) := by
  have hb : 2 ^ k - 1 - n < 2 ^ k := by
    have hp : 0 < 2 ^ k := by positivity
    omega
  rw [word_complement k n hn, word_carry k _ hb]
  have hh : (2 ^ k - 1 - n + 1 = 2 ^ k) ↔ n = 0 := by omega
  simp only [hh]

end Lax434930Proofs.SavitchProofs.BinaryCounter
