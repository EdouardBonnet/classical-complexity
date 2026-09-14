import Lax434930Proofs.InclusionAux.TimeHelpers.OutputDivision
import Lax434930Proofs.InclusionAux.TimeHelpers.OutputPolynomials

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930.PolynomialTime

variable {I : Type}

def Number.min (n m : Number I) : Number I := Number.choose (Test.lt n m) n m

lemma Number.min_value (n m : Number I) (a : I → Word) :
    (Number.min n m).value a = Nat.min (n.value a) (m.value a) := by
  simp only [Number.min, Number.choose, Test.lt, decide_eq_true_eq, Nat.min_def]
  split_ifs <;> omega

def Code.iterateValues (count cap initial : Code I) (body : Code (Option I)) : Code I :=
  .bind count (.bind (cap.rename some) (.bind (initial.rename (some ∘ some))
    (.iterate (some (some none)) (some none) none (body.rename (Option.map (some ∘ some ∘ some))))))

lemma extend_three (a : I → Word) (x y z acc : Word) :
    extend (extend (extend (extend a x) y) z) acc ∘ Option.map (some ∘ some ∘ some) = extend a acc := by
  funext i; cases i <;> rfl

lemma Code.eval_iterateValues (count cap initial : Code I) (body : Code (Option I)) (a : I → Word) :
    (Code.iterateValues count cap initial body).eval a =
      (fun acc => (body.eval (extend a acc)).take (cap.eval a).length)^[(count.eval a).length] (initial.eval a) := by
  simp only [iterateValues, eval, eval_rename, extend_some, extend_two_some, extend_three]
  rfl

lemma clipped_mul (x base cap : ℕ) : min (min x cap * base) cap = min (x * base) cap := by
  by_cases hb : base = 0
  · simp [hb]
  by_cases hx : x ≤ cap
  · simp [Nat.min_eq_left hx]
  · have h₁ : cap ≤ cap * base := by
      simpa using Nat.mul_le_mul_left cap (show 1 ≤ base by omega)
    have h₂ : cap ≤ x * base := by
      have hh : x ≤ x * base := by simpa using Nat.mul_le_mul_left x (show 1 ≤ base by omega)
      omega
    simp [Nat.min_eq_right (by omega : cap ≤ x), Nat.min_eq_right h₁, Nat.min_eq_right h₂]

def cappedPower (base cap n : ℕ) : ℕ := (fun value => min (value * base) cap)^[n] (min 1 cap)

lemma cappedPower_eq (base cap n : ℕ) : cappedPower base cap n = min (base ^ n) cap := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cappedPower, Function.iterate_succ_apply'] at *
    rw [ih, clipped_mul, pow_succ]

lemma iterate_replicate (f : Word → Word) (g : ℕ → ℕ)
    (h : ∀ n, f (List.replicate n true) = List.replicate (g n) true) (count initial : ℕ) :
    f^[count] (List.replicate initial true) = List.replicate (g^[count] initial) true := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih => simp only [Function.iterate_succ_apply, h, ih]

def Number.powCap (base exponent cap : Number I) : Number I where
  value a := cappedPower (base.value a) (cap.value a) (exponent.value a)
  code := Code.iterateValues exponent.code cap.code ((Number.constant 1).min cap).code
    (((Number.length none).mul (base.rename some)).code)
  correct a := by
    rw [Code.eval_iterateValues]
    simp only [Number.correct, List.length_replicate, Number.min_value, Number.constant]
    unfold cappedPower
    apply iterate_replicate
    intro n
    simp [Number.correct, Number.mul, Number.length, Number.rename, extend,
      List.take_replicate, Nat.min_comm]

lemma Number.powCap_value (base exponent cap : Number I) (a : I → Word) :
    (base.powCap exponent cap).value a = Nat.min (base.value a ^ exponent.value a) (cap.value a) :=
  cappedPower_eq _ _ _

lemma div_capped (n d : ℕ) : n / min d (n + 1) = n / d := by
  by_cases hd : d ≤ n + 1
  · rw [Nat.min_eq_left hd]
  · rw [Nat.min_eq_right (by omega : n + 1 ≤ d), Nat.div_eq_of_lt (by omega : n < n + 1),
      Nat.div_eq_of_lt (by omega : n < d)]

def Number.digit (value base index : Number I) : Number I :=
  (value.div (base.powCap index (value.add (.constant 1)))).mod base

lemma Number.digit_value (value base index : Number I) (a : I → Word) :
    (Number.digit value base index).value a = value.value a / base.value a ^ index.value a % base.value a := by
  simp only [Number.digit, Number.mod, Number.div, Number.powCap_value, Number.add, Number.constant, div_capped]

lemma emitted_choices (xs : List ℕ) (p : ℕ → Bool) :
    (xs.flatMap (fun i => if p i then [true] else [])).head?.isSome = xs.any p := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : p i <;> simp [h, ih]

def Test.exists (bound : Number I) (body : Test (Option I)) : Test I where
  value a := (List.range (bound.value a)).any (fun i => body.value (extend a (List.replicate i true)))
  code := .bind (Code.loop bound (Code.when body (.literal [true]) (.literal [])))
    (.inspect none Option.isSome)
  correct a := by
    simp only [Code.eval, Code.eval_loop, Code.eval_when, extend, Option.elim_none]
    rw [emitted_choices]

lemma Test.exists_true (bound : Number I) (body : Test (Option I)) (a : I → Word) :
    (Test.exists bound body).value a = true ↔
      ∃ i, i < bound.value a ∧ body.value (extend a (List.replicate i true)) = true := by
  simp [Test.exists, List.any_eq_true]

def Test.forall (bound : Number I) (body : Test (Option I)) : Test I := (Test.exists bound body.not).not

lemma Test.forall_true (bound : Number I) (body : Test (Option I)) (a : I → Word) :
    (Test.forall bound body).value a = true ↔
      ∀ i, i < bound.value a → body.value (extend a (List.replicate i true)) = true := by
  simp [Test.forall, Test.not, Test.exists, List.any_eq_false]

def Test.anyList {A : Type} (xs : List A) (f : A → Test I) : Test I :=
  xs.foldr (fun x rest => (f x).or rest) (.constant false)

lemma Test.anyList_true {A : Type} (xs : List A) (f : A → Test I) (a : I → Word) :
    (Test.anyList xs f).value a = true ↔ ∃ x ∈ xs, (f x).value a = true := by
  induction xs with
  | nil => simp [Test.anyList, Test.constant]
  | cons x xs ih =>
    change ((f x).value a || (Test.anyList xs f).value a) = true ↔ _
    simp [ih]

noncomputable def Test.anyFinite {A : Type} [Fintype A] (f : A → Test I) : Test I :=
  Test.anyList Finset.univ.toList f

lemma Test.anyFinite_true {A : Type} [Fintype A] (f : A → Test I) (a : I → Word) :
    (Test.anyFinite f).value a = true ↔ ∃ x, (f x).value a = true := by
  simp [Test.anyFinite, Test.anyList_true]

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
