import Lax434930Proofs.InclusionAux.TimeHelpers.OutputNumbers

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930.PolynomialTime

structure Test (I : Type) where
  value : (I → Word) → Bool
  code : Code I
  correct : ∀ a, code.eval a = [value a]

variable {I J : Type}

def Test.constant (b : Bool) : Test I := ⟨fun _ => b, .literal [b], fun _ => rfl⟩

def Test.rename (f : I → J) (t : Test I) : Test J where
  value a := t.value (a ∘ f)
  code := t.code.rename f
  correct a := (Code.eval_rename f t.code a).trans (t.correct _)

def Code.when (t : Test I) (p q : Code I) : Code I :=
  .bind t.code (.branch none (p.rename some) (q.rename some))

lemma Code.eval_when (t : Test I) (p q : Code I) (a : I → Word) :
    (Code.when t p q).eval a = if t.value a then p.eval a else q.eval a := by
  simp [Code.when, Code.eval, t.correct, Code.eval_rename, extend]

def Test.not (t : Test I) : Test I where
  value a := !(t.value a)
  code := Code.when t (.literal [false]) (.literal [true])
  correct a := by rw [Code.eval_when]; cases t.value a <;> rfl

def Test.and (t u : Test I) : Test I where
  value a := t.value a && u.value a
  code := Code.when t u.code (.literal [false])
  correct a := by rw [Code.eval_when]; cases t.value a <;> simp [Code.eval, u.correct]

def Test.or (t u : Test I) : Test I where
  value a := t.value a || u.value a
  code := Code.when t (.literal [true]) u.code
  correct a := by rw [Code.eval_when]; cases t.value a <;> simp [Code.eval, u.correct]

lemma unary_nonempty (n m : ℕ) :
    (List.replicate (m - n) true).head?.isSome = decide (n < m) := by
  simp only [List.head?_replicate]
  split_ifs with h <;> simp_all <;> omega

def Test.lt (n m : Number I) : Test I where
  value a := decide (n.value a < m.value a)
  code := .bind n.code (.bind (m.code.rename some)
    (.bind (.drop none (some none)) (.inspect none Option.isSome)))
  correct a := by
    simp [Code.eval, Code.eval_rename, n.correct, m.correct, extend, unary_nonempty]

def Test.eq (n m : Number I) : Test I := ((Test.lt n m).or (Test.lt m n)).not

lemma Test.eq_value (n m : Number I) (a : I → Word) :
    (Test.eq n m).value a = decide (n.value a = m.value a) := by
  apply Bool.eq_iff_iff.mpr
  simp [Test.eq, Test.not, Test.or, Test.lt]
  omega

def Number.choose (t : Test I) (n m : Number I) : Number I where
  value a := if t.value a then n.value a else m.value a
  code := Code.when t n.code m.code
  correct a := by rw [Code.eval_when]; split <;> first | exact n.correct a | exact m.correct a

def Test.input (i : I) (n : Number I) : Test I where
  value a := ((a i)[n.value a]?).getD false
  code := .bind n.code (.bind (.drop (some i) none) (.inspect none (fun b => b.getD false)))
  correct a := by
    simp [Code.eval, n.correct, extend, List.head?_drop]

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
