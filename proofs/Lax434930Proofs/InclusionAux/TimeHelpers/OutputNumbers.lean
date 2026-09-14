import Lax434930Proofs.InclusionAux.TimeHelpers.OutputCode

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930.PolynomialTime

structure Number (I : Type) where
  value : (I → Word) → ℕ
  code : Code I
  correct : ∀ a, code.eval a = List.replicate (value a) true

variable {I J : Type}

def Number.constant (n : ℕ) : Number I := ⟨fun _ => n, .literal (List.replicate n true), fun _ => rfl⟩

def Number.length (i : I) : Number I := ⟨fun a => (a i).length, .length i, fun _ => rfl⟩

def Number.rename (f : I → J) (n : Number I) : Number J where
  value a := n.value (a ∘ f)
  code := n.code.rename f
  correct a := (Code.eval_rename f n.code a).trans (n.correct _)

def Number.add (n m : Number I) : Number I where
  value a := n.value a + m.value a
  code := .append n.code m.code
  correct a := by simp only [Code.eval, n.correct, m.correct, List.replicate_add]

@[simp] lemma extend_some (a : I → Word) (w : Word) : extend a w ∘ some = a := rfl

@[simp] lemma extend_two_some (a : I → Word) (u v : Word) :
    extend (extend a u) v ∘ (some ∘ some) = a := rfl

lemma flatMap_constant {A : Type} (xs : List A) (w : Word) :
    (xs.flatMap fun _ => w) = (List.replicate xs.length w).flatten := by
  induction xs <;> simp_all [List.replicate_succ]

def Number.mul (n m : Number I) : Number I where
  value a := n.value a * m.value a
  code := .bind n.code (.forRange none (m.code.rename (some ∘ some)))
  correct a := by
    simp [Code.eval, n.correct, Code.eval_rename, extend, Function.comp_def, m.correct,
      flatMap_constant]

def Number.sub (n m : Number I) : Number I where
  value a := n.value a - m.value a
  code := .bind n.code (.bind (m.code.rename some) (.drop (some none) none))
  correct a := by
    simp [Code.eval, n.correct, Code.eval_rename, extend, Function.comp_def, m.correct]

def Code.loop (n : Number I) (body : Code (Option I)) : Code I :=
  .bind n.code (.forRange none (body.rename (Option.map some)))

lemma extend_skip (a : I → Word) (u v : Word) :
    extend (extend a u) v ∘ Option.map some = extend a v := by
  funext i
  cases i <;> rfl

lemma Code.eval_loop (n : Number I) (body : Code (Option I)) (a : I → Word) :
    (Code.loop n body).eval a = (List.range (n.value a)).flatMap
      (fun i => body.eval (extend a (List.replicate i true))) := by
  simp [loop, eval, n.correct, Code.eval_rename, extend_skip, extend]

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
