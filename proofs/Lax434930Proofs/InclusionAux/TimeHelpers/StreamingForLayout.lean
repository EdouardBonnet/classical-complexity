import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingBind
import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingSource
import Lax434930Proofs.InclusionAux.TimeCompiler.StackFor

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename Lax434930Proofs.InclusionAux.TimeCompiler.StackFor CNFOutput Lax434930.PolynomialTime

variable {I W : Type} [DecidableEq I] [DecidableEq W]

inductive ForSlot where
  | domain | counter | coord | temporary
  deriving DecidableEq, Fintype

abbrev ForWork (W : Type) := ForSlot ⊕ (Bool ⊕ W)

def forLength : Key I Bool → Key I (ForWork W)
  | .input i => .input i
  | .output => .work (.inl .domain)
  | .work w => .work (.inr (.inl w))

def forBody : Key (Option I) W → Key I (ForWork W)
  | .input none => .work (.inl .coord)
  | .input (some i) => .input i
  | .output => .output
  | .work w => .work (.inr (.inr w))

lemma forLength_injective : Function.Injective (forLength (I := I) (W := W)) := by
  intro k l h; cases k <;> cases l <;> simp_all [forLength]

lemma forBody_injective : Function.Injective (forBody (I := I) (W := W)) := by
  intro k l h; cases k <;> cases l <;> (try casesm* Option _) <;> simp_all [forBody]

def forStore (a : I → Word) (n : ℕ) (tail : Word) : BitStore (Key I (ForWork W)) Unit :=
  ⟨((), none), fun k => match k with
    | .input i => a i
    | .output => tail
    | .work (.inl .domain) => List.replicate n true
    | .work _ => []⟩

lemma forStore_start (a : I → Word) (n : ℕ) (tail : Word) (scratch : Option Bool) :
    emitted (Key.work (.inl ForSlot.domain)) (List.replicate n true)
      (store (W := ForWork W) a tail scratch) = forStore a n tail := by
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | (s | (b | w)) <;> try simp [emitted, store, forStore]
  cases s <;> simp [emitted, store, forStore]

lemma forStore_clear (a : I → Word) (n : ℕ) (tail : Word) :
    Executes (Lax434930Proofs.InclusionAux.TimeCompiler.StackClear.clear (.work (.inl ForSlot.domain)))
      (forStore (W := W) a n tail) (store a tail none) (2 * n + 2) := by
  have h := Lax434930Proofs.InclusionAux.TimeCompiler.StackClear.clear_store (.work (.inl ForSlot.domain))
    (forStore (W := W) a n tail)
  convert h using 1
  · apply Store.ext <;> try rfl
    funext k
    rcases k with i | _ | (s | (b | w)) <;> try simp [store, forStore]
    cases s <;> simp [store, forStore]
  · simp [forStore]

lemma forStore_emitted (a : I → Word) (n i remaining : ℕ) (tail w : Word) (scratch : Option Bool) :
    emitted Key.output w
      (pack (forStore (W := W) a n) (.work (.inl .counter)) (.work (.inl .coord)) tail i remaining scratch) =
    pack (forStore a n) (.work (.inl .counter)) (.work (.inl .coord))
      (w.reverse ++ tail) i remaining none := by
  apply Store.ext <;> try rfl
  funext k
  rcases k with j | _ | (s | (b | v)) <;> try simp [emitted, pack, working, forStore]
  cases s <;> simp [emitted, pack, working, forStore]

lemma foldRange_emitting (f : ℕ → Word) (start n : ℕ) (tail : Word) :
    foldRange (fun i w => (f i).reverse ++ w) start n tail =
      ((List.range' start n).flatMap f).reverse ++ tail := by
  induction n generalizing start tail with
  | zero => rfl
  | succ n ih => simp [foldRange, List.range'_succ, ih, List.reverse_append, List.append_assoc]

lemma flatMap_length_bound {A : Type} (xs : List A) (f : A → Word) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
