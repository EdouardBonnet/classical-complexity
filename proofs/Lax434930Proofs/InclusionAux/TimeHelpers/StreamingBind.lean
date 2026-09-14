import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingAppend
import Lax434930Proofs.InclusionAux.TimeCompiler.StackClear

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename Lax434930Proofs.InclusionAux.TimeCompiler.StackClear
open CNFOutput Lax434930.PolynomialTime Polynomial

variable {I W V : Type} [DecidableEq I] [DecidableEq W] [DecidableEq V]

def extend (a : I → Word) (w : Word) : Option I → Word := fun i => i.elim w a

abbrev BindWork (W V : Type) := Bool ⊕ (W ⊕ V)

def bindLeft : Key I W → Key I (BindWork W V)
  | .input i => .input i
  | .output => .work (.inl false)
  | .work w => .work (.inr (.inl w))

def bindRight : Key (Option I) V → Key I (BindWork W V)
  | .input none => .work (.inl true)
  | .input (some i) => .input i
  | .output => .output
  | .work v => .work (.inr (.inr v))

lemma bindLeft_injective : Function.Injective (bindLeft (I := I) (W := W) (V := V)) := by
  intro k l h
  cases k <;> cases l <;> simp_all [bindLeft]

lemma bindRight_injective : Function.Injective (bindRight (I := I) (W := W) (V := V)) := by
  intro k l h
  cases k <;> cases l <;> (try casesm* Option _) <;> simp_all [bindRight]

def bindStore (a : I → Word) (tail argument buffer : Word) (scratch : Option Bool) :
    BitStore (Key I (BindWork W V)) Unit :=
  ⟨((), scratch), fun k => match k with
    | .input i => a i
    | .output => tail
    | .work (.inl false) => buffer
    | .work (.inl true) => argument
    | .work (.inr _) => []⟩

lemma bindStore_empty (a : I → Word) (tail : Word) (scratch : Option Bool) :
    bindStore (W := W) (V := V) a tail [] [] scratch = store a tail scratch := by
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | (b | (w | v)) <;> try rfl
  cases b <;> rfl

lemma bindStore_buffer (a : I → Word) (tail w : Word) (scratch : Option Bool) :
    emitted (Key.work (.inl false)) w (store (W := BindWork W V) a tail scratch) =
      bindStore a tail [] w.reverse none := by
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | (b | (w | v)) <;> try simp [emitted, store, bindStore]
  cases b <;> simp [emitted, store, bindStore]

lemma bindStore_output (a : I → Word) (tail argument buffer w : Word) (scratch : Option Bool) :
    emitted Key.output w (bindStore (W := W) (V := V) a tail argument buffer scratch) =
      bindStore a (w.reverse ++ tail) argument buffer none := by
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | (b | (w | v)) <;> try simp [emitted, bindStore]
  cases b <;> simp [emitted, bindStore]

lemma bindStore_transfer (a : I → Word) (tail w : Word) :
    Executes (transfer (Key.work (.inl false)) (.work (.inl true)))
      (bindStore (W := W) (V := V) a tail [] w.reverse none)
      (bindStore a tail w [] none) (3 * w.length + 2) := by
  have h := transfer_store (Key.work (.inl false)) (.work (.inl true)) (by simp)
    (bindStore (W := W) (V := V) a tail [] w.reverse none)
  convert h using 1
  · apply Store.ext <;> try rfl
    funext k
    rcases k with i | _ | (b | (w | v)) <;> try simp [bindStore]
    cases b <;> simp [bindStore]
  · simp [bindStore]

lemma bindStore_clear (a : I → Word) (tail w : Word) :
    Executes (clear (Key.work (.inl true))) (bindStore (W := W) (V := V) a tail w [] none)
      (store a tail none) (2 * w.length + 2) := by
  have h := clear_store (Key.work (.inl true)) (bindStore (W := W) (V := V) a tail w [] none)
  convert h using 1
  apply Store.ext <;> try rfl
  funext k
  rcases k with i | _ | (b | (w | v)) <;> try simp [bindStore, store]
  cases b <;> simp [bindStore, store]
  all_goals rfl

noncomputable def Emitter.bind {f : (I → Word) → Word} {g : (Option I → Word) → Word}
    (p : Emitter I f) (q : Emitter (Option I) g) :
    Emitter I (fun a => g (extend a (f a))) where
  Workspace := BindWork p.Workspace q.Workspace
  program := .seq (rename bindLeft p.program)
    (.seq (transfer (.work (.inl false)) (.work (.inl true)))
      (.seq (rename bindRight q.program) (clear (.work (.inl true)))))
  bound := C 6 * p.bound + q.bound.comp (X + p.bound) + C 4
  length_bound a b hb := by
    have hf := p.length_bound a b hb
    have hq := q.length_bound (extend a (f a)) (b + p.bound.eval b) (by
      intro i; cases i with
      | none => exact le_trans hf (Nat.le_add_left _ _)
      | some i => exact le_trans (hb i) (Nat.le_add_right _ _))
    simp only [eval_add, eval_mul, eval_C, eval_comp, eval_X]
    omega
  executes a tail scratch b hb := by
    have hf := p.length_bound a b hb
    obtain ⟨t, ht, hp⟩ := p.run_in bindLeft bindLeft_injective
      (store (W := BindWork p.Workspace q.Workspace) a tail scratch) a b
      (by intro i; rfl) (by intro w; rfl) hb
    simp only [bindLeft, bindStore_buffer] at hp
    have htransfer := bindStore_transfer (W := p.Workspace) (V := q.Workspace) a tail (f a)
    obtain ⟨u, hu, hq⟩ := q.run_in bindRight bindRight_injective
      (bindStore (W := p.Workspace) (V := q.Workspace) a tail (f a) [] none)
      (extend a (f a)) (b + p.bound.eval b)
      (by intro i; cases i <;> rfl) (by intro w; rfl) (by
        intro i; cases i with
        | none => exact le_trans hf (Nat.le_add_left _ _)
        | some i => exact le_trans (hb i) (Nat.le_add_right _ _))
    simp only [bindRight, bindStore_output] at hq
    have hclear := bindStore_clear (W := p.Workspace) (V := q.Workspace) a
      ((g (extend a (f a))).reverse ++ tail) (f a)
    refine ⟨t + (3 * (f a).length + 2 + (u + (2 * (f a).length + 2))), ?_,
      Executes.seq hp (.seq htransfer (.seq hq hclear))⟩
    simp only [eval_add, eval_mul, eval_C, eval_comp, eval_X]
    omega

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
