import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingFor
import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingDrop
import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingBranch

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename Lax434930Proofs.InclusionAux.TimeCompiler.StackFor
open Lax434930Proofs.InclusionAux.TimeCompiler.StackClear (clear clear_store)
open Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy
open CNFOutput Lax434930.PolynomialTime Polynomial

noncomputable section

variable {I W : Type} [DecidableEq I] [DecidableEq W]

inductive IterateSlot where
  | domain | counter | coord | temporary | accumulator | buffer
  deriving DecidableEq, Fintype

abbrev IterateWork (W : Type) := IterateSlot ⊕ (Bool ⊕ W)

def iterateLength : Key I Bool → Key I (IterateWork W)
  | .input i => .input i
  | .output => .work (.inl .domain)
  | .work w => .work (.inr (.inl w))

def iterateBodyMap : Key (Option I) W → Key I (IterateWork W)
  | .input none => .work (.inl .accumulator)
  | .input (some i) => .input i
  | .output => .work (.inl .buffer)
  | .work w => .work (.inr (.inr w))

lemma iterateLength_injective : Function.Injective (iterateLength (I := I) (W := W)) := by
  intro k l h; cases k <;> cases l <;> simp_all [iterateLength]

lemma iterateBodyMap_injective : Function.Injective (iterateBodyMap (I := I) (W := W)) := by
  intro k l h; cases k <;> cases l <;> (try casesm* Option _) <;> simp_all [iterateBodyMap]

def iterationStore (a : I → Word) (n : ℕ) (tail acc : Word) : BitStore (Key I (IterateWork W)) Unit :=
  ⟨((), none), fun k => match k with
    | .input i => a i
    | .output => tail
    | .work (.inl .domain) => List.replicate n true
    | .work (.inl .accumulator) => acc
    | .work _ => []⟩

def iterationPoint (a : I → Word) (n : ℕ) (tail acc : Word) (remaining i : ℕ)
    (scratch : Option Bool) : BitStore (Key I (IterateWork W)) Unit :=
  pack (iterationStore a n tail) (.work (.inl .counter)) (.work (.inl .coord)) acc i remaining scratch

def iterationBody {f : (Option I → Word) → Word} (p : Emitter (Option I) f) :
    BitProgram (Key I (IterateWork p.Workspace)) Unit :=
  .seq (rename iterateBodyMap p.program)
    (.seq (clear (.work (.inl .accumulator)))
      (transfer (.work (.inl .buffer)) (.work (.inl .accumulator))))

lemma iterationBody_executes {f : (Option I → Word) → Word} (p : Emitter (Option I) f)
    (a : I → Word) (n b : ℕ) (hb : ∀ i, (a i).length ≤ b)
    (tail acc : Word) (ha : acc.length ≤ b) (hf : (f (extend a acc)).length ≤ b)
    (remaining i : ℕ) (scratch : Option Bool) :
    ∃ c, c ≤ p.bound.eval b + 5 * b + 4 ∧ Executes (iterationBody p)
      (iterationPoint a n tail acc remaining i scratch)
      (iterationPoint a n tail (f (extend a acc)) remaining i none) c := by
  let d := iterationPoint (W := p.Workspace) a n tail acc remaining i scratch
  let u := f (extend a acc)
  obtain ⟨c, hc, hp⟩ := p.run_in iterateBodyMap iterateBodyMap_injective d (extend a acc) b
    (by intro j; cases j <;> simp [d, iterationPoint, pack, working, iterationStore, iterateBodyMap, extend])
    (by intro j; simp [d, iterationPoint, pack, working, iterationStore, iterateBodyMap])
    (by intro j; cases j with | none => exact ha | some j => exact hb j)
  let e := emitted (Key.work (.inl IterateSlot.buffer)) u d
  have hclear := clear_store (Key.work (.inl IterateSlot.accumulator)) e
  let r : BitStore (Key I (IterateWork p.Workspace)) Unit :=
    ⟨((), none), Function.update e.stk (.work (.inl .accumulator)) []⟩
  have htransfer := transfer_store (Key.work (.inl IterateSlot.buffer)) (.work (.inl .accumulator))
    (by simp) r
  have hacc : e.stk (.work (.inl .accumulator)) = acc := by
    simp [e, d, emitted, iterationPoint, pack, working, iterationStore]
  have hbuffer : r.stk (.work (.inl .buffer)) = u.reverse := by
    simp [r, e, d, emitted, iterationPoint, pack, working, iterationStore]
  have hout : (⟨(r.state.1, none), Function.update
      (Function.update r.stk (.work (.inl .buffer)) []) (.work (.inl .accumulator))
      ((r.stk (.work (.inl .buffer))).reverse ++ r.stk (.work (.inl .accumulator)))⟩ :
      BitStore (Key I (IterateWork p.Workspace)) Unit) =
      iterationPoint a n tail u remaining i none := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with j | _ | (slot | (bit | v)) <;>
      try simp [r, e, d, emitted, iterationPoint, pack, working, iterationStore]
    cases slot <;> simp [r, e, d, emitted, iterationPoint, pack, working, iterationStore]
  rw [hout] at htransfer
  refine ⟨c + ((2 * acc.length + 2) + (3 * u.length + 2)), by dsimp [u]; omega, ?_⟩
  have hh := Executes.seq hp (Executes.seq hclear htransfer)
  simpa only [hacc, hbuffer, List.length_reverse] using! hh

lemma foldRange_iterate {A : Type} (f : A → A) (start count : ℕ) (a : A) :
    foldRange (fun _ => f) start count a = f^[count] a := by
  induction count generalizing start a with
  | zero => rfl
  | succ count ih => simpa only [foldRange, Function.iterate_succ_apply] using ih (start + 1) (f a)

def iterationInit (count source : I) : BitProgram (Key I (IterateWork W)) Unit :=
  .seq (rename iterateLength (Emitter.length count).program)
    (copy (.input source) (.work (.inl .accumulator)) (.work (.inl .temporary)))

lemma iterationInit_executes (count source : I) (a : I → Word) (tail : Word)
    (scratch : Option Bool) (b : ℕ) (hb : ∀ i, (a i).length ≤ b) :
    ∃ c, c ≤ 17 * b + 10 ∧ Executes (iterationInit (W := W) count source)
      (store a tail scratch) (iterationStore a (a count).length tail (a source)) c := by
  obtain ⟨c, hc, hp⟩ := (Emitter.length count).run_in iterateLength iterateLength_injective
    (store (W := IterateWork W) a tail scratch) a b (by intro i; rfl) (by intro i; rfl) hb
  have he : emitted (Key.work (.inl IterateSlot.domain)) (List.replicate (a count).length true)
      (store (W := IterateWork W) a tail scratch) = iterationStore a (a count).length tail [] := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with j | _ | (slot | (bit | v)) <;> try simp [emitted, store, iterationStore]
    cases slot <;> simp [emitted, store, iterationStore]
  simp only [iterateLength, he] at hp
  have hcopy := copy_store (Key.input source) (.work (.inl IterateSlot.accumulator))
    (.work (.inl IterateSlot.temporary)) (by simp) (by simp) (by simp)
    (iterationStore (W := W) a (a count).length tail []) rfl
  have hout : (⟨((), none), Function.update (iterationStore (W := W) a (a count).length tail []).stk
      (.work (.inl .accumulator)) (a source)⟩ : BitStore (Key I (IterateWork W)) Unit) =
      iterationStore a (a count).length tail (a source) := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with j | _ | (slot | (bit | v)) <;> try simp [iterationStore]
    cases slot <;> simp [iterationStore]
  simp only [iterationStore, List.append_nil] at hcopy
  change Executes _ _ _ _ at hcopy
  have hcopy' : Executes (copy (.input source) (.work (.inl .accumulator)) (.work (.inl .temporary)))
      (iterationStore (W := W) a (a count).length tail [])
      (iterationStore a (a count).length tail (a source)) (7 * (a source).length + 4) := by
    rw [← hout]
    exact hcopy
  refine ⟨c + (7 * (a source).length + 4), ?_, .seq hp hcopy'⟩
  simp only [Emitter.length, Emitter.congr, Emitter.sourceMap, eval_add, eval_mul, eval_C, eval_X] at hc
  have := hb source
  omega

def iterationFinish : BitProgram (Key I (IterateWork W)) Unit :=
  .seq (clear (.work (.inl .domain))) (transfer (.work (.inl .accumulator)) .output)

lemma iterationFinish_executes (a : I → Word) (n : ℕ) (tail acc : Word) :
    Executes (iterationFinish (W := W)) (iterationStore a n tail acc)
      (store a (acc.reverse ++ tail) none) ((2 * n + 2) + (3 * acc.length + 2)) := by
  have hc := clear_store (Key.work (.inl IterateSlot.domain)) (iterationStore (W := W) a n tail acc)
  let d : BitStore (Key I (IterateWork W)) Unit :=
    ⟨((), none), Function.update (iterationStore a n tail acc).stk (.work (.inl .domain)) []⟩
  have ht := transfer_store (Key.work (.inl IterateSlot.accumulator)) .output (by simp) d
  have he : (⟨(d.state.1, none), Function.update
      (Function.update d.stk (.work (.inl .accumulator)) []) .output
      ((d.stk (.work (.inl .accumulator))).reverse ++ d.stk .output)⟩ :
      BitStore (Key I (IterateWork W)) Unit) = store a (acc.reverse ++ tail) none := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with j | _ | (slot | (bit | v)) <;> try simp [d, iterationStore, store]
    cases slot <;> simp [d, iterationStore, store]
  rw [he] at ht
  simpa [iterationStore, d] using! Executes.seq hc ht

lemma iterate_length {f : (Option I → Word) → Word}
    (h : ∀ a b, (∀ i, (a i).length ≤ b) → ∀ acc, acc.length ≤ b →
      (f (extend a acc)).length ≤ b)
    (a : I → Word) (b : ℕ) (hb : ∀ i, (a i).length ≤ b) (acc : Word) (ha : acc.length ≤ b) (n : ℕ) :
    ((fun acc => f (extend a acc))^[n] acc).length ≤ b := by
  induction n generalizing acc with
  | zero => exact ha
  | succ n ih => exact ih _ (h a b hb acc ha)

noncomputable def Emitter.iterate (count source : I) {f : (Option I → Word) → Word}
    (p : Emitter (Option I) f)
    (h : ∀ a b, (∀ i, (a i).length ≤ b) → ∀ acc, acc.length ≤ b →
      (f (extend a acc)).length ≤ b) :
    Emitter I (fun a => (fun acc => f (extend a acc))^[(a count).length] (a source)) where
  Workspace := IterateWork p.Workspace
  program := .seq (iterationInit count source)
    (.seq (forValues (.work (.inl .domain)) (.work (.inl .counter)) (.work (.inl .coord))
      (.work (.inl .temporary)) (iterationBody p)) iterationFinish)
  bound := (p.bound + C 5 * X + C 40) * X + C 24
  length_bound a b hb := by
    have hh := iterate_length h a b hb (a source) (hb source) (a count).length
    simp only [eval_add, eval_mul, eval_C, eval_X]
    nlinarith
  executes a tail scratch b hb := by
    let n := (a count).length
    have hn : n ≤ b := hb count
    let V := {acc : Word // acc.length ≤ b}
    let F : V → V := fun acc => ⟨f (extend a acc.val), h a b hb acc.val acc.property⟩
    let base : V → BitStore (Key I (IterateWork p.Workspace)) Unit :=
      fun acc => iterationStore a n tail acc.val
    let start : V := ⟨a source, hb source⟩
    have hbody : ∀ i, i < n → ∀ acc remaining scratch,
        ∃ cost scratch', cost ≤ p.bound.eval b + 5 * b + 4 ∧ Executes (iterationBody p)
          (pack base (.work (.inl .counter)) (.work (.inl .coord)) acc i remaining scratch)
          (pack base (.work (.inl .counter)) (.work (.inl .coord)) (F acc) i remaining scratch') cost := by
      intro i hi acc remaining scratch
      obtain ⟨c, hc, he⟩ := iterationBody_executes p a n b hb tail acc.val acc.property
        (h a b hb acc.val acc.property) remaining i scratch
      exact ⟨c, none, hc, he⟩
    obtain ⟨t, ht, hinit⟩ := iterationInit_executes (W := p.Workspace) count source a tail scratch b hb
    obtain ⟨u, hu, hfor⟩ := forValues_executes base (.work (.inl .domain)) (.work (.inl .counter))
      (.work (.inl .coord)) (.work (.inl .temporary)) (by simp) (iterationBody p) (fun _ => F)
      n (p.bound.eval b + 5 * b + 4) (by intro acc; rfl) (by intro acc; rfl)
      (by intro acc; rfl) hbody start rfl
    have hval (k : ℕ) (v : V) : (F^[k] v).val = (fun acc => f (extend a acc))^[k] v.val := by
      induction k generalizing v with
      | zero => rfl
      | succ k ih => exact ih (F v)
    have hfinal : reset (base (foldRange (fun _ => F) 0 n start)) =
        iterationStore a n tail ((fun acc => f (extend a acc))^[n] (a source)) := by
      rw [foldRange_iterate]
      change iterationStore a n tail (F^[n] start).val = _
      rw [hval]
    rw [hfinal] at hfor
    have hfinish := iterationFinish_executes (W := p.Workspace) a n tail
      ((fun acc => f (extend a acc))^[n] (a source))
    have hlength := iterate_length h a b hb (a source) (hb source) n
    refine ⟨t + (u + ((2 * n + 2) +
      (3 * ((fun acc => f (extend a acc))^[n] (a source)).length + 2))), ?_,
      .seq hinit (.seq hfor hfinish)⟩
    simp only [eval_add, eval_mul, eval_C, eval_X]
    have hm := Nat.mul_le_mul_left (p.bound.eval b + 5 * b + 4 + 12) hn
    nlinarith

lemma range_getElem (xs : Word) (n : ℕ) :
    (List.range n).flatMap (fun i => xs[i]?.toList) = xs.take n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.range_succ, List.flatMap_append, ih, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.take_succ]

noncomputable def Emitter.take (source count : I) : Emitter I (fun a => (a source).take (a count).length) := by
  let item := (Emitter.drop (some source) (none : Option I)).bind
    ((Emitter.inspect none Option.isSome).bind
      (Emitter.branch none (Emitter.inspect (some none) (fun b => b.getD false)) (Emitter.constant [])))
  have he : ∀ a : Option I → Word,
      (if ((a (some source)).drop (a none).length).head?.isSome then
        [((a (some source)).drop (a none).length).head?.getD false] else []) =
      (a (some source))[(a none).length]?.toList := by
    intro a
    simp only [List.head?_drop]
    cases (a (some source))[(a none).length]? <;> rfl
  let q : Emitter (Option I) (fun a => (a (some source))[(a none).length]?.toList) :=
    item.congr (by intro a; simpa [extend] using he a)
  exact (Emitter.forRange count q).congr (by intro a; simpa [extend] using range_getElem (a source) (a count).length)

noncomputable def Emitter.clipped (cap : I) {f : (I → Word) → Word} (p : Emitter I f) :
    Emitter I (fun a => (f a).take (a cap).length) :=
  (p.bind (Emitter.take none (some cap))).congr (by intro a; rfl)

end

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
