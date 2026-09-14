import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingFor
import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingBranch
import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingDrop
import Lax434930Proofs.InclusionAux.TimeHelpers.StreamingIterate

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930.PolynomialTime

/-- Finite expressions for strings, with unary counters and bounded loops. -/
inductive Code : Type → Type 1 where
  | literal {I : Type} (w : Word) : Code I
  | source {I : Type} (i : I) : Code I
  | length {I : Type} (i : I) : Code I
  | drop {I : Type} (source index : I) : Code I
  | inspect {I : Type} (i : I) (f : Option Bool → Bool) : Code I
  | append {I : Type} (p q : Code I) : Code I
  | bind {I : Type} (p : Code I) (q : Code (Option I)) : Code I
  | branch {I : Type} (i : I) (p q : Code I) : Code I
  | forRange {I : Type} (domain : I) (body : Code (Option I)) : Code I
  | iterate {I : Type} (count cap source : I) (body : Code (Option I)) : Code I

def Code.eval : {I : Type} → Code I → (I → Word) → Word
  | _, .literal w, _ => w
  | _, .source i, a => a i
  | _, .length i, a => List.replicate (a i).length true
  | _, .drop src idx, a => (a src).drop (a idx).length
  | _, .inspect i f, a => [f (a i).head?]
  | _, .append p q, a => p.eval a ++ q.eval a
  | _, .bind p q, a => q.eval (extend a (p.eval a))
  | _, .branch i p q, a => if (a i).head?.getD false then p.eval a else q.eval a
  | _, .forRange domain body, a => (List.range (a domain).length).flatMap
      (fun i => body.eval (extend a (List.replicate i true)))
  | _, .iterate count cap src body, a =>
      (fun acc => (body.eval (extend a acc)).take (a cap).length)^[(a count).length] (a src)

noncomputable def Code.emitter : {I : Type} → [DecidableEq I] → (p : Code I) → Emitter I p.eval
  | _, _, .literal w => Emitter.constant w
  | _, _, .source i => Emitter.source i
  | _, _, .length i => Emitter.length i
  | _, _, .drop src idx => Emitter.drop src idx
  | _, _, .inspect i f => Emitter.inspect i f
  | _, _, .append p q => p.emitter.append q.emitter
  | _, _, .bind p q => p.emitter.bind q.emitter
  | _, _, .branch i p q => Emitter.branch i p.emitter q.emitter
  | _, _, .forRange domain body => Emitter.forRange domain body.emitter
  | _, _, .iterate count cap src body =>
      Emitter.iterate count src (body.emitter.clipped (some cap))
        (by intro a b hb acc ha; exact (List.length_take_le _ _).trans (hb cap))

def Code.rename : {I J : Type} → (I → J) → Code I → Code J
  | _, _, _, .literal w => .literal w
  | _, _, f, .source i => .source (f i)
  | _, _, f, .length i => .length (f i)
  | _, _, f, .drop src idx => .drop (f src) (f idx)
  | _, _, f, .inspect i g => .inspect (f i) g
  | _, _, f, .append p q => .append (p.rename f) (q.rename f)
  | _, _, f, .bind p q => .bind (p.rename f) (q.rename (Option.map f))
  | _, _, f, .branch i p q => .branch (f i) (p.rename f) (q.rename f)
  | _, _, f, .forRange domain body => .forRange (f domain) (body.rename (Option.map f))
  | _, _, f, .iterate count cap src body =>
      .iterate (f count) (f cap) (f src) (body.rename (Option.map f))

lemma extend_map {I J : Type} (f : I → J) (a : J → Word) (w : Word) :
    extend a w ∘ Option.map f = extend (a ∘ f) w := by
  funext i
  cases i <;> rfl

lemma Code.eval_rename {I J : Type} (f : I → J) (p : Code I) (a : J → Word) :
    (p.rename f).eval a = p.eval (a ∘ f) := by
  induction p generalizing J with
  | literal w | source i | length i | drop i j | inspect i g => rfl
  | append p q ihp ihq => simp [rename, eval, ihp, ihq]
  | bind p q ihp ihq => simp [rename, eval, ihp, ihq, extend_map]
  | branch i p q ihp ihq => simp [rename, eval, ihp, ihq, Function.comp_def]
  | forRange domain body ih => simp only [rename, eval, ih, extend_map]; rfl
  | iterate count cap src body ih => simp only [rename, eval, ih, extend_map]; rfl

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
