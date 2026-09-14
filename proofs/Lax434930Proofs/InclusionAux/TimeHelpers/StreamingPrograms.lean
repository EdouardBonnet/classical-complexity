import Lax434930Proofs.InclusionAux.TimeHelpers.Emitted
import Lax434930Proofs.InclusionAux.TimeCompiler.StackRename

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename CNFOutput Lax434930.PolynomialTime

inductive Key (I W : Type) where
  | input (i : I)
  | output
  | work (w : W)
  deriving DecidableEq, Fintype

def store {I W : Type} (a : I → Word) (tail : Word) (scratch : Option Bool) :
    BitStore (Key I W) Unit :=
  ⟨((), scratch), fun k => match k with
    | .input i => a i
    | .output => tail
    | .work _ => []⟩

/-- A finite stack program which preserves its arguments and appends its
output to a reverse buffer. Its workspace is empty after every call. -/
structure Emitter (I : Type) [DecidableEq I] (f : (I → Word) → Word) where
  Workspace : Type
  [finiteWorkspace : Fintype Workspace]
  [decidableWorkspace : DecidableEq Workspace]
  program : BitProgram (Key I Workspace) Unit
  bound : Polynomial ℕ
  length_bound : ∀ a b, (∀ i, (a i).length ≤ b) → (f a).length ≤ bound.eval b
  executes : ∀ a tail scratch b, (∀ i, (a i).length ≤ b) →
    ∃ t, t ≤ bound.eval b ∧ Executes program (store a tail scratch)
      (store a ((f a).reverse ++ tail) none) t

attribute [instance] Emitter.finiteWorkspace Emitter.decidableWorkspace

def Emitter.congr {I : Type} [DecidableEq I] {f g : (I → Word) → Word}
    (p : Emitter I f) (h : ∀ a, f a = g a) : Emitter I g where
  Workspace := p.Workspace
  program := p.program
  bound := p.bound
  length_bound a b hb := by rw [← h]; exact p.length_bound a b hb
  executes a tail scratch b hb := by simpa only [h] using p.executes a tail scratch b hb

lemma Emitter.run_in {I K : Type} [DecidableEq I] [DecidableEq K]
    {f : (I → Word) → Word} (p : Emitter I f)
    (embed : Key I p.Workspace → K) (hinj : Function.Injective embed)
    (s : BitStore K Unit) (a : I → Word) (b : ℕ)
    (ha : ∀ i, s.stk (embed (.input i)) = a i)
    (hw : ∀ w, s.stk (embed (.work w)) = []) (hb : ∀ i, (a i).length ≤ b) :
    ∃ t, t ≤ p.bound.eval b ∧ Executes (rename embed p.program) s
      (emitted (embed .output) (f a) s) t := by
  obtain ⟨t, ht, he⟩ := p.executes a (s.stk (embed .output)) s.state.2 b hb
  have hs : project embed s = store a (s.stk (embed .output)) s.state.2 := by
    apply Store.ext
    · exact Prod.ext (Subsingleton.elim _ _) rfl
    · funext k
      cases k with
      | input i => exact ha i
      | output => rfl
      | work w => exact hw w
  obtain ⟨u, hu, hproj, hframe⟩ := rename_executes embed hinj he s hs
  have hout : u = emitted (embed .output) (f a) s := by
    apply Store.ext
    · have hh := congrArg (fun q => q.state) hproj
      simpa [project, store, emitted] using hh
    · funext key
      by_cases hk : key ∈ Set.range embed
      · obtain ⟨k, rfl⟩ := hk
        have hh := congrArg (fun q => q.stk k) hproj
        cases k with
        | input i =>
          have hn : embed (.input i) ≠ embed .output := fun h => by cases hinj h
          simpa [project, store, emitted, hn, ha] using hh
        | output => simpa [project, store, emitted] using hh
        | work w =>
          have hn : embed (.work w) ≠ embed .output := fun h => by cases hinj h
          simpa [project, store, emitted, hn, hw] using hh
      · have hn : key ≠ embed .output := fun h => hk ⟨.output, h.symm⟩
        simpa [emitted, hn] using hframe key hk
  exact ⟨t, ht, hout ▸ hu⟩

lemma emitted_store {I W : Type} [DecidableEq I] [DecidableEq W]
    (a : I → Word) (tail w : Word) (scratch : Option Bool) :
    emitted (Key.output : Key I W) w (store a tail scratch) =
      store a (w.reverse ++ tail) none := by
  apply Store.ext
  · rfl
  · funext k
    cases k <;> simp [emitted, store]

def workMap {I W V : Type} (f : W → V) : Key I W → Key I V
  | .input i => .input i
  | .output => .output
  | .work w => .work (f w)

lemma workMap_injective {I W V : Type} (f : W → V) (hf : Function.Injective f) :
    Function.Injective (workMap (I := I) f) := by
  intro k l h
  cases k <;> cases l <;> simp_all [workMap, hf.eq_iff]

end Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
