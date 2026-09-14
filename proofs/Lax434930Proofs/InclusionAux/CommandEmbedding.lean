import Lax434930Proofs.SavitchProofs.StackLanguage

namespace Lax434930Proofs.CommandEmbedding

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open SavitchProofs.StackLanguage
open scoped Classical

noncomputable section

structure KeyMap (K J : Type) where
  key : K → J
  read : J → Option K
  read_key : ∀ k, read (key k) = some k
  key_read : ∀ j k, read j = some k → key k = j

variable {K J Γ Δ σ τ : Type}

def store (e : KeyMap K J) (symbol : Γ → Δ) (S : K → List Γ) (frame : J → List Δ) : J → List Δ :=
  fun j => match e.read j with
    | some k => (S k).map symbol
    | none => frame j

@[simp] lemma store_key (e : KeyMap K J) (symbol : Γ → Δ) (S : K → List Γ)
    (frame : J → List Δ) (k : K) : store e symbol S frame (e.key k) = (S k).map symbol := by
  simp [store, e.read_key]

lemma store_update (e : KeyMap K J) (symbol : Γ → Δ) (S : K → List Γ)
    (frame : J → List Δ) (k : K) (xs : List Γ) :
    store e symbol (Function.update S k xs) frame =
      Function.update (store e symbol S frame) (e.key k) (xs.map symbol) := by
  funext j
  by_cases hj : j = e.key k
  · subst j; simp
  · cases hr : e.read j with
    | none => simp [store, hr, Function.update_of_ne hj]
    | some a =>
      have ha : a ≠ k := by
        intro h
        subst a
        exact hj (e.key_read j k hr).symm
      simp [store, hr, Function.update_of_ne hj, Function.update_of_ne ha]

def data (e : KeyMap K J) (symbol : Γ → Δ) (state : σ → τ)
    (frame : J → List Δ) (d : Data K Γ σ) : Data J Δ τ :=
  ⟨state d.state, d.inputHead, store e symbol d.store frame⟩

lemma good (e : KeyMap K J) (symbol : Γ → Δ) (state : σ → τ)
    (frame : J → List Δ) (w : Word) (bound : ℕ) (d : Data K Γ σ)
    (hd : Good w bound d) (hf : ∀ j, e.read j = none → (frame j).length < bound) :
    Good w bound (data e symbol state frame d) := by
  refine ⟨hd.1, ?_⟩
  intro j
  cases hr : e.read j with
  | none => simpa [data, store, hr] using hf j hr
  | some k => simpa [data, store, hr] using hd.2 k

def command (e : KeyMap K J) (symbol : Γ → Δ) (readSymbol : Δ → Γ)
    (state : σ → τ) (readState : τ → σ) : Command K Γ σ → Command J Δ τ
  | .skip => .skip
  | .assign f => .assign (fun s => state (f (readState s)))
  | .input f => .input (fun s i => state (f (readState s) i))
  | .move f => .move (fun s => f (readState s))
  | .push k g => .push (fun s => e.key (k (readState s))) (fun s => symbol (g (readState s)))
  | .pop k f => .pop (fun s => e.key (k (readState s)))
      (fun s g => state (f (readState s) (g.map readSymbol)))
  | .seq a b => .seq (command e symbol readSymbol state readState a)
      (command e symbol readSymbol state readState b)
  | .branch test a b => .branch (fun s => test (readState s))
      (command e symbol readSymbol state readState a)
      (command e symbol readSymbol state readState b)
  | .loop test a => .loop (fun s => test (readState s))
      (command e symbol readSymbol state readState a)

lemma data_assigned (e : KeyMap K J) (symbol : Γ → Δ) (state : σ → τ)
    (frame : J → List Δ) (d : Data K Γ σ) (s : σ) :
    data e symbol state frame (assigned d s) = assigned (data e symbol state frame d) (state s) := rfl

lemma data_moved (e : KeyMap K J) (symbol : Γ → Δ) (state : σ → τ)
    (frame : J → List Δ) (w : Word) (d : Data K Γ σ) (direction : Move) :
    data e symbol state frame (moved w d direction) = moved w (data e symbol state frame d) direction := rfl

lemma data_pushed (e : KeyMap K J) (symbol : Γ → Δ) (state : σ → τ)
    (frame : J → List Δ) (d : Data K Γ σ) (k : K) (g : Γ) :
    data e symbol state frame (pushed d k g) =
      pushed (data e symbol state frame d) (e.key k) (symbol g) := by
  simp only [data, pushed, store_update, List.map_cons, store_key]

lemma data_popped (e : KeyMap K J) (symbol : Γ → Δ) (readSymbol : Δ → Γ)
    (state : σ → τ) (readState : τ → σ)
    (hSymbol : ∀ g, readSymbol (symbol g) = g) (hState : ∀ s, readState (state s) = s)
    (frame : J → List Δ) (d : Data K Γ σ) (k : K) (f : σ → Option Γ → σ) :
    data e symbol state frame (popped d k f) =
      popped (data e symbol state frame d) (e.key k)
        (fun s g => state (f (readState s) (g.map readSymbol))) := by
  have hh : ((d.store k).map symbol).head?.map readSymbol = (d.store k).head? := by
    cases d.store k <;> simp [hSymbol]
  simp only [data, popped, store_update, store_key, hState, hh, List.map_tail]

lemma execution (e : KeyMap K J) (symbol : Γ → Δ) (readSymbol : Δ → Γ)
    (state : σ → τ) (readState : τ → σ)
    (hSymbol : ∀ g, readSymbol (symbol g) = g) (hState : ∀ s, readState (state s) = s)
    (frame : J → List Δ) (w : Word) (bound : ℕ)
    (hf : ∀ j, e.read j = none → (frame j).length < bound)
    {c : Command K Γ σ} {d f : Data K Γ σ} (h : Exec w bound c d f) :
    Exec w bound (command e symbol readSymbol state readState c)
      (data e symbol state frame d) (data e symbol state frame f) := by
  induction h with
  | skip d hd => exact .skip _ (good e symbol state frame w bound d hd hf)
  | assign d f hd =>
    simpa only [command, data_assigned, data, assigned, hState] using
      Exec.assign (data e symbol state frame d) (fun s => state (f (readState s)))
        (good e symbol state frame w bound d hd hf)
  | input d f hd =>
    simpa only [command, data_assigned, data, assigned, hState] using
      Exec.input (data e symbol state frame d) (fun s i => state (f (readState s) i))
        (good e symbol state frame w bound d hd hf)
  | move d f hd =>
    simpa only [command, data_moved, data, moved, hState] using
      Exec.move (data e symbol state frame d) (fun s => f (readState s))
        (good e symbol state frame w bound d hd hf)
  | push d k g hd he =>
    have hp := good e symbol state frame w bound (pushed d (k d.state) (g d.state)) he hf
    rw [data_pushed] at hp
    simpa only [command, data_pushed, data, pushed, store_update, List.map_cons, store_key, hState] using
      Exec.push (data e symbol state frame d) (fun s => e.key (k (readState s)))
        (fun s => symbol (g (readState s))) (good e symbol state frame w bound d hd hf)
        (by simpa only [data, hState] using hp)
  | pop d k f hd =>
    rw [data_popped e symbol readSymbol state readState hSymbol hState]
    simpa only [command, data, hState] using
      Exec.pop (data e symbol state frame d) (fun s => e.key (k (readState s)))
        (fun s g => state (f (readState s) (g.map readSymbol)))
        (good e symbol state frame w bound d hd hf)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_true ht _ ih => exact .branch_true (by simpa [data, hState] using ht) ih
  | branch_false ht _ ih => exact .branch_false (by simpa [data, hState] using ht) ih
  | loop_false test body d hd ht =>
    exact .loop_false _ _ _ (good e symbol state frame w bound d hd hf)
      (by simpa [data, hState] using ht)
  | loop_true ht _ _ ih₁ ih₂ => exact .loop_true (by simpa [data, hState] using ht) ih₁ ih₂

end

end Lax434930Proofs.CommandEmbedding
