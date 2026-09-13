import Lax434930Proofs.TM2Bounds
import Lax434930Proofs.Time

/-! Encode the dependent stack alphabets in one finite alphabet. -/

namespace Lax434930Proofs.HomogeneousStacks

open Turing Function

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

abbrev Alphabet (Γ : K → Type) := Option (Sigma Γ)

def symbol (k : K) (g : Γ k) : Alphabet Γ := some ⟨k, g⟩

def readSymbol (k : K) : Alphabet Γ → Option (Γ k)
  | none => none
  | some ⟨j, g⟩ => if h : j = k then some (h ▸ g) else none

@[simp] lemma read_symbol (k : K) (g : Γ k) : readSymbol k (symbol k g) = some g := by
  simp [readSymbol, symbol]

def encodedStore (S : ∀ k, List (Γ k)) : K → List (Alphabet Γ) :=
  fun k => (S k).map (symbol k)

def cfg (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K => Alphabet Γ) Λ σ :=
  ⟨c.l, c.var, encodedStore c.stk⟩

lemma stacks_update (S : ∀ k, List (Γ k)) (k : K) (xs : List (Γ k)) :
    encodedStore (update S k xs) = update (encodedStore S) k (xs.map (symbol k)) := by
  funext j
  by_cases h : j = k
  · subst j; simp [encodedStore]
  · simp [encodedStore, update_of_ne h]

@[simp] lemma read_head (k : K) (xs : List (Γ k)) :
    ((xs.map (symbol k)).head?).bind (readSymbol k) = xs.head? := by
  cases xs <;> simp

def statement : TM2.Stmt Γ Λ σ → TM2.Stmt (fun _ : K => Alphabet Γ) Λ σ
  | .push k f q => .push k (fun v => symbol k (f v)) (statement q)
  | .pop k f q => .pop k (fun v g => f v (g.bind (readSymbol k))) (statement q)
  | .peek k f q => .peek k (fun v g => f v (g.bind (readSymbol k))) (statement q)
  | .load f q => .load f (statement q)
  | .branch f q r => .branch f (statement q) (statement r)
  | .goto f => .goto f
  | .halt => .halt

lemma statement_correct (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (statement q) v (encodedStore S) = cfg (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simpa only [statement, TM2.stepAux, stacks_update, List.map_cons, encodedStore] using
      ih v (update S k (f v :: S k))
  | pop k f q ih =>
    simpa only [statement, TM2.stepAux, encodedStore, read_head, stacks_update, List.map_tail] using
      ih (f v (S k).head?) (update S k (S k).tail)
  | peek k f q ih =>
    simpa only [statement, TM2.stepAux, encodedStore, read_head] using ih (f v (S k).head?) S
  | load f q ih => exact ih (f v) S
  | branch f q r ihq ihr =>
    cases h : f v
    · simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihr v S
    · simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihq v S
  | goto f | halt => rfl

lemma step_correct (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) :
    TM2.step (fun l => statement (M l)) (cfg c) = (TM2.step M c).map cfg := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l => exact congrArg some (statement_correct (M l) v S)

lemma run_correct (M : Λ → TM2.Stmt Γ Λ σ) {n : ℕ} {c d : TM2.Cfg Γ Λ σ}
    (h : Time.Run (TM2.step M) n c d) :
    Time.Run (TM2.step (fun l => statement (M l))) n (cfg c) (cfg d) := by
  exact h.map cfg (fun c d hs => by rw [step_correct, hs]; rfl)

@[simp] lemma pushes_statement (q : TM2.Stmt Γ Λ σ) :
    TM2Bounds.pushes (statement q) = TM2Bounds.pushes q := by
  induction q <;> simp_all [statement, TM2Bounds.pushes]

end Lax434930Proofs.HomogeneousStacks
