import Lax434930Proofs.HomogeneousStacks
import Lax434930Proofs.SavitchProofs.StackLanguage

/-! Execute finite TM2 instruction blocks in the work-space machine language. -/

namespace Lax434930Proofs.StackSpaceInterpreter

open Turing Lax434930.PolynomialTime
open SavitchProofs.StackLanguage

noncomputable section
open scoped Classical

variable {K Γ Λ σ : Type}

structure Control (Γ Λ σ : Type) where
  label : Option Λ
  var : σ
  value : Option Γ := none
  deriving Fintype

abbrev Data (K Γ Λ σ : Type) := SavitchProofs.StackLanguage.Data K Γ (Control Γ Λ σ)
abbrev Code (K Γ Λ σ : Type) := Command K Γ (Control Γ Λ σ)

def view (l : Option Λ) (v : σ) (S : K → List Γ) (inputHead : ℕ) : Data K Γ Λ σ :=
  ⟨⟨l, v, none⟩, inputHead, S⟩

def encode (c : TM2.Cfg (fun _ : K => Γ) Λ σ) (inputHead : ℕ) : Data K Γ Λ σ :=
  view c.l c.var c.stk inputHead

variable [Inhabited Γ]

def peek (k : K) (f : σ → Option Γ → σ) : Code K Γ Λ σ :=
  .seq (.pop (fun _ => k) (fun s g => {s with var := f s.var g, value := g}))
    (.seq (.branch (fun s => s.value.isSome)
      (.push (fun _ => k) (fun s => s.value.getD default)) .skip)
      (.assign (fun s => {s with value := none})))

def statement : TM2.Stmt (fun _ : K => Γ) Λ σ → Code K Γ Λ σ
  | .push k f q => .seq (.push (fun _ => k) (fun s => f s.var)) (statement q)
  | .pop k f q =>
      .seq (.pop (fun _ => k) (fun s g => {s with var := f s.var g})) (statement q)
  | .peek k f q => .seq (peek k f) (statement q)
  | .load f q => .seq (.assign (fun s => {s with var := f s.var})) (statement q)
  | .branch f q r => .branch (fun s => f s.var) (statement q) (statement r)
  | .goto f => .assign (fun s => {s with label := some (f s.var)})
  | .halt => .assign (fun s => {s with label := none})

lemma peek_execution (w : Word) (bound : ℕ) (k : K) (f : σ → Option Γ → σ)
    (l : Option Λ) (v : σ) (S : K → List Γ) (i : ℕ)
    (hd : Good w bound (view l v S i)) :
    Exec w bound (peek k f) (view l v S i) (view l (f v (S k).head?) S i) := by
  let dp := popped (view l v S i) k
    (fun s g => {s with var := f s.var g, value := g})
  have hp : Exec w bound (.pop (fun _ => k)
      (fun s g => {s with var := f s.var g, value := g})) (view l v S i) dp :=
    .pop _ _ _ hd
  cases hs : S k with
  | nil =>
    have ht := Exec.branch_false (test := fun s : Control Γ Λ σ => s.value.isSome)
      (yes := .push (fun _ => k) (fun s => s.value.getD default))
      (by simp [dp, popped, view, hs]) (Exec.skip dp hp.good.2)
    have ha := Exec.assign dp (fun s => {s with value := none}) hp.good.2
    have he : assigned dp {dp.state with value := none} = view l (f v (S k).head?) S i := by
      dsimp [assigned, dp, popped, view]
      congr 1
      funext j
      by_cases hj : j = k <;> simp_all [Function.update_apply]
    simpa only [peek, he, hs] using Exec.seq hp (Exec.seq ht ha)
  | cons g xs =>
    have he : pushed dp k (dp.state.value.getD default) =
        ⟨⟨l, f v (some g), some g⟩, i, S⟩ := by
      dsimp [pushed, dp, popped, view]
      simp only [hs, List.head?_cons, List.tail_cons, Option.getD_some]
      congr 1
      funext j
      by_cases hj : j = k <;> simp_all [Function.update_apply]
    have hg : Good w bound (pushed dp k (dp.state.value.getD default)) := by
      rw [he]
      exact hd
    have ht := Exec.branch_true (test := fun s : Control Γ Λ σ => s.value.isSome)
      (no := .skip) (by simp [dp, popped, view, hs])
      (Exec.push dp (fun _ => k) (fun s => s.value.getD default) hp.good.2 hg)
    have ha := Exec.assign _ (fun s : Control Γ Λ σ => {s with value := none}) hg
    simpa only [peek, he, assigned, hs, List.head?_cons, view] using Exec.seq hp (Exec.seq ht ha)

lemma statement_execution (q : TM2.Stmt (fun _ : K => Γ) Λ σ)
    (w : Word) (bound : ℕ) (l : Option Λ) (v : σ) (S : K → List Γ) (i : ℕ)
    (hi : i ≤ w.length + 1) (hb : ∀ k, (S k).length + TM2Bounds.pushes q < bound) :
    Exec w bound (statement q) (view l v S i) (encode (TM2.stepAux q v S) i) := by
  have hd : Good w bound (view l v S i) :=
    ⟨hi, fun k => lt_of_le_of_lt (Nat.le_add_right _ _) (hb k)⟩
  induction q generalizing l v S with
  | push k f q ih =>
    let S' := Function.update S k (f v :: S k)
    have hb' : ∀ j, (S' j).length + TM2Bounds.pushes q < bound := by
      intro j
      have hh := hb j
      by_cases hj : j = k <;> simp [S', Function.update_apply, hj, TM2Bounds.pushes] at * <;> omega
    have hp := Exec.push (view l v S i) (fun _ => k) (fun s => f s.var) hd
      (show Good w bound (view l v S' i) from
        ⟨hi, fun j => lt_of_le_of_lt (Nat.le_add_right _ _) (hb' j)⟩)
    exact Exec.seq hp (ih l v S' hb' hp.good.2)
  | pop k f q ih =>
    let S' := Function.update S k (S k).tail
    have hb' : ∀ j, (S' j).length + TM2Bounds.pushes q < bound := by
      intro j
      have hh := hb j
      by_cases hj : j = k <;> simp [S', Function.update_apply, hj, TM2Bounds.pushes] at * <;> omega
    have hp := Exec.pop (view l v S i) (fun _ => k) (fun s g => {s with var := f s.var g}) hd
    exact Exec.seq hp (ih l (f v (S k).head?) S' hb' hp.good.2)
  | peek k f q ih =>
    exact Exec.seq (peek_execution w bound k f l v S i hd) (ih l (f v (S k).head?) S hb hd)
  | load f q ih =>
    exact Exec.seq (Exec.assign (view l v S i) (fun s => {s with var := f s.var}) hd) (ih l (f v) S hb hd)
  | branch f q r ihq ihr =>
    cases hf : f v
    · have hr : ∀ k, (S k).length + TM2Bounds.pushes r < bound :=
        fun k => (Nat.add_le_add_left (Nat.le_max_right _ _) _).trans_lt (hb k)
      simpa only [statement, TM2.stepAux, hf, Bool.cond_false] using
        Exec.branch_false (test := fun s : Control Γ Λ σ => f s.var)
          (yes := statement q) hf (ihr l v S hr hd)
    · have hq : ∀ k, (S k).length + TM2Bounds.pushes q < bound :=
        fun k => (Nat.add_le_add_left (Nat.le_max_left _ _) _).trans_lt (hb k)
      simpa only [statement, TM2.stepAux, hf, Bool.cond_true] using
        Exec.branch_true (test := fun s : Control Γ Λ σ => f s.var)
          (no := statement r) hf (ihq l v S hq hd)
  | goto f => exact Exec.assign (view l v S i) (fun s => {s with label := some (f s.var)}) hd
  | halt => exact Exec.assign (view l v S i) (fun s => {s with label := none}) hd

def select (M : Λ → TM2.Stmt (fun _ : K => Γ) Λ σ) : List Λ → Code K Γ Λ σ
  | [] => .skip
  | l :: labels => .branch (fun s => decide (s.label = some l))
      (statement (M l)) (select M labels)

lemma select_execution (M : Λ → TM2.Stmt (fun _ : K => Γ) Λ σ)
    (labels : List Λ) (l : Λ) (hl : l ∈ labels)
    (w : Word) (bound : ℕ) (v : σ) (S : K → List Γ) (i : ℕ)
    (hi : i ≤ w.length + 1) (hb : ∀ k, (S k).length + TM2Bounds.pushes (M l) < bound) :
    Exec w bound (select M labels) (view (some l) v S i)
      (encode (TM2.stepAux (M l) v S) i) := by
  induction labels with
  | nil => simp at hl
  | cons j labels ih =>
    by_cases hj : l = j
    · subst j
      exact Exec.branch_true (by simp [view])
        (statement_execution (M l) w bound (some l) v S i hi hb)
    · have hm : l ∈ labels := by simpa [hj] using hl
      exact Exec.branch_false (by simp [view, hj]) (ih hm)

def program (M : Λ → TM2.Stmt (fun _ : K => Γ) Λ σ) (labels : List Λ) : Code K Γ Λ σ :=
  .loop (fun s => s.label.isSome) (select M labels)

lemma run_execution (M : Λ → TM2.Stmt (fun _ : K => Γ) Λ σ)
    (labels : List Λ) (hlabels : ∀ l, l ∈ labels) (C : ℕ)
    (hC : ∀ l, TM2Bounds.pushes (M l) ≤ C) (w : Word) (bound i : ℕ)
    (hi : i ≤ w.length + 1) {n : ℕ} {c d : TM2.Cfg (fun _ : K => Γ) Λ σ}
    (h : Time.Run (TM2.step M) n c d) (ht : d.l = none)
    (hb : ∀ k, (c.stk k).length + C * n < bound) :
    Exec w bound (program M labels) (encode c i) (encode d i) := by
  induction h with
  | zero c =>
    exact Exec.loop_false _ _ _ ⟨hi, fun k => by simpa [encode, view] using hb k⟩
      (by simp [encode, view, ht])
  | @cons n c e d hs hr ih =>
    cases c with
    | mk label v S =>
      cases label with
      | none => simp [TM2.step] at hs
      | some l =>
        have he : TM2.stepAux (M l) v S = e := Option.some.inj hs
        have hsize : ∀ k, (S k).length + TM2Bounds.pushes (M l) < bound := by
          intro k
          have hh := hb k
          have hc := hC l
          simp only [Nat.mul_succ] at hh
          change (S k).length + (C * n + C) < bound at hh
          omega
        have hbody := select_execution M labels l (hlabels l) w bound v S i hi hsize
        have hb' : ∀ k, (e.stk k).length + C * n < bound := by
          intro k
          have hh := hb k
          have hs := TM2Bounds.stepAux_length (M l) v S k
          rw [he] at hs
          have hc := hC l
          simp only [Nat.mul_succ] at hh
          change (S k).length + (C * n + C) < bound at hh
          omega
        rw [he] at hbody
        exact Exec.loop_true rfl hbody (ih ht hb')

end

end Lax434930Proofs.StackSpaceInterpreter
