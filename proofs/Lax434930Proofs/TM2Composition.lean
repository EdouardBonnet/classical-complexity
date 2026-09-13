import Lax434930Proofs.TM2Bounds
import Mathlib.Data.Fintype.Sum

set_option backward.isDefEq.respectTransparency false

/-! Sequential composition of two finite machines with a binary intermediate
word. Two transfers preserve the word's order and empty the temporary stack. -/

namespace Lax434930Proofs.TM2Composition

open Turing TM2Bounds

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (M N : FinTM2)

abbrev Key := M.K ⊕ (N.K ⊕ Unit)
abbrev Label := M.Λ ⊕ (Bool ⊕ N.Λ)
abbrev State := M.σ × (N.σ × Option Bool)

def Alphabet : Key M N → Type
  | .inl k => M.Γ k
  | .inr (.inl k) => N.Γ k
  | .inr (.inr _) => Bool

abbrev Cfg := TM2.Cfg (Alphabet M N) (Label M N) (State M N)
abbrev Stmt := TM2.Stmt (Alphabet M N) (Label M N) (State M N)

def joinedStacks (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Bool) : (k : Key M N) → List (Alphabet M N k)
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => tmp

theorem update_left (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Bool) (k : M.K) (xs : List (M.Γ k)) :
    Function.update (joinedStacks M N s t tmp) (.inl k) xs =
      joinedStacks M N (Function.update s k xs) t tmp := by
  funext j
  cases j with
  | inl j => by_cases hj : j = k <;> simp_all [joinedStacks] <;> rfl
  | inr j => cases j <;> simp [joinedStacks]

theorem update_right (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp : List Bool) (k : N.K) (xs : List (N.Γ k)) :
    Function.update (joinedStacks M N s t tmp) (.inr (.inl k)) xs =
      joinedStacks M N s (Function.update t k xs) tmp := by
  funext j
  cases j with
  | inl j => simp [joinedStacks]
  | inr j =>
      cases j with
      | inl j => by_cases hj : j = k <;> simp_all [joinedStacks] <;> rfl
      | inr j => simp [joinedStacks]

theorem update_tmp (s : (k : M.K) → List (M.Γ k)) (t : (k : N.K) → List (N.Γ k))
    (tmp xs : List Bool) :
    Function.update (joinedStacks M N s t tmp) (.inr (.inr ())) xs = joinedStacks M N s t xs := by
  funext j
  cases j with
  | inl j => simp [joinedStacks]
  | inr j => cases j <;> simp [joinedStacks]

def leftStmt : M.Stmt → Stmt M N
  | .push k f q => .push (.inl k) (fun v => f v.1) (leftStmt q)
  | .pop k f q => .pop (.inl k) (fun v b => (f v.1 b, v.2)) (leftStmt q)
  | .peek k f q => .peek (.inl k) (fun v b => (f v.1 b, v.2)) (leftStmt q)
  | .load f q => .load (fun v => (f v.1, v.2)) (leftStmt q)
  | .branch f p q => .branch (fun v => f v.1) (leftStmt p) (leftStmt q)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr (.inl false))

def rightStmt : N.Stmt → Stmt M N
  | .push k f q => .push (.inr (.inl k)) (fun v => f v.2.1) (rightStmt q)
  | .pop k f q => .pop (.inr (.inl k)) (fun v b => (v.1, f v.2.1 b, v.2.2)) (rightStmt q)
  | .peek k f q => .peek (.inr (.inl k)) (fun v b => (v.1, f v.2.1 b, v.2.2)) (rightStmt q)
  | .load f q => .load (fun v => (v.1, f v.2.1, v.2.2)) (rightStmt q)
  | .branch f p q => .branch (fun v => f v.2.1) (rightStmt p) (rightStmt q)
  | .goto f => .goto (fun v => .inr (.inr (f v.2.1)))
  | .halt => .halt

def leftCfg (c : M.Cfg) : Cfg M N where
  l := some (c.l.elim (.inr (.inl false)) Sum.inl)
  var := (c.var, N.initialState, none)
  stk := joinedStacks M N c.stk (fun _ => []) []

def rightCfg (c : N.Cfg) : Cfg M N where
  l := c.l.map (fun l => .inr (.inr l))
  var := (M.initialState, c.var, none)
  stk := joinedStacks M N (fun _ => []) c.stk []

theorem left_stepAux (q : M.Stmt) (v : M.σ) (s : (k : M.K) → List (M.Γ k)) :
    TM2.stepAux (leftStmt M N q) (v, N.initialState, none)
      (joinedStacks M N s (fun _ => []) []) = leftCfg M N (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa only [leftStmt, TM2.stepAux, update_left] using! ih v _
  | pop k f q ih =>
      simpa only [leftStmt, TM2.stepAux, joinedStacks, update_left] using! ih (f v (s k).head?) _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq => cases hf : f v <;> simp [leftStmt, TM2.stepAux, hf, ihp, ihq]
  | goto f => rfl
  | halt => rfl

theorem right_stepAux (q : N.Stmt) (v : N.σ) (s : (k : N.K) → List (N.Γ k)) :
    TM2.stepAux (rightStmt M N q) (M.initialState, v, none)
      (joinedStacks M N (fun _ => []) s []) = rightCfg M N (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa only [rightStmt, TM2.stepAux, update_right] using! ih v _
  | pop k f q ih =>
      simpa only [rightStmt, TM2.stepAux, joinedStacks, update_right] using! ih (f v (s k).head?) _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq => cases hf : f v <;> simp [rightStmt, TM2.stepAux, hf, ihp, ihq]
  | goto f => rfl
  | halt => rfl

variable (out : M.Γ M.k₁ ≃ Bool) (inp : N.Γ N.k₀ ≃ Bool)

def firstTransfer : Stmt M N :=
  .pop (.inl M.k₁) (fun v b => (v.1, v.2.1, b.map out))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inr ())) (fun v => v.2.2.getD false)
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => .inr (.inl false)))))
      (.goto (fun _ => .inr (.inl true))))

def secondTransfer : Stmt M N :=
  .pop (.inr (.inr ())) (fun v b => (v.1, v.2.1, b))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inl N.k₀)) (fun v => inp.symm (v.2.2.getD false))
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => .inr (.inl true)))))
      (.goto (fun _ => .inr (.inr N.main))))

def code : Label M N → Stmt M N
  | .inl l => leftStmt M N (M.m l)
  | .inr (.inl false) => firstTransfer M N out
  | .inr (.inl true) => secondTransfer M N inp
  | .inr (.inr l) => rightStmt M N (N.m l)

def machine : FinTM2 where
  K := Key M N
  k₀ := .inl M.k₀
  k₁ := .inr (.inl N.k₁)
  Γ := Alphabet M N
  Γk₀Fin := M.Γk₀Fin
  Λ := Label M N
  main := .inl M.main
  σ := State M N
  initialState := (M.initialState, N.initialState, none)
  m := code M N out inp

theorem left_step {c d : M.Cfg} (h : M.step c = some d) :
    (machine M N out inp).step (leftCfg M N c) = some (leftCfg M N d) := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (M.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact congrArg some (left_stepAux M N (M.m l) v s)

theorem right_step {c d : N.Cfg} (h : N.step c = some d) :
    (machine M N out inp).step (rightCfg M N c) = some (rightCfg M N d) := by
  cases c with
  | mk l v s =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have hd : TM2.stepAux (N.m l) v s = d := Option.some.inj h
          rw [← hd]
          exact congrArg some (right_stepAux M N (N.m l) v s)

end Lax434930Proofs.TM2Composition
