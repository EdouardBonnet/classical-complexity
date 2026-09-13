import Lax434930Proofs.TM2Composition

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.TM2Composition

open Turing TM2Bounds

variable (M N : FinTM2) (out : M.Γ M.k₁ ≃ Bool) (inp : N.Γ N.k₀ ≃ Bool)

def single {K : Type} [DecidableEq K] (Γ : K → Type) (port : K) (xs : List (Γ port)) :
    (k : K) → List (Γ k) := Function.update (fun _ => []) port xs

@[simp] theorem single_same {K : Type} [DecidableEq K] (Γ : K → Type) (port : K)
    (xs : List (Γ port)) : single Γ port xs port = xs := by simp [single]

@[simp] theorem single_nil {K : Type} [DecidableEq K] (Γ : K → Type) (port : K) :
    single Γ port [] = (fun _ => []) := by simp [single]

@[simp] theorem update_single {K : Type} [DecidableEq K] (Γ : K → Type) (port : K)
    (xs ys : List (Γ port)) : Function.update (single Γ port xs) port ys = single Γ port ys := by
  simp [single]

def firstCfg (xs : List (M.Γ M.k₁)) (tmp : List Bool) : Cfg M N where
  l := some (.inr (.inl false))
  var := (M.initialState, N.initialState, none)
  stk := joinedStacks M N (single M.Γ M.k₁ xs) (fun _ => []) tmp

def secondCfg (tmp : List Bool) (ys : List (N.Γ N.k₀)) : Cfg M N where
  l := some (.inr (.inl true))
  var := (M.initialState, N.initialState, none)
  stk := joinedStacks M N (fun _ => []) (single N.Γ N.k₀ ys) tmp

theorem first_cons (x : M.Γ M.k₁) (xs : List (M.Γ M.k₁)) (tmp : List Bool) :
    (machine M N out inp).step (firstCfg M N (x :: xs) tmp) =
      some (firstCfg M N xs (out x :: tmp)) := by
  simp [FinTM2.step, machine, code, firstTransfer, firstCfg, TM2.step, TM2.stepAux,
    update_left, update_tmp, joinedStacks, single, List.head?, List.tail]

theorem first_nil (tmp : List Bool) :
    (machine M N out inp).step (firstCfg M N [] tmp) = some (secondCfg M N tmp []) := by
  simp [FinTM2.step, machine, code, firstTransfer, firstCfg, secondCfg, TM2.step, TM2.stepAux,
    update_left, joinedStacks, single, List.head?, List.tail]

theorem second_cons (b : Bool) (tmp : List Bool) (ys : List (N.Γ N.k₀)) :
    (machine M N out inp).step (secondCfg M N (b :: tmp) ys) =
      some (secondCfg M N tmp (inp.symm b :: ys)) := by
  simp [FinTM2.step, machine, code, secondTransfer, secondCfg, TM2.step, TM2.stepAux,
    update_right, update_tmp, joinedStacks, single, List.head?, List.tail]

theorem second_nil (ys : List (N.Γ N.k₀)) :
    (machine M N out inp).step (secondCfg M N [] ys) = some (rightCfg M N (initList N ys)) := by
  simp [FinTM2.step, machine, code, secondTransfer, secondCfg, rightCfg,
    TM2.step, TM2.stepAux, update_tmp, joinedStacks, single, initList, Function.update,
    List.head?, List.tail]
  congr 2
  funext k
  by_cases hk : k = N.k₀
  · subst k; simp
  · simp [hk]

theorem first_run (xs : List (M.Γ M.k₁)) (tmp : List Bool) :
    (fun c : Option (Cfg M N) => c.bind (machine M N out inp).step)^[xs.length + 1]
      (some (firstCfg M N xs tmp)) =
      some (secondCfg M N ((xs.map out).reverse ++ tmp) []) := by
  induction xs generalizing tmp with
  | nil => simpa using first_nil M N out inp tmp
  | cons x xs ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, Option.bind_some,
        first_cons, ih]
      simp

theorem second_run (tmp : List Bool) (ys : List (N.Γ N.k₀)) :
    (fun c : Option (Cfg M N) => c.bind (machine M N out inp).step)^[tmp.length + 1]
      (some (secondCfg M N tmp ys)) =
      some (rightCfg M N (initList N (tmp.reverse.map inp.symm ++ ys))) := by
  induction tmp generalizing ys with
  | nil => simpa using second_nil M N out inp ys
  | cons b tmp ih =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, Option.bind_some,
        second_cons, ih]
      simp

theorem left_halt (xs : List (M.Γ M.k₁)) : leftCfg M N (haltList M xs) = firstCfg M N xs [] := by
  simp [leftCfg, haltList, firstCfg, single, Function.update]
  congr 1
  funext k
  by_cases hk : k = M.k₁
  · subst k; simp
  · simp [hk]

/-- Exactly two linear transfers, including their end-of-stack tests. -/
theorem transfer_run (xs : List (M.Γ M.k₁)) :
    (fun c : Option (Cfg M N) => c.bind (machine M N out inp).step)^[2 * xs.length + 2]
      (some (leftCfg M N (haltList M xs))) =
      some (rightCfg M N (initList N ((xs.map out).map inp.symm))) := by
  have h₁ := first_run M N out inp xs []
  have h₂ := second_run M N out inp (xs.map out).reverse []
  simp only [List.append_nil] at h₁
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil] at h₂
  have h := append_run (machine M N out inp).step h₁ h₂
  rw [left_halt]
  simpa only [show xs.length + 1 + (xs.length + 1) = 2 * xs.length + 2 by omega] using! h

theorem initial_eq (xs : List (M.Γ M.k₀)) :
    initList (machine M N out inp) xs = leftCfg M N (initList M xs) := by
  apply cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = M.k₀
      · subst k; simp [initList, machine, leftCfg, joinedStacks]
      · simp [initList, machine, leftCfg, joinedStacks, hk]
  | inr k => cases k <;> simp [initList, machine, leftCfg, joinedStacks]

theorem terminal_eq (ys : List (N.Γ N.k₁)) :
    rightCfg M N (haltList N ys) = haltList (machine M N out inp) ys := by
  apply cfg_ext
  · rfl
  · rfl
  funext k
  cases k with
  | inl k => simp [haltList, machine, rightCfg, joinedStacks]
  | inr k =>
      cases k with
      | inl k =>
          by_cases hk : k = N.k₁
          · subst k; simp [haltList, machine, rightCfg, joinedStacks]
          · simp [haltList, machine, rightCfg, joinedStacks, hk]
      | inr k => simp [haltList, machine, rightCfg, joinedStacks]

end Lax434930Proofs.TM2Composition
