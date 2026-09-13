import Lax434930Proofs.SavitchProofs.StackMacros

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackTransducer

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Command Exec Good assigned popped pushed)
open StackRoutines (Control Code Data)
open StackMacros
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def run {Ω : Type} (δ : σ → Γ → σ × Option Ω) : σ → List Γ → σ × List Ω
  | s, [] => (s, [])
  | s, g :: xs =>
      let (t, output) := δ s g
      let (u, rest) := run δ t xs
      (u, output.toList ++ rest)

lemma output_length {Ω : Type} (δ : σ → Γ → σ × Option Ω) (s : σ) (xs : List Γ) :
    (run δ s xs).2.length ≤ xs.length := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons g xs ih =>
    cases he : δ s g with
    | mk t output =>
      have hh := ih t
      cases output <;> simp [run, he] <;> omega

lemma run_append {Ω : Type} (δ : σ → Γ → σ × Option Ω) (s : σ) (xs ys : List Γ) :
    run δ s (xs ++ ys) =
      ((run δ (run δ s xs).1 ys).1, (run δ s xs).2 ++ (run δ (run δ s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons g xs ih =>
    cases hδ : δ s g
    simp [run, hδ, ih, List.append_assoc]

lemma run_map {Ω σ' Γ' Ω' : Type} (δ : σ → Γ → σ × Option Ω)
    (δ' : σ' → Γ' → σ' × Option Ω') (state : σ → σ') (input : Γ → Γ') (output : Ω → Ω')
    (h : ∀ s g, δ' (state s) (input g) = (state (δ s g).1, (δ s g).2.map output))
    (s : σ) (xs : List Γ) :
    run δ' (state s) (xs.map input) = (state (run δ s xs).1, (run δ s xs).2.map output) := by
  induction xs generalizing s with
  | nil => rfl
  | cons g xs ih =>
    cases hδ : δ s g with
    | mk t emitted =>
      have hh := h s g
      simp only [hδ] at hh
      cases emitted <;> simp [run, hδ, hh, ih, List.map_append]

variable [Inhabited Γ]

def body (dst : K) (δ : σ → Γ → σ × Option Γ) : Macro K Γ σ :=
  Macro.seq (Macro.assign fun s =>
    let (t, output) := δ s.user (s.value.getD default)
    {s with user := t, other := output})
    (Macro.branch (fun s => s.other.isSome) (Macro.push dst (fun s => s.other.getD default)) Macro.skip)

def code (src dst : K) (δ : σ → Γ → σ × Option Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (StackRoutines.read src) (.seq
    (.loop (fun s => s.value.isSome) (.seq (body dst δ).code (StackRoutines.read src)))
    (.assign (fun s => {s with other := none})))

def result (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) (δ : σ → Γ → σ × Option Γ) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with user := (run δ d.state.user (d.store src)).1, value := none, other := none},
    d.inputHead, Function.update (Function.update d.store src []) dst
      ((run δ d.state.user (d.store src)).2.reverse ++ d.store dst)⟩

lemma code_exec (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst)
    (δ : σ → Γ → σ × Option Γ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hd : Good w bound d) (hb : (d.store src).length + (d.store dst).length < bound) :
    Exec w bound (code src dst δ) d (result d src dst δ) := by
  generalize hx : d.store src = xs at *
  induction xs generalizing d with
  | nil =>
    have hr := Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    have hl := Exec.loop_false (fun s : Control Γ σ => s.value.isSome)
      (.seq (body dst δ).code (StackRoutines.read src)) _ hr.good.2
      (by simp [popped, hx])
    have hp := Exec.assign _ (fun s => {s with other := none}) hl.good.2
    have he : assigned (popped d src (fun s value => {s with value := value}))
        { (popped d src (fun s value => {s with value := value})).state with other := none } = result d src dst δ := by
      simp only [result, run, assigned, popped, hx, List.head?_nil, List.tail_nil]
      congr 1
      funext k
      by_cases hs : k = src <;> by_cases ht : k = dst <;> simp_all [Function.update_apply]
    exact he ▸ Exec.seq hr (Exec.seq hl hp)
  | cons g xs ih =>
    let dr := popped d src (fun s value => {s with value := value})
    have hr : Exec w bound (StackRoutines.read src) d dr := .pop d _ _ hd
    cases hδ : δ d.state.user g with
    | mk t output =>
      let dp := (body dst δ).result w dr
      have hguard : (body dst δ).guard w bound dr := by
        cases output <;>
          simp [body, Macro.seq, Macro.assign, Macro.branch, Macro.push, Macro.skip, assigned,
            dr, popped, hx, hδ, Ne.symm hne]
        have hh := hb
        simp only [List.length_cons] at hh
        omega
      have hp : Exec w bound (body dst δ).code dr dp := (body dst δ).correct w bound dr hr.good.2 hguard
      have hpSrc : dp.store src = xs := by
        cases output <;>
          simp [dp, body, Macro.seq, Macro.assign, Macro.branch, Macro.push, Macro.skip,
            assigned, pushed, dr, popped, hx, hδ, hne]
      have hpBudget : (dp.store src).length + (dp.store dst).length < bound := by
        rw [hpSrc]
        cases output <;>
          simp [dp, body, Macro.seq, Macro.assign, Macro.branch, Macro.push, Macro.skip,
            assigned, pushed, dr, popped, hx, hδ, Ne.symm hne] <;>
          simp only [List.length_cons] at hb <;> omega
      have ht := ih dp hp.good.2 hpSrc (by simpa [hpSrc] using hpBudget)
      cases ht with
      | @seq _ _ _ dm _ hread hrest =>
        cases hrest with
        | @seq _ _ _ dn _ hloop hpost =>
          have hl : Exec w bound
              (.loop (fun s : Control Γ σ => s.value.isSome)
                (.seq (body dst δ).code (StackRoutines.read src))) dr dn :=
            .loop_true (by simp [dr, popped, hx]) (.seq hp hread) hloop
          have he : result dp src dst δ = result d src dst δ := by
            cases output <;>
              simp only [result, dp, body, Macro.seq, Macro.assign, Macro.branch, Macro.push, Macro.skip,
                assigned, pushed, dr, popped, hx, hδ, List.head?_cons, List.tail_cons,
                Option.getD_some, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
                ↓reduceIte]
            all_goals
              congr 1
              · simp [Function.update_apply, hne, run, hδ]
              · funext k
                by_cases hs : k = src <;> by_cases ht : k = dst <;>
                  simp_all [Function.update_apply, run, List.reverse_append, List.append_assoc]
          exact he ▸ Exec.seq hr (Exec.seq hl hpost)

def asMacro (src dst : K) (δ : σ → Γ → σ × Option Γ) : Macro K Γ σ where
  code := code src dst δ
  result _ d := result d src dst δ
  guard _ b d := src ≠ dst ∧ (d.store src).length + (d.store dst).length < b
  correct w b d hd h := code_exec w b src dst h.1 δ d hd h.2

end

end Lax434930Proofs.SavitchProofs.StackTransducer
