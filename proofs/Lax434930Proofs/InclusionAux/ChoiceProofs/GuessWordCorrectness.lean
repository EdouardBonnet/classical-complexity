import Lax434930Proofs.InclusionAux.ChoiceProofs.GuessWord

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.ChoiceProofs.GuessWord

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ChoiceLanguage
open scoped Classical

noncomputable section

variable {K Γ σ : Type}

def result (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) (bit : Bool → Γ)
    (xs : List Bool) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none, flag := xs.foldl (fun _ b => b) d.state.flag}, d.inputHead,
    Function.update (Function.update d.store src []) dst (xs.reverse.map bit ++ d.store dst)⟩

lemma result_nil (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) (hne : src ≠ dst)
    (bit : Bool → Γ) (hs : d.store src = []) :
    StackLanguage.popped d src (fun s value => {s with value := value}) = result d src dst bit [] := by
  simp only [result, StackLanguage.popped, hs, List.head?_nil, List.tail_nil, List.foldl_nil,
    List.reverse_nil, List.map_nil, List.nil_append]
  congr 1
  funext k
  by_cases hk : k = src <;> by_cases hl : k = dst <;>
    simp_all [Function.update_apply, Ne.symm hne]

lemma result_step (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) (hne : src ≠ dst)
    (bit : Bool → Γ) (b : Bool) (xs : List Bool) :
    result (pushed (StackLanguage.popped d src (fun s value => {s with value := value})) dst bit b)
      src dst bit xs = result d src dst bit (b :: xs) := by
  simp only [result, pushed, chosen, StackLanguage.popped, StackLanguage.pushed,
    StackLanguage.assigned, List.foldl_cons, List.reverse_cons, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
  congr 1
  funext k
  by_cases hk : k = src <;> by_cases hl : k = dst <;>
    simp_all [Function.update_apply, Ne.symm hne]

lemma execution (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst) (bit : Bool → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store src).length + (d.store dst).length < bound)
    (xs : List Bool) (hlen : xs.length = (d.store src).length) :
    Exec w bound (code src dst bit) d (result d src dst bit xs) := by
  induction xs generalizing d with
  | nil =>
    have hs : d.store src = [] := by simpa using hlen.symm
    have hr := StackLanguage.Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    have hl := Exec.loop_false (fun s : StackRoutines.Control Γ σ => s.value.isSome)
      (body src dst bit) _ hr.good.2 (by simp [StackLanguage.popped, hs])
    exact result_nil d src dst hne bit hs ▸ Exec.seq (.det hr) hl
  | cons b xs ih =>
    cases hs : d.store src with
    | nil => simp [hs] at hlen
    | cons g gs =>
      let dr := StackLanguage.popped d src (fun s value => {s with value := value})
      let dp := pushed dr dst bit b
      have hr : StackLanguage.Exec w bound (StackRoutines.read src) d dr := .pop d _ _ hd
      have hdr : Good w bound dr := hr.good.2
      have hdst : dr.store dst = d.store dst := by simp [dr, StackLanguage.popped, Ne.symm hne]
      have hpbound : (dr.store dst).length + 1 < bound := by
        rw [hdst]
        simp only [hs, List.length_cons] at hb
        omega
      have hdp : Good w bound dp := StackRoutines.good_pushed (d := chosen dr b) hdr dst (bit b) hpbound
      have hps : dp.store src = gs := by
        simp [dp, pushed, chosen, dr, StackLanguage.pushed, StackLanguage.popped, StackLanguage.assigned, hne, hs]
      have hpd : dp.store dst = bit b :: d.store dst := by
        simp [dp, pushed, chosen, StackLanguage.pushed, StackLanguage.assigned, hdst]
      have hrest := ih dp hdp (by rw [hps, hpd]; simp only [hs, List.length_cons] at hb ⊢; omega)
        (by rw [hps]; simpa [hs] using hlen)
      cases hrest with
      | seq hread hloop =>
        have hp : StackLanguage.Exec w bound (write dst bit) (chosen dr b) dp :=
          .push _ _ _ hdr hdp
        have hbody : Exec w bound (body src dst bit) dr _ :=
          .seq (.choose dr _ b hdr) (.seq (.det hp) hread)
        have hh := Exec.seq (.det hr) (Exec.loop_true
          (by simp [dr, StackLanguage.popped, hs]) hbody hloop)
        exact result_step d src dst hne bit b xs ▸ hh

lemma execution_sound (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst) (bit : Bool → Γ)
    (d e : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store src).length + (d.store dst).length < bound)
    (h : Exec w bound (code src dst bit) d e) :
    ∃ xs : List Bool, xs.length = (d.store src).length ∧ e = result d src dst bit xs := by
  generalize hn : (d.store src).length = n at *
  induction n generalizing d e with
  | zero =>
    have hs : d.store src = [] := by simpa using hn
    have hr := StackLanguage.Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    cases h with
    | seq hread hloop =>
      obtain rfl := (det_exec_iff hr).mp hread
      cases hloop with
      | loop_false => exact ⟨[], by simp [hs], result_nil d src dst hne bit hs⟩
      | loop_true ht _ _ => simp [StackLanguage.popped, hs] at ht
  | succ n ih =>
    cases hs : d.store src with
    | nil => simp [hs] at hn
    | cons g gs =>
      let dr := StackLanguage.popped d src (fun s value => {s with value := value})
      have hr : StackLanguage.Exec w bound (StackRoutines.read src) d dr := .pop d _ _ hd
      have hdr : Good w bound dr := hr.good.2
      have hdst : dr.store dst = d.store dst := by simp [dr, StackLanguage.popped, Ne.symm hne]
      have hpbound : (dr.store dst).length + 1 < bound := by rw [hdst]; omega
      cases h with
      | seq hread hloop =>
        obtain rfl := (det_exec_iff hr).mp hread
        obtain ⟨f, hbody, hrest⟩ := exec_loop_true hloop (by simp [dr, StackLanguage.popped, hs])
        obtain ⟨b, rfl⟩ := (body_exec_iff w bound src dst bit dr _ hdr hpbound).mp hbody
        let dp := pushed dr dst bit b
        have hdp : Good w bound dp := StackRoutines.good_pushed (d := chosen dr b) hdr dst (bit b) hpbound
        have hps : dp.store src = gs := by
          simp [dp, pushed, chosen, dr, StackLanguage.pushed, StackLanguage.popped, StackLanguage.assigned, hne, hs]
        have hpd : dp.store dst = bit b :: d.store dst := by
          simp [dp, pushed, chosen, StackLanguage.pushed, StackLanguage.assigned, hdst]
        have htail : Exec w bound (code src dst bit) dp e :=
          .seq (.det (.pop dp _ _ hdp)) hrest
        obtain ⟨xs, hxlen, hxe⟩ := ih dp e hdp htail
          (by rw [hps]; simpa [hs] using hn)
          (by rw [hpd]; simp only [List.length_cons]; omega)
        refine ⟨b :: xs, by simp [hxlen], ?_⟩
        exact hxe.trans (result_step d src dst hne bit b xs)

end

end Lax434930Proofs.InclusionAux.ChoiceProofs.GuessWord
