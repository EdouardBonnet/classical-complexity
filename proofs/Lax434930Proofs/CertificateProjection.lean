import Lax434930.Certificates
import Lax434930Proofs.Time
import Lax434930Proofs.PolynomialComposition

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.CertificateProjection

open Turing Time Lax434930.PolynomialTime Lax434930.Certificates

/-- Read the first component, stopping at the pair delimiter. -/
def first : Word → Word
  | [] => []
  | true :: _ => []
  | false :: [] => []
  | false :: b :: rest => b :: first rest

lemma first_pair (x y : Word) : first (pair x y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa [pair, first] using ih

inductive Key | input | temporary | output deriving DecidableEq, Fintype
inductive Label | scan | clear | reverse deriving DecidableEq, Fintype

open Key Label

def code : Label → TM2.Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .scan => .pop .input (fun _ b => b)
      (.branch (fun b => b == some false)
        (.pop .input (fun _ b => b)
          (.branch Option.isSome
            (.push .temporary (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .scan))))
            (.load (fun _ => none) (.goto (fun _ => .clear)))))
        (.load (fun _ => none) (.goto (fun _ => .clear))))
  | .clear => .pop .input (fun _ b => b)
      (.load (fun b => b)
        (.branch Option.isSome (.load (fun _ => none) (.goto (fun _ => .clear)))
          (.load (fun _ => none) (.goto (fun _ => .reverse)))))
  | .reverse => .pop .temporary (fun _ b => b)
      (.branch Option.isSome
        (.push .output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .reverse))))
        (.load (fun _ => none) .halt))

def machine : FinTM2 where
  K := Key
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .scan
  σ := Option Bool
  initialState := none
  m := code

def memory (xs ys zs : Word) : Key → Word
  | .input => xs
  | .temporary => ys
  | .output => zs

def cfg (l : Option Label) (xs ys zs : Word) : machine.Cfg :=
  ⟨l, none, memory xs ys zs⟩

lemma scan_nil (ys : Word) : machine.step (cfg (some .scan) [] ys []) =
    some (cfg (some .clear) [] ys []) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma scan_true (xs ys : Word) : machine.step (cfg (some .scan) (true :: xs) ys []) =
    some (cfg (some .clear) xs ys []) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma scan_false_nil (ys : Word) : machine.step (cfg (some .scan) [false] ys []) =
    some (cfg (some .clear) [] ys []) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma scan_false_cons (b : Bool) (xs ys : Word) :
    machine.step (cfg (some .scan) (false :: b :: xs) ys []) =
      some (cfg (some .scan) xs (b :: ys) []) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma clear_nil (ys : Word) : machine.step (cfg (some .clear) [] ys []) =
    some (cfg (some .reverse) [] ys []) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma clear_cons (b : Bool) (xs ys : Word) :
    machine.step (cfg (some .clear) (b :: xs) ys []) =
      some (cfg (some .clear) xs ys []) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma reverse_nil (zs : Word) : machine.step (cfg (some .reverse) [] [] zs) =
    some (cfg none [] [] zs) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma reverse_cons (b : Bool) (ys zs : Word) :
    machine.step (cfg (some .reverse) [] (b :: ys) zs) =
      some (cfg (some .reverse) [] ys (b :: zs)) := by
  simp [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux] <;>
    funext k <;> cases k <;> rfl

lemma reverse_run (ys zs : Word) :
    Run machine.step (ys.length + 1) (cfg (some .reverse) [] ys zs)
      (cfg none [] [] (ys.reverse ++ zs)) := by
  induction ys generalizing zs with
  | nil => simpa using Run.one (reverse_nil zs)
  | cons b ys ih =>
      simpa [List.reverse_cons, List.append_assoc] using! Run.cons (reverse_cons b ys zs) (ih (b :: zs))

lemma clear_run (xs ys : Word) :
    Run machine.step (xs.length + ys.length + 2) (cfg (some .clear) xs ys [])
      (cfg none [] [] ys.reverse) := by
  induction xs with
  | nil => simpa using! Run.cons (clear_nil ys) (reverse_run ys [])
  | cons b xs ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! Run.cons (clear_cons b xs ys) ih

lemma scan_run (xs ys : Word) :
    ∃ n ≤ 2 * xs.length + ys.length + 3,
      Run machine.step n (cfg (some .scan) xs ys [])
        (cfg none [] [] (ys.reverse ++ first xs)) := by
  induction xs using first.induct generalizing ys with
  | case1 =>
      refine ⟨ys.length + 3, by simp, ?_⟩
      simpa [first, Nat.add_assoc] using! Run.cons (scan_nil ys) (clear_run [] ys)
  | case2 xs =>
      refine ⟨xs.length + ys.length + 3, by simp <;> omega, ?_⟩
      simpa [first, Nat.add_assoc] using! Run.cons (scan_true xs ys) (clear_run xs ys)
  | case3 =>
      refine ⟨ys.length + 3, by simp <;> omega, ?_⟩
      simpa [first, Nat.add_assoc] using! Run.cons (scan_false_nil ys) (clear_run [] ys)
  | case4 b xs ih =>
      obtain ⟨n, hn, hr⟩ := ih (b :: ys)
      refine ⟨n + 1, by simp at *; omega, ?_⟩
      simpa [first, List.reverse_cons, List.append_assoc] using! Run.cons (scan_false_cons b xs ys) hr

lemma init_eq (xs : Word) : initList machine xs = cfg (some .scan) xs [] [] := by
  apply TM2Bounds.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> rfl

lemma halt_eq (xs : Word) : haltList machine xs = cfg none [] [] xs := by
  apply TM2Bounds.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> rfl

noncomputable def computable : TM2ComputableInPolyTime id id first where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 3
  outputsFun xs := by
    let n := Classical.choose (scan_run xs [])
    have hn := (Classical.choose_spec (scan_run xs [])).1
    have hr := (Classical.choose_spec (scan_run xs [])).2
    refine { steps := n
             steps_le_m := by simpa using hn
             evals_in_steps := ?_ }
    simpa [init_eq, halt_eq, Equiv.refl] using! hr.iterate

end Lax434930Proofs.CertificateProjection
