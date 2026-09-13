import Lax434930Proofs.SavitchProofs.PairScan
import Lax434930Proofs.SavitchProofs.MapStack
import Lax434930Proofs.SavitchProofs.BinaryWords

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackMacros

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Exec Good assigned popped pushed)
open StackRoutines (Control Data Code)
open scoped Classical

noncomputable section

structure Macro (K Γ σ : Type) where
  code : Code (K := K) (Γ := Γ) (σ := σ)
  result : Word → Data (K := K) (Γ := Γ) (σ := σ) → Data (K := K) (Γ := Γ) (σ := σ)
  guard : Word → ℕ → Data (K := K) (Γ := Γ) (σ := σ) → Prop
  correct : ∀ w bound d, Good w bound d → guard w bound d → Exec w bound code d (result w d)

namespace Macro

variable {K Γ σ : Type}

def skip : Macro K Γ σ where
  code := .skip
  result _ d := d
  guard _ _ _ := True
  correct _ _ d hd _ := .skip d hd

def seq (A B : Macro K Γ σ) : Macro K Γ σ where
  code := .seq A.code B.code
  result w d := B.result w (A.result w d)
  guard w b d := A.guard w b d ∧ B.guard w b (A.result w d)
  correct w b d hd h := by
    have ha := A.correct w b d hd h.1
    exact .seq ha (B.correct w b _ ha.good.2 h.2)

def branch (test : Control Γ σ → Bool) (A B : Macro K Γ σ) : Macro K Γ σ where
  code := .branch test A.code B.code
  result w d := if test d.state then A.result w d else B.result w d
  guard w b d := if test d.state then A.guard w b d else B.guard w b d
  correct w b d hd h := by
    cases ht : test d.state
    · exact .branch_false ht (B.correct w b d hd (by simpa [ht] using h))
    · exact .branch_true ht (A.correct w b d hd (by simpa [ht] using h))

def assign (f : Control Γ σ → Control Γ σ) : Macro K Γ σ where
  code := .assign f
  result _ d := assigned d (f d.state)
  guard _ _ _ := True
  correct _ _ d hd _ := .assign d f hd

def read (src : K) : Macro K Γ σ where
  code := StackRoutines.read src
  result _ d := popped d src (fun s value => {s with value := value})
  guard _ _ _ := True
  correct _ _ d hd _ := .pop d _ _ hd

def move (direction : Control Γ σ → Move) : Macro K Γ σ where
  code := .move direction
  result w d := StackLanguage.moved w d (direction d.state)
  guard _ _ _ := True
  correct _ _ d hd _ := .move d direction hd

def sample : Macro K Γ σ where
  code := .input (fun s i => {s with input := i})
  result w d := assigned d {d.state with input := readInput w d.inputHead}
  guard _ _ _ := True
  correct _ _ d hd _ := .input d _ hd

def push (dst : K) (g : Control Γ σ → Γ) : Macro K Γ σ where
  code := .push (fun _ => dst) g
  result _ d := pushed d dst (g d.state)
  guard _ b d := (d.store dst).length + 1 < b
  correct _ _ d hd h := .push d _ _ hd (StackRoutines.good_pushed hd dst _ h)

def clear (src : K) : Macro K Γ σ where
  code := StackRoutines.clear src
  result _ d := StackRoutines.cleared d src
  guard _ _ _ := True
  correct w b d hd _ := StackRoutines.clear_exec w b src d hd

def copy [Inhabited Γ] (src dst aux : K) : Macro K Γ σ where
  code := StackRoutines.copy src dst aux
  result _ d := ⟨{d.state with value := none}, d.inputHead, Function.update d.store dst (d.store src)⟩
  guard _ _ d := src ≠ dst ∧ src ≠ aux ∧ dst ≠ aux ∧ d.store aux = []
  correct w b d hd h := StackRoutines.copy_exec w b src dst aux h.1 h.2.1 h.2.2.1 d hd h.2.2.2

def copyMap [Inhabited Γ] (src dst aux : K) (f : Γ → Γ) : Macro K Γ σ where
  code := StackRoutines.copyMap src dst aux f
  result _ d := ⟨{d.state with value := none}, d.inputHead,
    Function.update d.store dst ((d.store src).map f)⟩
  guard _ _ d := src ≠ dst ∧ src ≠ aux ∧ dst ≠ aux ∧ d.store aux = []
  correct w b d hd h := StackRoutines.copyMap_exec w b src dst aux h.1 h.2.1 h.2.2.1 f d hd h.2.2.2

def transfer [Inhabited Γ] (src dst : K) (f : Γ → Γ := id) : Macro K Γ σ where
  code := StackRoutines.transfer src dst f
  result _ d := StackRoutines.transferred d src dst f
  guard _ b d := src ≠ dst ∧ (d.store src).length + (d.store dst).length < b
  correct w b d hd h := StackRoutines.transfer_exec w b src dst h.1 d hd h.2 f

def copyAppend [Inhabited Γ] (src dst aux : K) : Macro K Γ σ where
  code := StackRoutines.copyAppend src dst aux
  result _ d := StackRoutines.copiedAppend d src dst
  guard _ b d := src ≠ dst ∧ src ≠ aux ∧ dst ≠ aux ∧ d.store aux = [] ∧
    (d.store src).length + (d.store dst).length < b
  correct w b d hd h := StackRoutines.copyAppend_exec w b src dst aux h.1 h.2.1 h.2.2.1
    d hd h.2.2.2.1 h.2.2.2.2

def scanPairs (src dst : K) (f : Control Γ σ → Control Γ σ) : Macro K Γ σ where
  code := StackRoutines.scanPairs src dst f
  result _ d := StackRoutines.scannedPairs d src dst f
  guard _ _ _ := src ≠ dst
  correct w b d hd h := StackRoutines.scanPairs_exec w b src dst h f d hd

def save [Inhabited Γ] (src dst aux : K) (separator : Γ) : Macro K Γ σ where
  code := StackRoutines.pushField src dst aux separator
  result _ d := ⟨{d.state with value := none}, d.inputHead,
    Function.update d.store dst (d.store src ++ separator :: d.store dst)⟩
  guard _ b d := src ≠ dst ∧ src ≠ aux ∧ dst ≠ aux ∧ d.store aux = [] ∧
    (d.store src).length + (d.store dst).length + 1 < b
  correct w b d hd h :=
    StackRoutines.pushField_exec w b src dst aux h.1 h.2.1 h.2.2.1 separator d hd h.2.2.2.1 h.2.2.2.2

def before (separator : Γ) (xs : List Γ) : List Γ := xs.takeWhile (fun g => decide (g ≠ separator))
def after (separator : Γ) (xs : List Γ) : List Γ := (xs.dropWhile (fun g => decide (g ≠ separator))).tail

lemma before_append (separator : Γ) (xs tail : List Γ) (h : separator ∉ xs) :
    before separator (xs ++ separator :: tail) = xs := by
  induction xs with
  | nil => simp [before]
  | cons x xs ih =>
    have hh : separator ≠ x ∧ separator ∉ xs := by simpa only [List.mem_cons, not_or] using h
    simpa [before, Ne.symm hh.1] using ih hh.2

lemma after_append (separator : Γ) (xs tail : List Γ) (h : separator ∉ xs) :
    after separator (xs ++ separator :: tail) = tail := by
  induction xs with
  | nil => simp [after]
  | cons x xs ih =>
    have hh : separator ≠ x ∧ separator ∉ xs := by simpa only [List.mem_cons, not_or] using h
    simpa [after, Ne.symm hh.1] using ih hh.2

lemma field_split (separator : Γ) (xs : List Γ) (h : separator ∈ xs) :
    separator ∉ before separator xs ∧ xs = before separator xs ++ separator :: after separator xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = separator
    · subst x; simp [before, after]
    · have hh : separator ∈ xs := by simpa [Ne.symm hx] using h
      obtain ⟨ha, hb⟩ := ih hh
      constructor
      · simpa [before, hx, Ne.symm hx] using ha
      · simpa [before, after, hx] using congrArg (x :: ·) hb

def restore [Inhabited Γ] (src dst aux : K) (separator : Γ) : Macro K Γ σ where
  code := StackRoutines.popField src dst aux separator
  result _ d := ⟨{d.state with value := none}, d.inputHead,
    Function.update (Function.update d.store src (after separator (d.store src))) dst
      (before separator (d.store src))⟩
  guard _ _ d := src ≠ dst ∧ src ≠ aux ∧ dst ≠ aux ∧ d.store aux = [] ∧ separator ∈ d.store src
  correct w b d hd h := by
    obtain ⟨hn, hs⟩ := field_split separator (d.store src) h.2.2.2.2
    exact StackRoutines.popField_exec w b src dst aux h.1 h.2.1 h.2.2.1 separator _ _ hn d hd h.2.2.2.1 hs

def compare (first second : K) : Macro K Γ σ where
  code := StackRoutines.compareWords first second
  result _ d :=
    ⟨{d.state with
        value := none
        other := none
        flag := decide (d.store first = d.store second)}, d.inputHead,
      Function.update (Function.update d.store first []) second []⟩
  guard _ _ _ := first ≠ second
  correct w b d hd h := StackRoutines.compareWords_exec w b first second h d hd

def increment [Inhabited Γ] (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Macro K Γ σ where
  code := BinaryCounter.counter src aux bit readBit
  result _ d :=
    ⟨{d.state with value := none, flag := BinaryCounter.carry ((d.store src).map readBit)},
      d.inputHead, Function.update d.store src ((BinaryCounter.increment ((d.store src).map readBit)).map bit)⟩
  guard _ _ d := src ≠ aux ∧ (∀ b, readBit (bit b) = b) ∧ d.store aux = [] ∧
    ((d.store src).map readBit).map bit = d.store src
  correct w b d hd h := BinaryCounter.counter_exec w b src aux h.1 bit readBit h.2.1
    ((d.store src).map readBit) d hd h.2.2.2.symm h.2.2.1

end Macro

end

end Lax434930Proofs.SavitchProofs.StackMacros
