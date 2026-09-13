import Lax434930Proofs.SavitchProofs.BinaryWords
import Lax434930Proofs.SavitchProofs.StackSearch

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.SearchProgram

open StackSearch
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Good)
open scoped Classical

noncomputable section

inductive Register where
  | a | b | middle | depth | frameA | frameB | frameMiddle | frameDepth | kinds | width | aux
  deriving DecidableEq, Fintype

inductive Phase where
  | call | scan | ret | done
  deriving DecidableEq, Fintype

structure Control (ε : Type) where
  phase : Phase
  answer : Bool
  overflow : Bool
  query : ε
  deriving Fintype

abbrev Alphabet (β : Type) := Sum β Symbol
abbrev Key (δ : Type) := Sum Register δ
abbrev Context (β ε : Type) := StackRoutines.Control (Alphabet β) (Control ε)
abbrev Data (β ε δ : Type) := StackLanguage.Data (Key δ) (Alphabet β) (Context β ε)
abbrev Code (β ε δ : Type) := StackLanguage.Command (Key δ) (Alphabet β) (Context β ε)

instance {β : Type} : Inhabited (Alphabet β) := ⟨.inr .tally⟩

variable {β ε δ : Type} {N : ℕ}

def key (r : Register) : Key δ := .inl r
def symbol (s : Symbol) : Alphabet β := .inr s
def bit (b : Bool) : Alphabet β := symbol (.bit b)
def readBit : Alphabet β → Bool
  | .inr (.bit b) => b
  | _ => false

@[simp] lemma readBit_bit (b : Bool) : readBit (bit (β := β) b) = b := rfl

def word (m n : ℕ) : List (Alphabet β) := (BinaryCounter.word m n).map bit
def unary (n : ℕ) : List (Alphabet β) := List.replicate n (symbol .tally)

@[simp] lemma word_length (m n : ℕ) : (word (β := β) m n).length = m := by simp [word]
@[simp] lemma unary_length (n : ℕ) : (unary (β := β) n).length = n := by simp [unary]
@[simp] lemma word_zero (m : ℕ) : word (β := β) m 0 = List.replicate m (bit false) := by
  simp [word, BinaryCounter.word_zero]

@[simp] lemma word_read (m n : ℕ) :
    (word (β := β) m n).map readBit = BinaryCounter.word m n := by
  simp [word, List.map_map, Function.comp_def]

lemma word_eq_fin_iff (m : ℕ) (a b : Fin (2 ^ m)) :
    word (β := β) m a = word m b ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (List.map readBit) h
    simp only [word_read] at hh
    exact Fin.ext ((BinaryCounter.word_eq_iff m a b a.isLt b.isLt).mp hh)
  · rintro rfl; rfl

@[simp] lemma separator_not_word (m n : ℕ) : symbol Symbol.separator ∉ word (β := β) m n := by
  simp [word, bit, symbol]

@[simp] lemma separator_not_unary (n : ℕ) : symbol Symbol.separator ∉ unary (β := β) n := by
  simp [unary, symbol]

def Frame.first : Frame N → Fin N
  | .left _ a _ _ | .right _ a _ _ => a
def Frame.second : Frame N → Fin N
  | .left _ _ b _ | .right _ _ b _ => b
def Frame.middle : Frame N → Fin N
  | .left _ _ _ m | .right _ _ _ m => m
def Frame.kind : Frame N → Alphabet β
  | .left .. => symbol .leftTag
  | .right .. => symbol .rightTag

def column (f : Frame N → List (Alphabet β)) (stack : List (Frame N)) : List (Alphabet β) :=
  stack.flatMap fun frame => f frame ++ [symbol .separator]

@[simp] lemma column_nil (f : Frame N → List (Alphabet β)) : column f [] = [] := rfl
@[simp] lemma column_cons (f : Frame N → List (Alphabet β)) (frame : Frame N) (stack) :
    column f (frame :: stack) = f frame ++ symbol .separator :: column f stack := by
  simp [column, List.append_assoc]

def stackStore (m : ℕ) (stack : List (Frame N)) : Register → List (Alphabet β)
  | .frameA => column (fun f => word m (Frame.first f)) stack
  | .frameB => column (fun f => word m (Frame.second f)) stack
  | .frameMiddle => column (fun f => word m (Frame.middle f)) stack
  | .frameDepth => column (fun f => unary f.depth) stack
  | .kinds => stack.map Frame.kind
  | .width => unary m
  | _ => []

def store (m : ℕ) : State N → Register → List (Alphabet β)
  | .call _ a _ _, .a => word m a
  | .call _ _ b _, .b => word m b
  | .call k _ _ _, .depth => unary k
  | .call _ _ _ stack, r => stackStore m stack r
  | .scan _ a _ _ _, .a => word m a
  | .scan _ _ b _ _, .b => word m b
  | .scan _ _ _ mid _, .middle => word m mid
  | .scan k _ _ _ _, .depth => unary k
  | .scan _ _ _ _ stack, r => stackStore m stack r
  | .ret _ stack, r => stackStore m stack r

def phase : State N → Phase
  | .call .. => .call
  | .scan .. => .scan
  | .ret .. => .ret

def Fits (m : ℕ) (s : State (2 ^ m)) (d : Data β ε δ) : Prop :=
  d.state.user.phase = phase s ∧
  (∀ r, d.store (key r) = store m s r) ∧
  (match s with
    | .ret answer _ => d.state.user.answer = answer
    | .scan _ _ _ mid _ => d.state.user.overflow = decide (mid = 2 ^ m)
    | _ => True)

def budget (m : ℕ) : ℕ := (m + 2) ^ 2

lemma column_length (m : ℕ) (stack : List (Frame N)) (f : Frame N → List (Alphabet β))
    (hf : ∀ frame ∈ stack, (f frame).length ≤ m) :
    (column f stack).length ≤ stack.length * (m + 1) := by
  induction stack with
  | nil => simp
  | cons frame stack ih =>
    have hhead := hf frame (by simp)
    have htail := ih (fun f hf' => hf f (by simp [hf']))
    simp only [column_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

lemma valid_depth (m : ℕ) (stack : List (Frame N)) (h : StackValid m stack) :
    ∀ f ∈ stack, f.depth ≤ m := by
  induction stack with
  | nil => simp
  | cons f stack ih =>
    intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · have := h.1; omega
    · exact ih h.2 g hg

lemma stackStore_length (m : ℕ) (stack : List (Frame N))
    (hlen : stack.length ≤ m) (h : StackValid m stack) (r : Register) :
    (stackStore (β := β) m stack r).length ≤ m * (m + 1) + m := by
  have hc (f : Frame N → List (Alphabet β)) (hf : ∀ f' ∈ stack, (f f').length ≤ m) :=
    (column_length m stack f hf).trans (Nat.mul_le_mul_right (m + 1) hlen)
  have ha := hc (fun f => word m (Frame.first f)) (by intros; simp)
  have hb := hc (fun f => word m (Frame.second f)) (by intros; simp)
  have hm := hc (fun f => word m (Frame.middle f)) (by intros; simp)
  have hd := hc (fun f => unary f.depth) (by simpa using valid_depth m stack h)
  cases r <;> simp only [stackStore, List.length_nil, List.length_map, unary_length] <;> omega

lemma store_length (m : ℕ) (s : State N) (h : s.Valid m) (r : Register) :
    (store (β := β) m s r).length ≤ m * (m + 1) + m := by
  cases s with
  | call k a b stack =>
    have hk := h.1
    have hh := stackStore_length (β := β) m stack (by omega) h.2 r
    cases r <;> simp_all [store, stackStore]
    all_goals omega
  | scan k a b mid stack =>
    have hk := h.1
    have hh := stackStore_length (β := β) m stack (by omega) h.2.2 r
    cases r <;> simp_all [store, stackStore]
    all_goals omega
  | ret answer stack => exact stackStore_length m stack h.1 h.2 r

lemma store_lt_budget (m : ℕ) (s : State N) (h : s.Valid m) (r : Register) :
    (store (β := β) m s r).length + m + 1 < budget m := by
  have := store_length (β := β) m s h r
  dsimp [budget]
  nlinarith

end

end Lax434930Proofs.SavitchProofs.SearchProgram
