import Lax434930Proofs.InputTapeView
import Lax434930Proofs.WorkTapeView
import Lax434930Proofs.TM2Bounds

set_option backward.isDefEq.respectTransparency false

/-! A finite stack machine simulates each transition of the fixed work-space machine model. -/

namespace Lax434930Proofs.SpaceToStack

open Lax434930.PolynomialTime Lax434930.SpaceMachines Turing

noncomputable section

structure View (M : Machine) where
  state : M.Q
  input : InputTapeView.View
  left : List M.Γ
  current : M.Γ
  right : List M.Γ

def View.work {M : Machine} (v : View M) : WorkTapeView.View M :=
  ⟨v.state, v.input.position, v.left, v.current, v.right⟩

def View.expand {M : Machine} (v : View M) : M.Config := v.work.expand

def initial (M : Machine) (w : Word) : View M :=
  ⟨M.start, InputTapeView.initial w, [], M.blank, []⟩

def apply (M : Machine) (v : View M) (a : Action M.Γ M.Q) : View M :=
  let u := WorkTapeView.apply M v.input.word v.work a
  ⟨a.state, InputTapeView.move a.inputMove v.input, u.left, u.current, u.right⟩

lemma apply_work (M : Machine) (v : View M) (a : Action M.Γ M.Q)
    (hv : v.input.Valid) :
    (apply M v a).work = WorkTapeView.apply M v.input.word v.work a := by
  cases hm : a.workMove <;> cases hl : v.left <;>
    simp [apply, View.work, WorkTapeView.apply, hm, hl, InputTapeView.move_position _ _ hv]

lemma apply_expand (M : Machine) (v : View M) (a : Action M.Γ M.Q)
    (hv : v.input.Valid) :
    (apply M v a).expand = M.execute v.input.word v.expand a := by
  rw [View.expand, apply_work M v a hv, WorkTapeView.apply_expand]
  rfl

lemma initial_expand (M : Machine) (w : Word) : (initial M w).expand = M.initial :=
  WorkTapeView.initial_expand M

inductive Key | inputLeft | inputRight | workLeft | workRight | output
  deriving DecidableEq, Fintype

inductive Label (M : Machine) where
  | run (state : M.Q) (input : InputSymbol) (current : M.Γ)
  | clear (answer : Bool) (stack : Key)
  deriving Fintype

def Alphabet (M : Machine) : Key → Type
  | .workLeft | .workRight => M.Γ
  | _ => Bool

instance alphabet_fintype (M : Machine) (k : Key) : Fintype (Alphabet M k) := by
  cases k <;> unfold Alphabet <;> infer_instance

abbrev Register (M : Machine) := Option Bool × Option M.Γ
abbrev Code (M : Machine) := TM2.Stmt (Alphabet M) (Label M) (Register M)

def choose (M : Machine) (q : M.Q) (i : InputSymbol) (g : M.Γ) :
    Option (Action M.Γ M.Q) := (M.transition q i g).toList.head?

lemma choose_mem (M : Machine) (q : M.Q) (i : InputSymbol) (g : M.Γ)
    (a : Action M.Γ M.Q) (h : choose M q i g = some a) : a ∈ M.transition q i g := by
  obtain ⟨xs, hx⟩ := List.head?_eq_some_iff.mp h
  apply Finset.mem_toList.mp
  rw [hx]
  exact List.mem_cons_self

lemma choose_action (M : Machine) (hd : M.Deterministic) (q : M.Q) (i : InputSymbol)
    (g : M.Γ) (a : Action M.Γ M.Q) (ha : a ∈ M.transition q i g) :
    choose M q i g = some a := by
  cases h : choose M q i g with
  | none =>
    have he : M.transition q i g = ∅ := by simpa [choose] using h
    exact (Finset.notMem_empty a (he ▸ ha)).elim
  | some b =>
    have hb := choose_mem M q i g b h
    obtain rfl := hd q i g a ha b hb
    rfl

def inputCode (M : Machine) (d : Move) (i : InputSymbol)
    (cont : (Register M → InputSymbol) → Code M) : Code M :=
  match d, i with
  | .stay, _ | .left, .leftEnd | .right, .rightEnd => cont (fun _ => i)
  | .right, .leftEnd =>
    .pop .inputRight (fun r b => (b, r.2)) (cont (fun r => r.1.elim .rightEnd .bit))
  | .right, .bit b =>
    .push .inputLeft (fun _ => b)
      (.pop .inputRight (fun r b => (b, r.2)) (cont (fun r => r.1.elim .rightEnd .bit)))
  | .left, .rightEnd =>
    .pop .inputLeft (fun r b => (b, r.2)) (cont (fun r => r.1.elim .leftEnd .bit))
  | .left, .bit b =>
    .push .inputRight (fun _ => b)
      (.pop .inputLeft (fun r b => (b, r.2)) (cont (fun r => r.1.elim .leftEnd .bit)))

def workCode (M : Machine) (d : Move) (written : M.Γ) (q : M.Q)
    (input : Register M → InputSymbol) : Code M :=
  match d with
  | .stay => .goto (fun r => .run q (input r) written)
  | .right =>
    .push .workLeft (fun _ => written)
      (.pop .workRight (fun r g => (r.1, g))
        (.goto (fun r => .run q (input r) (r.2.getD M.blank))))
  | .left =>
    .pop .workLeft (fun r g => (r.1, g))
      (.branch (fun r => r.2.isSome)
        (.push .workRight (fun _ => written)
          (.goto (fun r => .run q (input r) (r.2.getD M.blank))))
        (.goto (fun r => .run q (input r) written)))

def nextKey : Key → Key
  | .inputLeft => .inputRight
  | .inputRight => .workLeft
  | .workLeft => .workRight
  | .workRight | .output => .output

def code (M : Machine) : Label M → Code M
  | .run q i g => match choose M q i g with
    | none => .goto (fun _ => .clear (M.accept q) .inputLeft)
    | some a => inputCode M a.inputMove i (workCode M a.workMove a.write a.state)
  | .clear b .output => .push .output (fun _ => b) (.load (fun _ => (none, none)) .halt)
  | .clear b k =>
    .pop k (fun _ g => (some g.isSome, none))
      (.branch (fun r => r.1.getD false)
        (.goto (fun _ => .clear b k)) (.goto (fun _ => .clear b (nextKey k))))

def machine (M : Machine) : FinTM2 where
  K := Key
  k₀ := .inputRight
  k₁ := .output
  Γ := Alphabet M
  Λ := Label M
  main := .run M.start .leftEnd M.blank
  σ := Register M
  initialState := (none, none)
  m := code M

def memory {M : Machine} (v : View M) : (k : Key) → List (Alphabet M k)
  | .inputLeft => v.input.left
  | .inputRight => v.input.right
  | .workLeft => v.left
  | .workRight => v.right
  | .output => []

def cfg {M : Machine} (v : View M) (r : Register M) : (machine M).Cfg :=
  ⟨some (.run v.state v.input.current v.current), r, memory v⟩

def inputRegister {M : Machine} (v : View M) (d : Move) (r : Register M) : Register M :=
  match d, v.input.current with
  | .right, .leftEnd | .right, .bit _ => (v.input.right.head?, r.2)
  | .left, .rightEnd | .left, .bit _ => (v.input.left.head?, r.2)
  | _, _ => r

def nextRegister {M : Machine} (v : View M) (a : Action M.Γ M.Q) (r : Register M) : Register M :=
  let r' := inputRegister v a.inputMove r
  match a.workMove with
  | .stay => r'
  | .left => (r'.1, v.left.head?)
  | .right => (r'.1, v.right.head?)

lemma init_eq (M : Machine) (w : Word) :
    initList (machine M) w = cfg (initial M w) (none, none) := by
  apply TM2Bounds.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> rfl

set_option maxHeartbeats 1600000 in
lemma action_step (M : Machine) (v : View M) (r : Register M) (a : Action M.Γ M.Q)
    (hv : v.input.Valid) (ha : choose M v.state v.input.current v.current = some a) :
    (machine M).step (cfg v r) = some (cfg (apply M v a) (nextRegister v a r)) := by
  cases v with
  | mk q input left current right =>
    cases input with
    | mk il i ir =>
      cases a with
      | mk q' written im wm =>
        cases im <;> cases i <;> cases il <;> cases ir <;> cases wm <;> cases left <;> cases right <;>
          simp_all [FinTM2.step, machine, code, cfg, memory, TM2.step, TM2.stepAux,
            inputCode, workCode, apply, View.work, WorkTapeView.apply,
            InputTapeView.move, InputTapeView.View.Valid, nextRegister, inputRegister,
            Function.update_apply] <;>
          funext k <;> cases k <;> rfl

end

end Lax434930Proofs.SpaceToStack
