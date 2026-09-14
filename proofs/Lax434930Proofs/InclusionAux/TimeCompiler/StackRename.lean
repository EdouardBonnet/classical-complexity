import Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.InclusionAux.TimeCompiler.StackRename

open StackProgram

variable {K L Γ σ : Type} [DecidableEq K] [DecidableEq L]

def renameOp (f : K → L) : Op (fun _ : K => Γ) σ → Op (fun _ : L => Γ) σ
  | .push k g => .push (f k) g
  | .pop k g => .pop (f k) g
  | .peek k g => .peek (f k) g
  | .load g => .load g

def rename (f : K → L) : Program (fun _ : K => Γ) σ → Program (fun _ : L => Γ) σ
  | .atom o => .atom (renameOp f o)
  | .seq p q => .seq (rename f p) (rename f q)
  | .branch b p q => .branch b (rename f p) (rename f q)
  | .loop b p => .loop b (rename f p)

def project (f : K → L) (s : Store (fun _ : L => Γ) σ) : Store (fun _ : K => Γ) σ :=
  ⟨s.state, fun k => s.stk (f k)⟩

theorem op_project (f : K → L) (hf : Function.Injective f)
    (o : Op (fun _ : K => Γ) σ) (s : Store (fun _ : L => Γ) σ) :
    project f ((renameOp f o).apply s) = o.apply (project f s) := by
  cases o with
  | push k g | pop k g =>
      apply Store.ext
      · rfl
      · funext j
        by_cases h : j = k
        · subst j; simp [project, renameOp, Op.apply]
        · have hj : f j ≠ f k := fun he => h (hf he)
          simp [project, renameOp, Op.apply, h, hj]
  | peek k g | load g => rfl

omit [DecidableEq K] in
theorem op_frame (f : K → L) (o : Op (fun _ : K => Γ) σ)
    (s : Store (fun _ : L => Γ) σ) (key : L) (hk : key ∉ Set.range f) :
    ((renameOp f o).apply s).stk key = s.stk key := by
  have hne : ∀ k, key ≠ f k := fun k he => hk ⟨k, he.symm⟩
  cases o <;> simp [renameOp, Op.apply, hne]

/-- A verified program can be embedded in a larger finite stack layout.
The execution cost is unchanged, and every extra stack is preserved. -/
theorem rename_executes (f : K → L) (hf : Function.Injective f)
    {p : Program (fun _ : K => Γ) σ} {s t : Store (fun _ : K => Γ) σ} {cost : Nat}
    (h : Executes p s t cost) (s' : Store (fun _ : L => Γ) σ) (hs : project f s' = s) :
    ∃ t', Executes (rename f p) s' t' cost ∧ project f t' = t ∧
      ∀ key, key ∉ Set.range f → t'.stk key = s'.stk key := by
  induction h generalizing s' with
  | atom o s =>
      refine ⟨(renameOp f o).apply s', Executes.atom _ _, ?_, ?_⟩
      · rw [op_project f hf, hs]
      · exact op_frame f o s'
  | seq hp hq ihp ihq =>
      obtain ⟨u', hp', hu, hpu⟩ := ihp s' hs
      obtain ⟨t', hq', ht, hqt⟩ := ihq u' hu
      exact ⟨t', Executes.seq hp' hq', ht, fun key hk => (hqt key hk).trans (hpu key hk)⟩
  | branch_true hb hp ih =>
      obtain ⟨t', hp', ht, hpt⟩ := ih s' hs
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨t', Executes.branch_true (by rw [hstate]; exact hb) hp', ht, hpt⟩
  | branch_false hb hp ih =>
      obtain ⟨t', hp', ht, hpt⟩ := ih s' hs
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨t', Executes.branch_false (by rw [hstate]; exact hb) hp', ht, hpt⟩
  | loop_false hb =>
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨s', Executes.loop_false (by rw [hstate]; exact hb), hs, fun _ _ => rfl⟩
  | loop_true hb hp hq ihp ihq =>
      obtain ⟨u', hp', hu, hpu⟩ := ihp s' hs
      obtain ⟨t', hq', ht, hqt⟩ := ihq u' hu
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨t', Executes.loop_true (by rw [hstate]; exact hb) hp' hq', ht,
        fun key hk => (hqt key hk).trans (hpu key hk)⟩

def sumStore (s : Store (fun _ : K => Γ) σ) (extra : L → List Γ) : Store (fun _ : K ⊕ L => Γ) σ :=
  ⟨s.state, Sum.elim s.stk extra⟩

theorem executes_in_sum {p : Program (fun _ : K => Γ) σ} {s t : Store (fun _ : K => Γ) σ}
    {cost : Nat} (h : Executes p s t cost) (extra : L → List Γ) :
    Executes (rename Sum.inl p) (sumStore s extra) (sumStore t extra) cost := by
  obtain ⟨t', ht, hproj, hframe⟩ := rename_executes (L := K ⊕ L) Sum.inl Sum.inl_injective h
    (sumStore s extra) rfl
  have he : t' = sumStore t extra := by
    apply Store.ext
    · exact congrArg (fun q => q.state) hproj
    · funext key
      cases key with
      | inl k => exact congrArg (fun q => q.stk k) hproj
      | inr l => exact hframe (.inr l) (by simp)
  rwa [he] at ht

end Lax434930Proofs.InclusionAux.TimeCompiler.StackRename
