import Lax434930Proofs.SavitchProofs.StackRoutines

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackRoutines

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage (Exec Good)
open scoped Classical

noncomputable section

variable {K Γ σ : Type} [Inhabited Γ]

def mapStack (src aux : K) (f : Γ → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (transfer src aux f) (transfer aux src)

lemma mapStack_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (f : Γ → Γ) (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (ha : d.store aux = []) :
    Exec w bound (mapStack src aux f) d
      ⟨{d.state with value := none}, d.inputHead, Function.update d.store src ((d.store src).map f)⟩ := by
  have h₁ := transfer_exec w bound src aux hne d hd (by simpa [ha] using hd.2 src) f
  let dt := transferred d src aux f
  have h₂ := transfer_exec w bound aux src (Ne.symm hne) dt h₁.good.2
    (by simpa [dt, transferred, ha, hne] using hd.2 src)
  have he : transferred dt aux src =
      ⟨{d.state with value := none}, d.inputHead, Function.update d.store src ((d.store src).map f)⟩ := by
    simp only [transferred, dt]
    congr 1
    funext k
    by_cases hs : k = src <;> by_cases ha' : k = aux <;>
      simp_all [Function.update_apply, List.map_reverse]
  exact he ▸ Exec.seq h₁ h₂

def copyMap (src dst aux : K) (f : Γ → Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (copy src dst aux) (mapStack dst aux f)

lemma copyMap_exec (w : Word) (bound : ℕ) (src dst aux : K)
    (h₁ : src ≠ dst) (h₂ : src ≠ aux) (h₃ : dst ≠ aux) (f : Γ → Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) (ha : d.store aux = []) :
    Exec w bound (copyMap src dst aux f) d
      ⟨{d.state with value := none}, d.inputHead, Function.update d.store dst ((d.store src).map f)⟩ := by
  have hc := copy_exec w bound src dst aux h₁ h₂ h₃ d hd ha
  have hm := mapStack_exec w bound dst aux h₃ f _ hc.good.2
    (by simp [Ne.symm h₃, ha])
  simpa using! Exec.seq hc hm

end

end Lax434930Proofs.SavitchProofs.StackRoutines
