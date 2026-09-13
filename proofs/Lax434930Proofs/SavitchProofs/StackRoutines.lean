import Lax434930Proofs.SavitchProofs.StackLanguage

set_option backward.isDefEq.respectTransparency false

namespace Lax434930Proofs.SavitchProofs.StackRoutines

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open StackLanguage
open scoped Classical

noncomputable section

structure Control (Γ σ : Type) where
  user : σ
  value : Option Γ
  flag : Bool
  input : InputSymbol
  other : Option Γ := none
  deriving Fintype

variable {K Γ σ : Type}

abbrev Data := StackLanguage.Data K Γ (Control Γ σ)
abbrev Code := Command K Γ (Control Γ σ)

def read (src : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .pop (fun _ => src) (fun s value => {s with value := value})

def write [Inhabited Γ] (dst : K) (f : Γ → Γ := id) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .push (fun _ => dst) (fun s => f (s.value.getD default))

def transfer [Inhabited Γ] (src dst : K) (f : Γ → Γ := id) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (read src) (.loop (fun s => s.value.isSome) (.seq (write dst f) (read src)))

def clear (src : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (read src) (.loop (fun s => s.value.isSome) (read src))

def cleared (d : Data (K := K) (Γ := Γ) (σ := σ)) (src : K) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none}, d.inputHead, Function.update d.store src []⟩

def transferred (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) (f : Γ → Γ := id) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none}, d.inputHead,
    Function.update (Function.update d.store src []) dst ((d.store src).reverse.map f ++ d.store dst)⟩

lemma good_store_update {w : Word} {bound : ℕ} {d : Data (K := K) (Γ := Γ) (σ := σ)}
    (hd : Good w bound d) (k : K) (xs : List Γ) (hx : xs.length < bound) :
    Good w bound ⟨d.state, d.inputHead, Function.update d.store k xs⟩ := by
  refine ⟨hd.1, ?_⟩
  intro j
  by_cases hj : j = k
  · subst j
    simpa using hx
  · simpa [Function.update_of_ne hj] using hd.2 j

lemma good_pushed {w : Word} {bound : ℕ} {d : Data (K := K) (Γ := Γ) (σ := σ)}
    (hd : Good w bound d) (k : K) (g : Γ) (hx : (d.store k).length + 1 < bound) :
    Good w bound (pushed d k g) := good_store_update hd k (g :: d.store k) hx

lemma transfer_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : (d.store src).length + (d.store dst).length < bound) (f : Γ → Γ := id) :
    Exec w bound (transfer src dst f) d (transferred d src dst f) := by
  generalize hxs : d.store src = xs at *
  induction xs generalizing d with
  | nil =>
    have hr := Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    have hg := hr.good.2
    have hf : (fun s : Control Γ σ => s.value.isSome)
        (popped d src (fun s value => {s with value := value})).state = false := by
      simp [popped, hxs]
    have hl := Exec.loop_false (fun s : Control Γ σ => s.value.isSome)
      (.seq (write dst f) (read src)) _ hg hf
    have he : popped d src (fun s value => {s with value := value}) = transferred d src dst f := by
      simp only [popped, transferred, hxs, List.head?_nil, List.tail_nil, List.reverse_nil,
        List.map_nil, List.nil_append]
      congr 1
      funext j
      by_cases hjs : j = src <;> by_cases hjd : j = dst <;>
        simp_all [Function.update_apply]
    exact he ▸ Exec.seq hr hl
  | cons g xs ih =>
    let dr := popped d src (fun s value => {s with value := value})
    have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
    have hdr : Good w bound dr := hr.good.2
    have hsv : dr.state.value = some g := by simp [dr, popped, hxs]
    let dp := pushed dr dst (f g)
    have hdst : dr.store dst = d.store dst := by
      simp [dr, popped, Function.update_of_ne (Ne.symm hne)]
    have hdp : Good w bound dp := by
      apply good_pushed hdr dst (f g)
      rw [hdst]
      simp only [List.length_cons] at hb
      omega
    have hw : Exec w bound (write dst f) dr dp := by
      simpa [write, dp, hsv] using
        (Exec.push dr (fun _ => dst) (fun s => f (s.value.getD default)) hdr
          (by simpa [hsv] using hdp))
    have hpSrc : dp.store src = xs := by simp [dp, pushed, dr, popped, hne, hxs]
    have hpDst : dp.store dst = f g :: d.store dst := by simp [dp, pushed, hdst]
    have hpBudget : (dp.store src).length + (dp.store dst).length < bound := by
      rw [hpSrc, hpDst, List.length_cons]
      simp only [List.length_cons] at hb
      omega
    have htail := ih dp hdp hpSrc (by simpa [hpSrc] using hpBudget)
    cases htail with
    | @seq _ _ _ dm _ hread hloop =>
      have hbody : Exec w bound (.seq (write dst f) (read src)) dr dm := .seq hw hread
      have hl : Exec w bound (.loop (fun s : Control Γ σ => s.value.isSome)
          (.seq (write dst f) (read src))) dr (transferred dp src dst f) :=
        .loop_true (by simp [hsv]) hbody hloop
      have he : transferred dp src dst f = transferred d src dst f := by
        simp only [transferred, dp, pushed, dr, popped, hxs, List.head?_cons,
          List.tail_cons, List.reverse_cons]
        congr 1
        funext j
        by_cases hjs : j = src <;> by_cases hjd : j = dst <;>
          simp_all [Function.update_apply, List.reverse_cons, List.append_assoc]
      exact he ▸ Exec.seq hr hl

lemma clear_exec (w : Word) (bound : ℕ) (src : K)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) :
    Exec w bound (clear src) d (cleared d src) := by
  generalize hxs : d.store src = xs at *
  induction xs generalizing d with
  | nil =>
    have hr := Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    have hl := Exec.loop_false (fun s : Control Γ σ => s.value.isSome) (read src) _ hr.good.2
      (by simp [popped, hxs])
    simpa [cleared, popped, hxs] using! Exec.seq hr hl
  | cons g xs ih =>
    let dr := popped d src (fun s value => {s with value := value})
    have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
    have hsr : dr.store src = xs := by simp [dr, popped, hxs]
    have htail := ih dr hr.good.2 hsr
    cases htail with
    | @seq _ _ _ dm _ hread hloop =>
      have hl : Exec w bound (.loop (fun s : Control Γ σ => s.value.isSome) (read src))
          dr (cleared dr src) := .loop_true (by simp [dr, popped, hxs]) hread hloop
      have he : cleared dr src = cleared d src := by simp [cleared, dr, popped]
      exact he ▸ Exec.seq hr hl

def putWord (dst : K) : List Γ → Code (K := K) (Γ := Γ) (σ := σ)
  | [] => .skip
  | g :: xs => .seq (putWord dst xs) (.push (fun _ => dst) (fun _ => g))

lemma prefix_exec (w : Word) (bound : ℕ) (dst : K) (xs : List Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb : xs.length + (d.store dst).length < bound) :
    Exec w bound (putWord dst xs) d
      ⟨d.state, d.inputHead, Function.update d.store dst (xs ++ d.store dst)⟩ := by
  induction xs with
  | nil => simpa using! Exec.skip d hd
  | cons g xs ih =>
    have hx := ih (by simp only [List.length_cons] at hb; omega)
    have hs := Exec.push _ (fun _ => dst) (fun _ => g) hx.good.2
      (good_pushed hx.good.2 dst g
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb))
    simpa [pushed] using! Exec.seq hx hs

def fanout [Inhabited Γ] (src first second : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (read src) (.loop (fun s => s.value.isSome)
    (.seq (write first) (.seq (write second) (read src))))

def fanned (d : Data (K := K) (Γ := Γ) (σ := σ)) (src first second : K) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none}, d.inputHead,
    Function.update (Function.update (Function.update d.store src [])
      first ((d.store src).reverse ++ d.store first))
      second ((d.store src).reverse ++ d.store second)⟩

lemma fanout_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src first second : K)
    (h₁ : src ≠ first) (h₂ : src ≠ second) (h₃ : first ≠ second)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hb₁ : (d.store src).length + (d.store first).length < bound)
    (hb₂ : (d.store src).length + (d.store second).length < bound) :
    Exec w bound (fanout src first second) d (fanned d src first second) := by
  generalize hxs : d.store src = xs at *
  induction xs generalizing d with
  | nil =>
    have hr := Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    have hl := Exec.loop_false (fun s : Control Γ σ => s.value.isSome)
      (.seq (write first) (.seq (write second) (read src))) _ hr.good.2
      (by simp [popped, hxs])
    have he : popped d src (fun s value => {s with value := value}) =
        fanned d src first second := by
      simp only [popped, fanned, hxs, List.head?_nil, List.tail_nil, List.reverse_nil,
        List.nil_append]
      congr 1
      funext j
      by_cases hs : j = src <;> by_cases hf : j = first <;> by_cases hg : j = second <;>
        simp_all [Function.update_apply]
    exact he ▸ Exec.seq hr hl
  | cons g xs ih =>
    let dr := popped d src (fun s value => {s with value := value})
    have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
    have hsv : dr.state.value = some g := by simp [dr, popped, hxs]
    have hf : dr.store first = d.store first := by simp [dr, popped, Ne.symm h₁]
    have hg : dr.store second = d.store second := by simp [dr, popped, Ne.symm h₂]
    let dp₁ := pushed dr first g
    have hd₁ : Good w bound dp₁ := good_pushed hr.good.2 first g (by
      rw [hf]; simp only [List.length_cons] at hb₁; omega)
    have hw₁ : Exec w bound (write first) dr dp₁ := by
      simpa [write, dp₁, hsv] using
        (Exec.push dr (fun _ => first) (fun s => s.value.getD default) hr.good.2
          (by simpa [hsv] using hd₁))
    have hg₁ : dp₁.store second = d.store second := by simp [dp₁, pushed, Ne.symm h₃, hg]
    let dp₂ := pushed dp₁ second g
    have hd₂ : Good w bound dp₂ := good_pushed hd₁ second g (by
      rw [hg₁]; simp only [List.length_cons] at hb₂; omega)
    have hw₂ : Exec w bound (write second) dp₁ dp₂ := by
      simpa [write, dp₂, dp₁, pushed, hsv] using
        (Exec.push dp₁ (fun _ => second) (fun s => s.value.getD default) hd₁
          (by simpa [dp₁, pushed, hsv] using! hd₂))
    have hsrc : dp₂.store src = xs := by simp [dp₂, dp₁, pushed, dr, popped, h₁, h₂, hxs]
    have hfirst : dp₂.store first = g :: d.store first := by simp [dp₂, dp₁, pushed, h₃, hf]
    have hsecond : dp₂.store second = g :: d.store second := by simp [dp₂, pushed, hg₁]
    have hbudget₁ : xs.length + (dp₂.store first).length < bound := by
      rw [hfirst, List.length_cons]; simp only [List.length_cons] at hb₁; omega
    have hbudget₂ : xs.length + (dp₂.store second).length < bound := by
      rw [hsecond, List.length_cons]; simp only [List.length_cons] at hb₂; omega
    have htail := ih dp₂ hd₂ hsrc hbudget₁ hbudget₂
    cases htail with
    | @seq _ _ _ dm _ hread hloop =>
      have hl : Exec w bound (.loop (fun s : Control Γ σ => s.value.isSome)
          (.seq (write first) (.seq (write second) (read src)))) dr (fanned dp₂ src first second) :=
        .loop_true (by simp [hsv]) (.seq hw₁ (.seq hw₂ hread)) hloop
      have he : fanned dp₂ src first second = fanned d src first second := by
        simp only [fanned, dp₂, dp₁, pushed, dr, popped, hxs, List.head?_cons, List.tail_cons]
        congr 1
        funext j
        by_cases hs : j = src <;> by_cases hf : j = first <;> by_cases hg : j = second <;>
          simp_all [Function.update_apply, List.reverse_cons, List.append_assoc]
      exact he ▸ Exec.seq hr hl

def copyAppend [Inhabited Γ] (src dst aux : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (transfer src aux) (fanout aux src dst)

def copiedAppend (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K) :
    Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := none}, d.inputHead, Function.update d.store dst (d.store src ++ d.store dst)⟩

lemma copyAppend_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst aux : K)
    (h₁ : src ≠ dst) (h₂ : src ≠ aux) (h₃ : dst ≠ aux)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (ha : d.store aux = []) (hb : (d.store src).length + (d.store dst).length < bound) :
    Exec w bound (copyAppend src dst aux) d (copiedAppend d src dst) := by
  have ht := transfer_exec w bound src aux h₂ d hd (by simpa [ha] using hd.2 src)
  let dt := transferred d src aux
  have hs : dt.store src = [] := by simp [dt, transferred, h₂]
  have hu : dt.store aux = (d.store src).reverse := by simp [dt, transferred, ha]
  have hd' : dt.store dst = d.store dst := by simp [dt, transferred, h₃, Ne.symm h₁]
  have hf := fanout_exec w bound aux src dst (Ne.symm h₂) (Ne.symm h₃) h₁ dt ht.good.2
    (by simpa [hu, hs] using hd.2 src) (by simpa [hu, hd'] using hb)
  have he : fanned dt aux src dst = copiedAppend d src dst := by
    simp only [fanned, copiedAppend, dt, transferred]
    congr 1
    funext j
    by_cases hj₁ : j = src <;> by_cases hj₂ : j = dst <;> by_cases hj₃ : j = aux <;>
      simp_all [Function.update_apply]
  exact he ▸ Exec.seq ht hf

def copy [Inhabited Γ] (src dst aux : K) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (clear dst) (copyAppend src dst aux)

lemma copy_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst aux : K)
    (h₁ : src ≠ dst) (h₂ : src ≠ aux) (h₃ : dst ≠ aux)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) (ha : d.store aux = []) :
    Exec w bound (copy src dst aux) d
      ⟨{d.state with value := none}, d.inputHead, Function.update d.store dst (d.store src)⟩ := by
  have hc := clear_exec w bound dst d hd
  let dc := cleared d dst
  have hs : dc.store src = d.store src := by simp [dc, cleared, h₁]
  have ht := copyAppend_exec w bound src dst aux h₁ h₂ h₃ dc hc.good.2
    (by simp [dc, cleared, Ne.symm h₃, ha]) (by simpa [dc, cleared, h₁] using hd.2 src)
  simpa [copiedAppend, dc, cleared, h₁] using! Exec.seq hc ht

def transferUntil [Inhabited Γ] (src dst : K) (stop : Γ → Bool) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (read src) (.loop (fun s => s.value.isSome && !(s.value.map stop).getD true)
    (.seq (write dst) (read src)))

def untilResult (d : Data (K := K) (Γ := Γ) (σ := σ)) (src dst : K)
    (xs : List Γ) (separator : Γ) (tail : List Γ) : Data (K := K) (Γ := Γ) (σ := σ) :=
  ⟨{d.state with value := some separator}, d.inputHead,
    Function.update (Function.update d.store src tail) dst (xs.reverse ++ d.store dst)⟩

lemma until_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst : K) (hne : src ≠ dst)
    (stop : Γ → Bool) (xs : List Γ) (separator : Γ) (tail : List Γ)
    (hstop : stop separator = true) (hxs : ∀ g ∈ xs, stop g = false)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hsrc : d.store src = xs ++ separator :: tail)
    (hb : xs.length + (d.store dst).length < bound) :
    Exec w bound (transferUntil src dst stop) d (untilResult d src dst xs separator tail) := by
  induction xs generalizing d with
  | nil =>
    have hr := Exec.pop d (fun _ => src) (fun s value => {s with value := value}) hd
    have hl := Exec.loop_false
      (fun s : Control Γ σ => s.value.isSome && !(s.value.map stop).getD true)
      (.seq (write dst) (read src)) _ hr.good.2 (by simp [popped, hsrc, hstop])
    have he : popped d src (fun s value => {s with value := value}) =
        untilResult d src dst [] separator tail := by
      simp only [popped, untilResult, hsrc, List.nil_append, List.head?_cons, List.tail_cons,
        List.reverse_nil]
      congr 1
      funext j
      by_cases hs : j = src <;> by_cases ht : j = dst <;> simp_all [Function.update_apply]
    exact he ▸ Exec.seq hr hl
  | cons g xs ih =>
    have hg : stop g = false := hxs g (by simp)
    have htail : ∀ a ∈ xs, stop a = false := fun a ha => hxs a (List.mem_cons_of_mem g ha)
    let dr := popped d src (fun s value => {s with value := value})
    have hr : Exec w bound (read src) d dr := Exec.pop d _ _ hd
    have hsv : dr.state.value = some g := by simp [dr, popped, hsrc]
    have hdst : dr.store dst = d.store dst := by simp [dr, popped, Ne.symm hne]
    let dp := pushed dr dst g
    have hdp : Good w bound dp := good_pushed hr.good.2 dst g (by
      rw [hdst]; simp only [List.length_cons] at hb; omega)
    have hp : Exec w bound (write dst) dr dp := by
      simpa [write, dp, hsv] using Exec.push dr (fun _ => dst) (fun s => s.value.getD default)
        hr.good.2 (by simpa [hsv] using hdp)
    have hpSrc : dp.store src = xs ++ separator :: tail := by
      simp [dp, pushed, dr, popped, hsrc, hne]
    have hpDst : dp.store dst = g :: d.store dst := by simp [dp, pushed, hdst]
    have hb' : xs.length + (dp.store dst).length < bound := by
      rw [hpDst, List.length_cons]; simp only [List.length_cons] at hb; omega
    have ht := ih htail dp hdp hpSrc hb'
    cases ht with
    | @seq _ _ _ dm _ hread hloop =>
      have hl : Exec w bound
          (.loop (fun s : Control Γ σ => s.value.isSome && !(s.value.map stop).getD true)
            (.seq (write dst) (read src))) dr (untilResult dp src dst xs separator tail) :=
        .loop_true (by simp [hsv, hg]) (.seq hp hread) hloop
      have he : untilResult dp src dst xs separator tail = untilResult d src dst (g :: xs) separator tail := by
        simp only [untilResult, dp, pushed, dr, popped, hsrc, List.cons_append, List.head?_cons,
          List.tail_cons]
        congr 1
        funext j
        by_cases hs : j = src <;> by_cases ht : j = dst <;>
          simp_all [Function.update_apply, List.reverse_cons, List.append_assoc]
      exact he ▸ Exec.seq hr hl

def pushField [Inhabited Γ] (src dst aux : K) (separator : Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (.push (fun _ => dst) (fun _ => separator)) (copyAppend src dst aux)

lemma pushField_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst aux : K)
    (h₁ : src ≠ dst) (h₂ : src ≠ aux) (h₃ : dst ≠ aux) (separator : Γ)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) (ha : d.store aux = [])
    (hb : (d.store src).length + (d.store dst).length + 1 < bound) :
    Exec w bound (pushField src dst aux separator) d
      ⟨{d.state with value := none}, d.inputHead,
        Function.update d.store dst (d.store src ++ separator :: d.store dst)⟩ := by
  let dp := pushed d dst separator
  have hpGood : Good w bound dp := good_pushed hd dst separator (by omega)
  have hp := Exec.push d (fun _ => dst) (fun _ => separator) hd hpGood
  have ht := copyAppend_exec w bound src dst aux h₁ h₂ h₃ dp hpGood
    (by simp [dp, pushed, Ne.symm h₃, ha]) (by
      simpa [dp, pushed, h₁, Nat.add_assoc] using hb)
  simpa [copiedAppend, dp, pushed, h₁] using! Exec.seq hp ht

def popField [Inhabited Γ] (src dst aux : K) (separator : Γ) : Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (clear dst) (.seq (transferUntil src aux (fun g => decide (g = separator))) (transfer aux dst))

lemma popField_exec [Inhabited Γ] (w : Word) (bound : ℕ) (src dst aux : K)
    (h₁ : src ≠ dst) (h₂ : src ≠ aux) (h₃ : dst ≠ aux) (separator : Γ)
    (xs tail : List Γ) (hsep : separator ∉ xs)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d) (ha : d.store aux = [])
    (hsrc : d.store src = xs ++ separator :: tail) :
    Exec w bound (popField src dst aux separator) d
      ⟨{d.state with value := none}, d.inputHead,
        Function.update (Function.update d.store src tail) dst xs⟩ := by
  have hc := clear_exec w bound dst d hd
  let dc := cleared d dst
  have hu := until_exec w bound src aux h₂ (fun g => decide (g = separator)) xs separator tail
    (by simp) (by intro g hg; simp; exact fun h => hsep (h ▸ hg)) dc hc.good.2
    (by simpa [dc, cleared, h₁] using hsrc) (by
      have hl := hd.2 src
      simp [hsrc] at hl
      simp [dc, cleared, Ne.symm h₃, ha]
      omega)
  let du := untilResult dc src aux xs separator tail
  have haux : du.store aux = xs.reverse := by simp [du, untilResult, dc, cleared, Ne.symm h₃, ha]
  have hdst : du.store dst = [] := by simp [du, untilResult, dc, cleared, h₃, Ne.symm h₁]
  have ht := transfer_exec w bound aux dst (Ne.symm h₃) du hu.good.2
    (by
      have hx : (du.store aux).length < bound := hu.good.2.2 aux
      simpa [haux, hdst] using hx)
  have he : transferred du aux dst =
      ⟨{d.state with value := none}, d.inputHead,
        Function.update (Function.update d.store src tail) dst xs⟩ := by
    simp only [transferred, du, untilResult, dc, cleared]
    congr 1
    funext j
    by_cases hs : j = src <;> by_cases ht : j = dst <;> by_cases hu : j = aux <;>
      simp_all [Function.update_apply]
  exact he ▸ Exec.seq hc (Exec.seq hu ht)

end

end Lax434930Proofs.SavitchProofs.StackRoutines
