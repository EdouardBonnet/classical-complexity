import Lax434930.Certificates
import Mathlib.Tactic

namespace Lax434930Proofs.Certificates

open Lax434930.PolynomialTime Lax434930.Certificates

/--
---
conclusion: Lax434930.Certificates.unpair_pair
assumptions:
---
Induct on the first word, decoding one two-bit block at a time.
-/
theorem unpair_pair (x y : Word) : unpair (pair x y) = some (x, y) := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pair, unpair, ih]

/--
---
conclusion: Lax434930.Certificates.pair_injective
assumptions:
---
Apply the decoder to an equality of encodings.
-/
theorem pair_injective : Function.Injective (fun p : Word × Word => pair p.1 p.2) := by
  intro a b h
  have hd := congrArg unpair h
  simpa only [unpair_pair, Prod.mk.eta, Option.some.injEq] using hd

/--
---
conclusion: Lax434930.Certificates.pair_length
assumptions:
---
Each bit of the first word contributes two bits, and the delimiter contributes one.
-/
theorem pair_length (x y : Word) : (pair x y).length = 2 * x.length + y.length + 1 := by
  induction x with
  | nil => simp [pair]
  | cons b x ih =>
    simp only [pair, List.length_cons, ih]
    omega

end Lax434930Proofs.Certificates
