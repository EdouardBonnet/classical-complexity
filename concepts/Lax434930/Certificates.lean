import Lax434930.PolynomialTime

/-!
---
title: Binary encoding of an input and a certificate
type: definition
---
To encode a pair $(x,y)$ of binary strings, replace each bit $b$ of $x$ by
$0b$, then append a single $1$ followed by $y$. This encoding has length
$2|x|+|y|+1$ and has a unique decoding. In particular, a polynomial bound in
the encoded length is a polynomial bound in the combined input and
certificate lengths.
-/

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

/-- Decode a pair, rejecting a missing delimiter or an incomplete bit block. -/
def unpair : Word → Option (Word × Word)
  | [] => none
  | true :: y => some ([], y)
  | false :: [] => none
  | false :: b :: rest => (unpair rest).map (fun p => (b :: p.1, p.2))

/-- Encoding followed by decoding recovers both strings. -/
axiom unpair_pair (x y : Word) : unpair (pair x y) = some (x, y)

/-- Distinct pairs of strings have distinct encodings. -/
axiom pair_injective : Function.Injective (fun p : Word × Word => pair p.1 p.2)

/-- The encoding has linear length in its two arguments. -/
axiom pair_length (x y : Word) : (pair x y).length = 2 * x.length + y.length + 1

end Lax434930.Certificates
