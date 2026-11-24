import Mathlib.Computability.Encoding

/-!
# How inputs and answers are written down

Every problem of this campaign is about binary strings, `List Bool`. A machine reads its input as
a string of symbols and writes its answer as one, so each kind of value needs a fixed way of being
written. This file fixes three, all of them Mathlib's own encodings:

* a binary string is written as itself, one symbol per bit;
* a pair of binary strings is written as the first string followed by the second, over the
  alphabet `Bool ⊕ Bool` (bits of the first string tagged `Sum.inl`, of the second `Sum.inr`), so
  no separator is needed and the written length is the sum of the two lengths;
* a yes/no answer is written as the one-symbol string `[b]`.

These are the conventions behind every statement's notion of "input length": the length of a
string, and for a pair the sum of the two lengths.
-/

set_option autoImplicit false

namespace PvsNP

/-- A binary string, written as itself: Mathlib's `Computability.encodingList Bool`. -/
abbrev encodeString : List Bool → List Bool :=
  (Computability.encodingList Bool).encode

/-- A pair of binary strings `(x, w)`, written as `x` then `w` over `Bool ⊕ Bool`: Mathlib's
`Computability.encodingProd` of two copies of `Computability.encodingList Bool`. -/
abbrev encodePair : List Bool × List Bool → List (Bool ⊕ Bool) :=
  (Computability.encodingProd (Computability.encodingList Bool)
    (Computability.encodingList Bool)).encode

/-- A yes/no answer `b`, written as the one-symbol string `[b]`: Mathlib's
`Computability.encodeBool`. -/
abbrev encodeAnswer : Bool → List Bool :=
  Computability.encodeBool

end PvsNP
