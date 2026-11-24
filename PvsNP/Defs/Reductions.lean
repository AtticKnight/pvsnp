import PvsNP.Defs.Classes

/-!
# Karp reductions, NP-hardness and NP-completeness

* `KarpReducible L₁ L₂`: some function on binary strings, computable in polynomial time, sends
  every member of `L₁` to a member of `L₂` and every non-member of `L₁` to a non-member of `L₂`
  (a polynomial-time many-one reduction).
* `NPHard L`: every language in NP is Karp reducible to `L`.
* `NPComplete L`: `L` is in NP and NP-hard.

Prior art: the same three notions, under other names, are `PolyTimeReducible`, `NPHard` and
`NPComplete` in `lean/PEqualNP/Defs/Base.lean` of github.com/brilliant-hq/pequalnp-proofs at
commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0); they are the textbook ones
(Arora and Barak, Computational Complexity: A Modern Approach (2009), Section 2.2). Modified: the
reduction is stated over this project's `PolyTimeComputable` with the string encoding
`encodeString` on both sides.
-/

set_option autoImplicit false

namespace PvsNP

/-- `L₁` is Karp reducible to `L₂` (polynomial-time many-one reducible): some function `f` on
binary strings, computable in polynomial time, satisfies `x ∈ L₁ ↔ f x ∈ L₂` for every string
`x`. -/
def KarpReducible (L₁ L₂ : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool,
    PolyTimeComputable encodeString encodeString f ∧ ∀ x : List Bool, x ∈ L₁ ↔ f x ∈ L₂

/-- `L` is NP-hard: every language in NP is Karp reducible to `L`. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, KarpReducible L' L

/-- `L` is NP-complete: `L` is in NP and NP-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

end PvsNP
