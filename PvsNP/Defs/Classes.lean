import Mathlib.Computability.Language
import PvsNP.Defs.Encoding
import PvsNP.Defs.Machine

/-!
# P, NP and coNP

A decision problem is a language over the binary alphabet, Mathlib's `Language Bool` (a set of
binary strings). The classes are sets of such languages.

* `PolyTimeDecidable L`: some yes/no function on strings that answers yes exactly on the members of
  `L` is computable in polynomial time (`PvsNP.PolyTimeComputable`, a Mathlib multi-stack machine
  answering `[true]` or `[false]`).
* `P`: the languages decidable in polynomial time.
* `PolyTimeVerifier L V p`: `V` is a polynomial-time yes/no function on pairs `(x, w)`, and `x` is
  in `L` exactly when some certificate `w` of length at most `p (length of x)` makes `V` answer
  yes. `p` is a polynomial with natural-number coefficients, written out as one (see below).
* `NP`: the languages with a polynomial-time verifier (the verifier definition of NP).
* `coNP`: the languages whose complement is in NP.

The certificate bound is a `Polynomial ℕ`, never an arbitrary function bounded by one: with an
arbitrary bound `b` in its place, `∃ w, w.length ≤ b x.length ∧ …` could hide an undecidable set of
lengths in `b`, and the class would contain undecidable languages.

Prior art: the verifier form of `NP` and the complement form of `coNP` follow `NP` and `coNP` in
`FormalConjecturesForMathlib/Computability/Complexity.lean` of
github.com/google-deepmind/formal-conjectures at commit 1d3feb7ddcfd6d922c49a96b5134dba488b7de1c
(Apache License 2.0), which cite Definition 2.1 of Arora and Barak, Computational Complexity: A
Modern Approach (2009); deciding a set by a yes/no function `f` with `x ∈ L ↔ f x = true` follows
`DecidableInPolyTime` in `lean/PEqualNP/Defs/Base.lean` of github.com/brilliant-hq/pequalnp-proofs
at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0). Modified: problems are
`Language Bool` (formal-conjectures uses functions `List Bool → Bool`); the verifier is a yes/no
function on pairs written by Mathlib's `encodingProd`; the verifier condition is named
(`PolyTimeVerifier`) so a statement can mention one verifier.
-/

set_option autoImplicit false

namespace PvsNP

/-- `L` is decidable in polynomial time: a yes/no function on binary strings that answers yes
exactly on the members of `L` is computable in polynomial time. -/
def PolyTimeDecidable (L : Language Bool) : Prop :=
  ∃ f : List Bool → Bool,
    PolyTimeComputable encodeString encodeAnswer f ∧ ∀ x : List Bool, x ∈ L ↔ f x = true

/-- The class P: the languages over the binary alphabet decidable in polynomial time. -/
def P : Set (Language Bool) :=
  {L | PolyTimeDecidable L}

/-- `V` is a polynomial-time verifier for `L` with certificates of length at most `p`: `V` is a
yes/no function on pairs (input, certificate) computable in polynomial time in the length of the
pair, and a string `x` is in `L` exactly when some certificate `w` with
`w.length ≤ p.eval x.length` makes `V` answer yes on `(x, w)`. -/
def PolyTimeVerifier (L : Language Bool) (V : List Bool × List Bool → Bool) (p : Polynomial ℕ) :
    Prop :=
  PolyTimeComputable encodePair encodeAnswer V ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ V (x, w) = true

/-- The class NP: the languages over the binary alphabet that have a polynomial-time verifier with
polynomially bounded certificates. -/
def NP : Set (Language Bool) :=
  {L | ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ), PolyTimeVerifier L V p}

/-- The class coNP: the languages over the binary alphabet whose complement is in NP. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

end PvsNP
