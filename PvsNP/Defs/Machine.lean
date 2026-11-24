import Mathlib.Computability.TuringMachine.Computable

/-!
# Polynomial-time computability (the machine model)

The machine model of this campaign is Mathlib's, and none of it is redefined here:

* `Turing.FinTM2`: a Turing machine with finitely many stacks (one of them holds the input,
  one the output), finitely many function labels and finitely many internal states; its input
  alphabet is finite, and since every symbol it pushes is a function of its finitely many
  internal states, only finitely many symbols ever reach its other stacks;
* `Turing.TM2OutputsInTime tm l l' m`: started with `l` on its input stack, `tm` halts within `m`
  steps with `l'` on its output stack, every other stack empty;
* `Turing.TM2ComputableInPolyTime ea eb f`: a machine together with a polynomial `time` such that,
  for every `a`, the machine turns the written input `ea a` into the written output `eb (f a)`
  within `time` evaluated at the length of `ea a` steps.

A step executes one of the machine's finitely many statements (`Turing.TM2.Stmt`), so a step is a
bounded number of elementary pushes, pops and tests: up to a constant factor, the number of steps
is the running time of a multi-stack machine.

Mathlib's `TM2ComputableInPolyTime` is data (a machine and its bound), not a proposition. The one
definition below turns it into the proposition "some such machine exists".

Prior art: the `Nonempty (Turing.TM2ComputableInPolyTime …)` form is the one of
`IsPolyTimeWithEncoding` in `FormalConjecturesForMathlib/Computability/Complexity.lean` of
github.com/google-deepmind/formal-conjectures at commit 1d3feb7ddcfd6d922c49a96b5134dba488b7de1c
(Apache License 2.0), and of `ComputableInPolyTime` in `lean/PEqualNP/Defs/Base.lean` of
github.com/brilliant-hq/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0). Modified: it takes the two encodings as plain functions (formal-conjectures
takes `Computability.Encoding`s), under this project's name.
-/

set_option autoImplicit false

namespace PvsNP

/-- `f` is computable in polynomial time, its inputs written by `ea` and its outputs by `eb`:
some finite multi-stack Turing machine (Mathlib's `Turing.FinTM2`) computes `f` within a number
of steps bounded by a polynomial in the length of the written input. -/
def PolyTimeComputable {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) :
    Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

end PvsNP
