import PvsNP.Defs.Encoding
import PvsNP.Defs.Machine
import PvsNP.Defs.Classes
import PvsNP.Defs.Reductions
import PvsNP.Defs.SingleTape

/-!
# The definitions root

Every definition a statement of this campaign may mention, beyond Mathlib, is in the modules
imported above; `AUDIT.md` beside this tree is their reading list. A definitions module imports
only Mathlib and other definitions modules, and holds definitions only: no theorem a unit could
lean on and no axiom.

* `PvsNP.Defs.Encoding`: how strings, pairs of strings and yes/no answers are written.
* `PvsNP.Defs.Machine`: polynomial-time computability on Mathlib's multi-stack machines.
* `PvsNP.Defs.Classes`: polynomial-time decidability, P, verifiers, NP, coNP.
* `PvsNP.Defs.Reductions`: Karp reducibility, NP-hard, NP-complete.
* `PvsNP.Defs.SingleTape`: the single-tape machine and the same notions on it, the names the
  bridge between the two models is stated with.
-/
