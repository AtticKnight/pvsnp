import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

/-- Keeping the first 3 bits of a binary string is polynomial-time (TM2): a finite-state
transducer with states `Fin (3 + 1)` counting the bits copied so far. It copies while the
count is below 3 and afterwards writes nothing, so its output function from state `q` is
`List.take (3 - q)`, which from state `0` is `List.take 3`. Polynomial time then follows
from the settled unit `m2_transducer_polytime`. -/
theorem PvsNP.Units.tf_fun_take : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.take 3) := by
  have key := PvsNP.Units.m2_transducer_polytime (Fin (3 + 1))
    (fun q b => if q.val < 3 then (q + 1, some b) else (q, none))
    (fun _ => none)
    (fun q x => x.take (3 - q.val))
    (by intro q; simp)
    (by
      intro q b x
      fin_cases q <;> simp)
    0
  exact key
