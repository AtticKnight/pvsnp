import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime

set_option autoImplicit false

/-- Keeping the first `k` bits of a binary string is polynomial-time (TM2), for every `k`:
a finite-state transducer with states `Fin (k + 1)` counting the bits copied so far. It copies
while the count is below `k` and afterwards writes nothing, so its output function from state
`q` is `List.take (k - q)`, which from state `0` is `List.take k`. Polynomial time then follows
from the settled unit `m2_transducer_polytime`. -/
theorem PvsNP.Units.tf_fun_take_all :
    ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.take k) := by
  intro k
  have key := PvsNP.Units.m2_transducer_polytime (Fin (k + 1))
    (fun q b => if h : q.val < k then (⟨q.val + 1, by omega⟩, some b) else (q, none))
    (fun _ => none)
    (fun q x => x.take (k - q.val))
    (by intro q; simp)
    (by
      intro q b x
      by_cases h : q.val < k
      · obtain ⟨m, hm⟩ : ∃ m, k - q.val = m + 1 := ⟨k - q.val - 1, by omega⟩
        have e2 : k - (q.val + 1) = m := by omega
        simp only [dif_pos h, hm, e2, List.take_succ_cons, Option.toList_some,
          List.singleton_append]
      · have e0 : k - q.val = 0 := by omega
        simp only [dif_neg h, e0, Option.toList_none, List.nil_append, List.take_zero])
    0
  exact key
