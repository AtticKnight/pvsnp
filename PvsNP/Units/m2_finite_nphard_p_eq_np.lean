import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_subset_np

set_option autoImplicit false

/-- If a finite language is NP-hard, then `P = NP` (TM2): every finite language is in `P`
    (`m2_p_finite`), and `P` is downward closed under Karp reductions (`m2_p_down_closed`). -/
theorem PvsNP.Units.m2_finite_nphard_p_eq_np :
    ∀ S : Finset (List Bool), PvsNP.NPHard ({x : List Bool | x ∈ S} : Language Bool) → PvsNP.P = PvsNP.NP := by
  intro S hHard
  have hfinP : ({x : List Bool | x ∈ S} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite S
  apply Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
  intro L hL
  exact PvsNP.Units.m2_p_down_closed L _ (hHard L hL) hfinP
