import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_npc_exists

theorem PvsNP.Units.m2_nphard_in_p_iff :
    (∃ L : Language Bool, PvsNP.NPHard L ∧ L ∈ PvsNP.P) ↔ PvsNP.P = PvsNP.NP := by
  constructor
  · rintro ⟨L, hhard, hLP⟩
    exact Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
      (fun L' hL' => PvsNP.Units.m2_p_down_closed L' L (hhard L' hL') hLP)
  · intro hEq
    obtain ⟨L, hLNP, hLhard⟩ := PvsNP.Units.m2_npc_exists
    exact ⟨L, hLhard, hEq ▸ hLNP⟩
