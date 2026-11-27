import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_conp_one_inclusion
import PvsNP.Units.m2_npc_exists
import PvsNP.Units.m2_np_down_closed

/-- Collapse transfers completeness to coNP. Conversely every coNP language reduces to the given NP language. -/
theorem PvsNP.Units.m2_np_eq_conp_iff_conphard_in_np :
    PvsNP.NP = PvsNP.coNP ↔ ∃ L ∈ PvsNP.NP, ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L := by
  constructor
  · intro eqn
    obtain ⟨L, h⟩ := PvsNP.Units.m2_npc_exists
    exact ⟨L, h.1, fun A hA => h.2 A (eqn.symm ▸ hA)⟩
  · rintro ⟨L, hL, hard⟩
    apply PvsNP.Units.m2_np_conp_one_inclusion.2.1
    intro A hA
    exact PvsNP.Units.m2_np_down_closed A L (hard A hA) hL
