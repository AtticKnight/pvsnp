import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_npc_in_conp

/-- An NP-hard member of the intersection would be NP-complete and in coNP, forcing equality. -/
theorem PvsNP.Units.m2_np_conp_no_nphard :
    PvsNP.NP ≠ PvsNP.coNP → ∀ L ∈ PvsNP.NP ∩ PvsNP.coNP, ¬ PvsNP.NPHard L := by
  intro sep L both hard
  exact sep (PvsNP.Units.m2_npc_in_conp L ⟨both.1, hard⟩ both.2)
