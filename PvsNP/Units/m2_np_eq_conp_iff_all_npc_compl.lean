import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_npc_exists
import PvsNP.Units.m2_npc_in_conp

set_option autoImplicit false

/-- `NP = coNP` iff the complement of every NP-complete language is in `NP`. -/
theorem PvsNP.Units.m2_np_eq_conp_iff_all_npc_compl :
    PvsNP.NP = PvsNP.coNP ↔ ∀ L : Language Bool, PvsNP.NPComplete L → Lᶜ ∈ PvsNP.NP := by
  constructor
  · intro h L hL
    have hco : L ∈ PvsNP.coNP := by rw [← h]; exact hL.1
    exact hco
  · intro h
    obtain ⟨L, hL⟩ := PvsNP.Units.m2_npc_exists
    exact PvsNP.Units.m2_npc_in_conp L hL (h L hL)
