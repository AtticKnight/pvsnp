import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_npc_in_conp
import PvsNP.Units.m2_npc_exists

/-- NP = coNP exactly when some NP-complete language is in coNP (TM2). -/
theorem PvsNP.Units.m2_np_eq_conp_iff_npc_in_conp :
    PvsNP.NP = PvsNP.coNP ↔
      ∃ L : Language Bool, PvsNP.NPComplete L ∧ L ∈ PvsNP.coNP := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := PvsNP.Units.m2_npc_exists
    exact ⟨L, hL, h ▸ hL.1⟩
  · rintro ⟨L, hL, hco⟩
    exact PvsNP.Units.m2_npc_in_conp L hL hco
