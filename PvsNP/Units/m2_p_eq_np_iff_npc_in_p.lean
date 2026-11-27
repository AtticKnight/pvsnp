import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_npc_exists
import PvsNP.Units.m2_npc_in_p

/-- Use one known NP-complete language for the universal reverse implication and for the existential forward implication. -/
theorem PvsNP.Units.m2_p_eq_np_iff_npc_in_p :
    (PvsNP.P = PvsNP.NP ↔ ∀ L : Language Bool, PvsNP.NPComplete L → L ∈ PvsNP.P) ∧
  (PvsNP.P = PvsNP.NP ↔ ∃ L : Language Bool, PvsNP.NPComplete L ∧ L ∈ PvsNP.P) := by
  obtain ⟨A, hA⟩ := PvsNP.Units.m2_npc_exists
  constructor
  · constructor
    · intro eq L h
      exact eq.symm ▸ h.1
    · intro all
      exact PvsNP.Units.m2_npc_in_p A hA (all A hA)
  · constructor
    · intro eq
      exact ⟨A, hA, eq.symm ▸ hA.1⟩
    · rintro ⟨L, h, hP⟩
      exact PvsNP.Units.m2_npc_in_p L h hP
