import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_trans

theorem PvsNP.Units.m2_npc_transfer :
    ∀ L₁ L₂ : Language Bool,
      PvsNP.NPComplete L₁ → L₂ ∈ PvsNP.NP → PvsNP.KarpReducible L₁ L₂ → PvsNP.NPComplete L₂ := by
  intro L₁ L₂ h₁ h₂ h₁₂
  exact ⟨h₂, fun L hL => PvsNP.Units.m2_karp_trans L L₁ L₂ (h₁.2 L hL) h₁₂⟩
