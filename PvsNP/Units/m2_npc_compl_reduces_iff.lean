import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_npc_in_conp

theorem PvsNP.Units.m2_npc_compl_reduces_iff :
    ∀ L₁ L₂ : Language Bool, PvsNP.NPComplete L₁ → PvsNP.NPComplete L₂ →
      (PvsNP.KarpReducible L₁ᶜ L₂ ↔ PvsNP.NP = PvsNP.coNP) := by
  intro L₁ L₂ h1 h2
  have hL1 : L₁ ∈ PvsNP.NP := h1.1
  obtain ⟨hL2, hhard2⟩ := h2
  constructor
  · intro hred
    have hc : L₁ᶜ ∈ PvsNP.NP := PvsNP.Units.m2_np_down_closed L₁ᶜ L₂ hred hL2
    exact PvsNP.Units.m2_npc_in_conp L₁ h1 hc
  · intro hEq
    have hco : L₁ ∈ PvsNP.coNP := hEq ▸ hL1
    exact hhard2 L₁ᶜ hco
