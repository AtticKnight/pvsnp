import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m2_npc_mutual_karp :
    ∀ L₁ L₂ : Language Bool, PvsNP.NPComplete L₁ → PvsNP.NPComplete L₂ →
      PvsNP.KarpReducible L₁ L₂ ∧ PvsNP.KarpReducible L₂ L₁ :=
  fun L₁ L₂ h₁ h₂ => ⟨h₂.2 L₁ h₁.1, h₁.2 L₂ h₂.1⟩
