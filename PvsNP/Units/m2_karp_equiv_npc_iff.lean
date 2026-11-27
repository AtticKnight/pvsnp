import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_nphard_transfer
import PvsNP.Units.m2_np_down_closed

set_option autoImplicit false

/-- Languages that Karp-reduce to each other are NP-hard together (`m2_nphard_transfer`) and
NP-complete together (combining `m2_nphard_transfer` with `m2_np_down_closed`). -/
theorem PvsNP.Units.m2_karp_equiv_npc_iff :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ → PvsNP.KarpReducible L₂ L₁ →
      (PvsNP.NPHard L₁ ↔ PvsNP.NPHard L₂) ∧ (PvsNP.NPComplete L₁ ↔ PvsNP.NPComplete L₂) := by
  intro L₁ L₂ h12 h21
  exact ⟨⟨fun h => PvsNP.Units.m2_nphard_transfer L₁ L₂ h h12,
          fun h => PvsNP.Units.m2_nphard_transfer L₂ L₁ h h21⟩,
         ⟨fun ⟨hm, hh⟩ => ⟨PvsNP.Units.m2_np_down_closed L₂ L₁ h21 hm,
                           PvsNP.Units.m2_nphard_transfer L₁ L₂ hh h12⟩,
          fun ⟨hm, hh⟩ => ⟨PvsNP.Units.m2_np_down_closed L₁ L₂ h12 hm,
                           PvsNP.Units.m2_nphard_transfer L₂ L₁ hh h21⟩⟩⟩
