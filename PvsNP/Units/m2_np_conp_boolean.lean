import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_conp_union
import PvsNP.Units.m2_conp_inter

theorem PvsNP.Units.m2_np_conp_boolean :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP ∩ PvsNP.coNP → L₂ ∈ PvsNP.NP ∩ PvsNP.coNP →
      L₁ᶜ ∈ PvsNP.NP ∩ PvsNP.coNP ∧ L₁ ⊔ L₂ ∈ PvsNP.NP ∩ PvsNP.coNP ∧ L₁ ⊓ L₂ ∈ PvsNP.NP ∩ PvsNP.coNP := by
  intro L₁ L₂ h₁ h₂
  refine ⟨⟨h₁.2, ?_⟩,
    ⟨PvsNP.Units.m2_np_union L₁ L₂ h₁.1 h₂.1, PvsNP.Units.m2_conp_union L₁ L₂ h₁.2 h₂.2⟩,
    ⟨PvsNP.Units.m2_np_inter L₁ L₂ h₁.1 h₂.1, PvsNP.Units.m2_conp_inter L₁ L₂ h₁.2 h₂.2⟩⟩
  show L₁ᶜᶜ ∈ PvsNP.NP
  rw [compl_compl]
  exact h₁.1
