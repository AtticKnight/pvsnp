import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_inter

theorem PvsNP.Units.m2_p_diff :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
      ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) ∈ PvsNP.P := by
  intro L₁ L₂ h₁ h₂
  have heq : ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) = L₁ ⊓ L₂ᶜ := by
    ext x
    rfl
  rw [heq]
  exact PvsNP.Units.m2_p_inter L₁ L₂ᶜ h₁ (PvsNP.Units.m2_p_compl L₂ h₂)
