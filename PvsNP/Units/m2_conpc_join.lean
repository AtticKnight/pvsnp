import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_conp_join
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

theorem PvsNP.Units.m2_conpc_join :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.coNP → (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L₁) →
  L₂ ∈ PvsNP.coNP →
    ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∈ PvsNP.coNP ∧
      ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) := by
  intro L₁ L₂ h₁ hhard h₂
  refine ⟨m2_conp_join L₁ L₂ h₁ h₂, ?_⟩
  intro L' hL'
  exact m2_karp_trans L' L₁ _ (hhard L' hL') (m2_join_karp_sides L₁ L₂).1
