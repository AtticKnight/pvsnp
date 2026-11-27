import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_np

/-- NP = coNP exactly when an NP language intersected with a coNP language stays
in NP: forward by rewriting the coNP side into NP and closing under ∩; backward
by intersecting with the universal language (in NP) to recover each side. -/
theorem PvsNP.Units.m2_z_np_eq_conp_iff_inter_conp :
    PvsNP.NP = PvsNP.coNP ↔
      ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.coNP → L₁ ⊓ L₂ ∈ PvsNP.NP := by
  have hTop : (⊤ : Language Bool) ∈ PvsNP.NP := by
    show (Set.univ : Language Bool) ∈ PvsNP.NP
    exact PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.2
  constructor
  · intro h L₁ L₂ h1 h2
    have h2' : L₂ ∈ PvsNP.NP := by
      rw [h]
      exact h2
    exact PvsNP.Units.m2_np_inter L₁ L₂ h1 h2'
  · intro h
    apply Set.Subset.antisymm
    · intro M hM
      show Mᶜ ∈ PvsNP.NP
      have hMc : Mᶜ ∈ PvsNP.coNP := by
        show (Mᶜ)ᶜ ∈ PvsNP.NP
        rw [compl_compl]
        exact hM
      have h1 := h ⊤ Mᶜ hTop hMc
      simpa using h1
    · intro M hM
      have h1 := h ⊤ M hTop hM
      simpa using h1
