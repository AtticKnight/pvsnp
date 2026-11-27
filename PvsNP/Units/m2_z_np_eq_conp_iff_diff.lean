import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_trivial

/-- `NP = coNP` exactly when `NP` is closed under set difference. Forward:
under the equality the second language lies in `coNP`, so its complement
lies in `NP` and the difference is an intersection of two `NP` languages.
Backward: taking the first language to be everything makes the difference
a complement, so every `NP` language has its complement in `NP`, i.e.
`NP ⊆ coNP`; the other inclusion follows by complementing twice. -/
theorem PvsNP.Units.m2_z_np_eq_conp_iff_diff :
    PvsNP.NP = PvsNP.coNP ↔ ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
      ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) ∈ PvsNP.NP := by
  constructor
  · intro h L₁ L₂ h₁ h₂
    have h₂co : L₂ ∈ PvsNP.coNP := by rw [← h]; exact h₂
    have h₂c : L₂ᶜ ∈ PvsNP.NP := h₂co
    have heq : ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) = L₁ ⊓ L₂ᶜ := by
      ext x
      constructor
      · intro h
        exact ⟨h.1, h.2⟩
      · intro h
        exact ⟨h.1, h.2⟩
    rw [heq]
    exact PvsNP.Units.m2_np_inter L₁ L₂ᶜ h₁ h₂c
  · intro h
    have hsub : PvsNP.NP ⊆ PvsNP.coNP := by
      intro L hL
      have huniv : (Set.univ : Language Bool) ∈ PvsNP.NP :=
        PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.2
      have hdiff := h Set.univ L huniv hL
      have heq : ({x : List Bool | x ∈ (Set.univ : Language Bool) ∧ x ∉ L} : Language Bool) =
          Lᶜ := by
        ext x
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨Set.mem_univ x, h⟩
      show Lᶜ ∈ PvsNP.NP
      rw [← heq]
      exact hdiff
    apply le_antisymm
    · exact hsub
    · intro L hL
      have hLc : Lᶜ ∈ PvsNP.NP := hL
      have h2 : Lᶜ ∈ PvsNP.coNP := hsub hLc
      have h3 : (Lᶜ)ᶜ ∈ PvsNP.NP := h2
      rwa [compl_compl] at h3
