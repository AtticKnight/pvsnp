import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_conp_join
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_join_karp_sides

theorem PvsNP.Units.m2_join_compl_conp_iff :
    ∀ L : Language Bool, ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} :
        Language Bool) ∈ PvsNP.coNP ↔ L ∈ PvsNP.NP ∩ PvsNP.coNP := by
  intro L
  constructor
  · intro hJ
    have hLco : L ∈ PvsNP.coNP :=
      PvsNP.Units.m2_conp_down_closed L _
        (PvsNP.Units.m2_join_karp_sides L Lᶜ).1 hJ
    have hLcco : Lᶜ ∈ PvsNP.coNP :=
      PvsNP.Units.m2_conp_down_closed Lᶜ _
        (PvsNP.Units.m2_join_karp_sides L Lᶜ).2 hJ
    have hLNP : L ∈ PvsNP.NP := by
      have hcc : (Lᶜ)ᶜ ∈ PvsNP.NP := hLcco
      simpa using hcc
    exact ⟨hLNP, hLco⟩
  · rintro ⟨hLNP, hLco⟩
    have hLcco : Lᶜ ∈ PvsNP.coNP := by
      show (Lᶜ)ᶜ ∈ PvsNP.NP
      simpa using hLNP
    exact PvsNP.Units.m2_conp_join L Lᶜ hLco hLcco
