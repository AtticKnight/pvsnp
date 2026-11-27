import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_list_closure
import PvsNP.Units.m2_conp_list_closure

/-- NP ∩ coNP is closed under the union and the intersection of a family indexed below a bound
(TM2). -/
theorem PvsNP.Units.m2_z_np_conp_range_closure :
    ∀ (F : ℕ → Language Bool) (m : ℕ), (∀ i < m, F i ∈ PvsNP.NP ∩ PvsNP.coNP) →
      ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.NP ∩ PvsNP.coNP ∧
        ({x : List Bool | ∀ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.NP ∩ PvsNP.coNP := by
  intro F m hF
  have hmem : ∀ L ∈ (List.range m).map F, L ∈ PvsNP.NP := by
    intro L hL
    rw [List.mem_map] at hL
    obtain ⟨i, hi, rfl⟩ := hL
    rw [List.mem_range] at hi
    exact (hF i hi).1
  have hmemc : ∀ L ∈ (List.range m).map F, L ∈ PvsNP.coNP := by
    intro L hL
    rw [List.mem_map] at hL
    obtain ⟨i, hi, rfl⟩ := hL
    rw [List.mem_range] at hi
    exact (hF i hi).2
  obtain ⟨hun, hint⟩ := PvsNP.Units.m2_np_list_closure ((List.range m).map F) hmem
  obtain ⟨hunc, hintc⟩ := PvsNP.Units.m2_conp_list_closure ((List.range m).map F) hmemc
  have hunion : ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool)
      = {x : List Bool | ∃ L ∈ (List.range m).map F, x ∈ L} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hxi⟩
      exact ⟨F i, List.mem_map_of_mem (List.mem_range.mpr hi), hxi⟩
    · rintro ⟨L, hL, hxL⟩
      rw [List.mem_map] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      rw [List.mem_range] at hi
      exact ⟨i, hi, hxL⟩
  have hinter : ({x : List Bool | ∀ i < m, x ∈ F i} : Language Bool)
      = {x : List Bool | ∀ L ∈ (List.range m).map F, x ∈ L} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h L hL
      rw [List.mem_map] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      rw [List.mem_range] at hi
      exact h i hi
    · intro h i hi
      exact h (F i) (List.mem_map_of_mem (List.mem_range.mpr hi))
  rw [hunion, hinter]
  exact ⟨⟨hun, hunc⟩, ⟨hint, hintc⟩⟩
