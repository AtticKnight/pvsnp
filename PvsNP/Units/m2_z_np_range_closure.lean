import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_list_closure

theorem PvsNP.Units.m2_z_np_range_closure :
    ∀ (F : ℕ → Language Bool) (m : ℕ), (∀ i < m, F i ∈ PvsNP.NP) →
      ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.NP ∧
        ({x : List Bool | ∀ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.NP := by
  intro F m hF
  have hmem : ∀ L ∈ (List.range m).map F, L ∈ PvsNP.NP := by
    intro L hL
    rw [List.mem_map] at hL
    obtain ⟨i, hi, rfl⟩ := hL
    rw [List.mem_range] at hi
    exact hF i hi
  have h := PvsNP.Units.m2_np_list_closure ((List.range m).map F) hmem
  have hunion : ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) =
      {x : List Bool | ∃ L ∈ (List.range m).map F, x ∈ L} := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, hxi⟩
      exact ⟨F i, ⟨i, hi, rfl⟩, hxi⟩
    · rintro ⟨L, ⟨i, hi, rfl⟩, hxi⟩
      exact ⟨i, hi, hxi⟩
  have hinter : ({x : List Bool | ∀ i < m, x ∈ F i} : Language Bool) =
      {x : List Bool | ∀ L ∈ (List.range m).map F, x ∈ L} := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_range]
    constructor
    · intro hx L hL
      obtain ⟨i, hi, rfl⟩ := hL
      exact hx i hi
    · intro hx i hi
      exact hx (F i) ⟨i, hi, rfl⟩
  rw [hunion, hinter]
  exact h
