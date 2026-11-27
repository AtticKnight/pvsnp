import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_conp_list_closure

theorem PvsNP.Units.m2_z_conp_finset_closure : ∀ (S : Finset ℕ) (F : ℕ → Language Bool), (∀ i ∈ S, F i ∈ PvsNP.coNP) →
  ({x : List Bool | ∃ i ∈ S, x ∈ F i} : Language Bool) ∈ PvsNP.coNP ∧ ({x : List Bool | ∀ i ∈ S, x ∈ F i} : Language Bool) ∈ PvsNP.coNP := by
  intro S F hF
  have h := PvsNP.Units.m2_conp_list_closure (S.toList.map F) (by
    intro L hL
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hL
    exact hF i (Finset.mem_toList.mp hi))
  have e1 : ({x : List Bool | ∃ i ∈ S, x ∈ F i} : Language Bool) =
      {x : List Bool | ∃ L ∈ S.toList.map F, x ∈ L} := by
    ext x
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨F i, List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, hx⟩
    · rintro ⟨L, hL, hx⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hL
      exact ⟨i, Finset.mem_toList.mp hi, hx⟩
  have e2 : ({x : List Bool | ∀ i ∈ S, x ∈ F i} : Language Bool) =
      {x : List Bool | ∀ L ∈ S.toList.map F, x ∈ L} := by
    ext x
    constructor
    · intro hx L hL
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hL
      exact hx i (Finset.mem_toList.mp hi)
    · intro hx i hi
      exact hx (F i) (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩)
  rw [e1, e2]
  exact h
