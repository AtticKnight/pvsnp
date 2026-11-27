import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_conp_list_closure

theorem PvsNP.Units.m2_z_conp_range_closure :
    ∀ (F : ℕ → Language Bool) (m : ℕ), (∀ i < m, F i ∈ PvsNP.coNP) →
      ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.coNP ∧
      ({x : List Bool | ∀ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.coNP := by
  intro F m hF
  let Ls := (List.range m).map F
  have hMem (L : Language Bool) : L ∈ Ls ↔ ∃ i < m, F i = L := by
    change L ∈ (List.range m).map F ↔ ∃ i < m, F i = L
    simp only [List.mem_map, List.mem_range]
  have hLs : ∀ L ∈ Ls, L ∈ PvsNP.coNP := by
    intro L hL
    obtain ⟨i, hi, rfl⟩ := (hMem L).mp hL
    exact hF i hi
  obtain ⟨hU, hI⟩ := PvsNP.Units.m2_conp_list_closure Ls hLs
  have unionEq :
      ({x : List Bool | ∃ L ∈ Ls, x ∈ L} : Language Bool) =
      {x | ∃ i < m, x ∈ F i} := by
    ext x
    change (∃ L ∈ Ls, x ∈ L) ↔ (∃ i < m, x ∈ F i)
    constructor
    · rintro ⟨L, hL, hx⟩
      obtain ⟨i, hi, rfl⟩ := (hMem L).mp hL
      exact ⟨i, hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      exact ⟨F i, (hMem (F i)).mpr ⟨i, hi, rfl⟩, hx⟩
  have interEq :
      ({x : List Bool | ∀ L ∈ Ls, x ∈ L} : Language Bool) =
      {x | ∀ i < m, x ∈ F i} := by
    ext x
    change (∀ L ∈ Ls, x ∈ L) ↔ (∀ i < m, x ∈ F i)
    constructor
    · intro hx i hi
      exact hx (F i) ((hMem (F i)).mpr ⟨i, hi, rfl⟩)
    · intro hx L hL
      obtain ⟨i, hi, rfl⟩ := (hMem L).mp hL
      exact hx i hi
  rw [unionEq] at hU
  rw [interEq] at hI
  exact ⟨hU, hI⟩
