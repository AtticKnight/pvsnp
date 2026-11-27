import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_list_closure

/-- NP is closed under the union and the intersection of a family over a finite
set of indices: apply the settled unit `m2_np_list_closure` to the list
`S.toList.map F`; membership in that list is membership in the finset
(`List.mem_map`, `Finset.mem_toList`). -/
theorem PvsNP.Units.m2_z_np_finset_closure :
    ∀ (S : Finset ℕ) (F : ℕ → Language Bool), (∀ i ∈ S, F i ∈ PvsNP.NP) →
      ({x : List Bool | ∃ i ∈ S, x ∈ F i} : Language Bool) ∈ PvsNP.NP ∧ ({x : List Bool | ∀ i ∈ S, x ∈ F i} : Language Bool) ∈ PvsNP.NP := by
  intro S F hF
  have hlist := PvsNP.Units.m2_np_list_closure (S.toList.map F) (by
    intro L hL
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hL
    exact hF i (Finset.mem_toList.mp hi))
  have hset1 : ({x : List Bool | ∃ i ∈ S, x ∈ F i} : Language Bool)
      = {x : List Bool | ∃ L ∈ S.toList.map F, x ∈ L} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hxi⟩
      exact ⟨F i, List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, hxi⟩
    · rintro ⟨L, hL, hxL⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hL
      exact ⟨i, Finset.mem_toList.mp hi, hxL⟩
  have hset2 : ({x : List Bool | ∀ i ∈ S, x ∈ F i} : Language Bool)
      = {x : List Bool | ∀ L ∈ S.toList.map F, x ∈ L} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h L hL
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hL
      exact h i (Finset.mem_toList.mp hi)
    · intro h i hi
      exact h (F i) (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩)
  constructor
  · rw [hset1]
    exact hlist.1
  · rw [hset2]
    exact hlist.2
