import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_np_inter

namespace PvsNP.Units.m2_np_list_closure

/-- The union of no languages is empty. -/
theorem union_nil :
    ({x : List Bool | ∃ L ∈ ([] : List (Language Bool)), x ∈ L} : Language Bool) = ∅ := by
  ext x
  simp

/-- The intersection of no languages is everything. -/
theorem inter_nil :
    ({x : List Bool | ∀ L ∈ ([] : List (Language Bool)), x ∈ L} : Language Bool)
      = Set.univ := by
  ext x
  simp

/-- Adding one language to the union. -/
theorem union_cons (L : Language Bool) (Ls : List (Language Bool)) :
    ({x : List Bool | ∃ M ∈ L :: Ls, x ∈ M} : Language Bool)
      = L ⊔ {x : List Bool | ∃ M ∈ Ls, x ∈ M} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.sup_eq_union, Set.mem_union, List.mem_cons]
  constructor
  · rintro ⟨M, rfl | hM, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨M, hM, hx⟩
  · rintro (hx | ⟨M, hM, hx⟩)
    · exact ⟨L, Or.inl rfl, hx⟩
    · exact ⟨M, Or.inr hM, hx⟩

/-- Adding one language to the intersection. -/
theorem inter_cons (L : Language Bool) (Ls : List (Language Bool)) :
    ({x : List Bool | ∀ M ∈ L :: Ls, x ∈ M} : Language Bool)
      = L ⊓ {x : List Bool | ∀ M ∈ Ls, x ∈ M} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.inf_eq_inter, Set.mem_inter, List.mem_cons]
  constructor
  · intro h
    exact ⟨h L (Or.inl rfl), fun M hM => h M (Or.inr hM)⟩
  · rintro ⟨hx, h⟩ M (rfl | hM)
    · exact hx
    · exact h M hM

end PvsNP.Units.m2_np_list_closure

theorem PvsNP.Units.m2_np_list_closure :
    ∀ Ls : List (Language Bool), (∀ L ∈ Ls, L ∈ PvsNP.NP) →
      ({x : List Bool | ∃ L ∈ Ls, x ∈ L} : Language Bool) ∈ PvsNP.NP ∧
        ({x : List Bool | ∀ L ∈ Ls, x ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro Ls
  induction Ls with
  | nil =>
      intro _
      constructor
      · rw [PvsNP.Units.m2_np_list_closure.union_nil]
        exact PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.1
      · rw [PvsNP.Units.m2_np_list_closure.inter_nil]
        exact PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.2
  | cons L Ls ih =>
      intro h
      have hL : L ∈ PvsNP.NP := h L (List.mem_cons.mpr (Or.inl rfl))
      have hLs : ∀ M ∈ Ls, M ∈ PvsNP.NP := fun M hM => h M (List.mem_cons.mpr (Or.inr hM))
      obtain ⟨ihU, ihI⟩ := ih hLs
      constructor
      · rw [PvsNP.Units.m2_np_list_closure.union_cons]
        exact PvsNP.Units.m2_np_union L _ hL ihU
      · rw [PvsNP.Units.m2_np_list_closure.inter_cons]
        exact PvsNP.Units.m2_np_inter L _ hL ihI
