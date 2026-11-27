import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_in_p
import PvsNP.Units.m2_npc_join
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed

/-- The join of two languages is in P, or in NP, exactly when both are: the forward
    directions use the settled join-in-P / join-in-NP units, the backward directions
    reduce each side to the join (m2_join_karp_sides) and close down. No machine. -/
theorem PvsNP.Units.m2_join_classes_iff :
    ∀ L₁ L₂ : Language Bool,
      (({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∈ PvsNP.P ↔ L₁ ∈ PvsNP.P ∧ L₂ ∈ PvsNP.P) ∧
      (({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∈ PvsNP.NP ↔ L₁ ∈ PvsNP.NP ∧ L₂ ∈ PvsNP.NP) := by
  intro L₁ L₂
  obtain ⟨hred1, hred2⟩ := PvsNP.Units.m2_join_karp_sides L₁ L₂
  constructor
  · constructor
    · intro hJ
      exact ⟨PvsNP.Units.m2_p_down_closed L₁ _ hred1 hJ,
        PvsNP.Units.m2_p_down_closed L₂ _ hred2 hJ⟩
    · rintro ⟨h1, h2⟩
      exact PvsNP.Units.m2_join_in_p L₁ L₂ h1 h2
  · constructor
    · intro hJ
      exact ⟨PvsNP.Units.m2_np_down_closed L₁ _ hred1 hJ,
        PvsNP.Units.m2_np_down_closed L₂ _ hred2 hJ⟩
    · rintro ⟨h1, h2⟩
      exact PvsNP.Units.m2_npc_join.join_in_np h1 h2
