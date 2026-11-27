import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_join_karp_sides

/-- Use the opposite tag inclusion for each summand. The empty word belongs to neither tag. -/
theorem PvsNP.Units.m2_join_swap_karp :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)
  ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₁, x = true :: y)} : Language Bool) := by
  intro A B
  obtain ⟨b, a⟩ := PvsNP.Units.m2_join_karp_sides B A
  refine PvsNP.Units.m2_join_lub _ _ _ a b ⟨[], ?_⟩
  rintro (⟨y, _, h⟩ | ⟨y, _, h⟩) <;> cases h
