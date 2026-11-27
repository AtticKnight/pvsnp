import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_trans
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_join_lub

/-- The join is monotone under Karp reductions in both arguments (TM2): each side reduces
into the target join via `m2_join_karp_sides` and `m2_karp_trans`, and `[]` is never in a
join, so `m2_join_lub` gives the reduction from the source join to the target join. -/
theorem PvsNP.Units.m2_join_monotone :
    ∀ L₁ L₂ L₃ L₄ : Language Bool, PvsNP.KarpReducible L₁ L₂ → PvsNP.KarpReducible L₃ L₄ →
      PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool)
        ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₄, x = true :: y)} : Language Bool) := by
  intro L₁ L₂ L₃ L₄ h12 h34
  obtain ⟨hs1, hs2⟩ := PvsNP.Units.m2_join_karp_sides L₂ L₄
  refine PvsNP.Units.m2_join_lub L₁ L₃ _
    (PvsNP.Units.m2_karp_trans L₁ L₂ _ h12 hs1)
    (PvsNP.Units.m2_karp_trans L₃ L₄ _ h34 hs2)
    ⟨[], ?_⟩
  rintro (⟨y, _, h⟩ | ⟨y, _, h⟩) <;> cases h
