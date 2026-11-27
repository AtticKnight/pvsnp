import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_join_lub

/-- The join of two languages reduces to their join the other way round (TM2): each
side of the first join is a side of the swapped join, so it reduces to the swapped
join by `m2_join_karp_sides`; the join itself then reduces to the swapped join by
the least-upper-bound property `m2_join_lub`, anchored at the empty string, which
is a member of no join. -/
theorem PvsNP.Units.m2_join_swap_karp :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)
  ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₁, x = true :: y)} : Language Bool) := by
  intro L₁ L₂
  obtain ⟨h₂, h₁⟩ := PvsNP.Units.m2_join_karp_sides L₂ L₁
  refine PvsNP.Units.m2_join_lub L₁ L₂ _ h₁ h₂ ⟨[], ?_⟩
  intro h
  have h' : (∃ y ∈ L₂, ([] : List Bool) = false :: y) ∨
      (∃ y ∈ L₁, ([] : List Bool) = true :: y) := h
  rcases h' with ⟨y, _, h⟩ | ⟨y, _, h⟩ <;> cases h
