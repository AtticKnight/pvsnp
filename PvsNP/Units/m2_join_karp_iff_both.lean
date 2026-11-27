import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

/-- Compose each tag inclusion with the common reduction. Dispatching on the tag gives the converse. -/
theorem PvsNP.Units.m2_join_karp_iff_both :
    ∀ L₁ L₂ L₃ : Language Bool, (∃ z : List Bool, z ∉ L₃) →
  (PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) L₃ ↔
    PvsNP.KarpReducible L₁ L₃ ∧ PvsNP.KarpReducible L₂ L₃) := by
  intro A B C noInstance
  constructor
  · intro r
    obtain ⟨a, b⟩ := PvsNP.Units.m2_join_karp_sides A B
    exact ⟨PvsNP.Units.m2_karp_trans _ _ _ a r, PvsNP.Units.m2_karp_trans _ _ _ b r⟩
  · rintro ⟨a, b⟩
    exact PvsNP.Units.m2_join_lub A B C a b noInstance
