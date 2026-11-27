import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_refl

/-- Both tags dispatch to the identity reduction. Either inclusion embeds the language into its self-join. -/
theorem PvsNP.Units.m2_join_self_karp_equiv :
    ∀ L : Language Bool, (∃ z : List Bool, z ∉ L) →
  PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ L, x = true :: y)} : Language Bool) L ∧
    PvsNP.KarpReducible L ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ L, x = true :: y)} : Language Bool) := by
  intro L noInstance
  exact ⟨PvsNP.Units.m2_join_lub L L L (PvsNP.Units.m2_karp_refl L)
    (PvsNP.Units.m2_karp_refl L) noInstance, (PvsNP.Units.m2_join_karp_sides L L).1⟩
