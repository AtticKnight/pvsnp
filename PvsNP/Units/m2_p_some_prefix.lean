import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_concat
import PvsNP.Units.m2_p_trivial

/-- P is closed under "some prefix is in L" (TM2): the language of strings with a prefix in `L`
is the concatenation of `L` with the universal language, since `y <+: x` means `x = y ++ z`
for some `z`, and both `L` and the universal language are in P. -/
theorem PvsNP.Units.m2_p_some_prefix :
    ∀ L ∈ PvsNP.P, ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  have h := PvsNP.Units.m2_p_concat L (Set.univ : Language Bool) hL
    PvsNP.Units.m2_p_trivial.2
  have e : ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool) =
      {x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ L ∧
        v ∈ (Set.univ : Language Bool)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, hy⟩
      exact ⟨y, z, rfl, hy, Set.mem_univ z⟩
    · rintro ⟨u, v, rfl, hu, -⟩
      exact ⟨u, ⟨v, rfl⟩, hu⟩
  rw [e]
  exact h
