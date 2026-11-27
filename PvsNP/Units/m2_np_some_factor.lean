import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_concat
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_np

theorem PvsNP.Units.m2_np_some_factor :
    ∀ L ∈ PvsNP.NP, ({x : List Bool | ∃ y : List Bool, y <:+: x ∧ y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have huniv : (Set.univ : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_trivial).2
  have h1 := PvsNP.Units.m2_np_concat Set.univ L huniv hL
  have h2 := PvsNP.Units.m2_np_concat _ Set.univ h1 huniv
  have heq :
      ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧
          u ∈ ({z : List Bool | ∃ a b : List Bool, z = a ++ b ∧ a ∈ (Set.univ : Language Bool) ∧ b ∈ L} : Language Bool) ∧
          v ∈ (Set.univ : Language Bool)} : Language Bool) =
      ({x : List Bool | ∃ y : List Bool, y <:+: x ∧ y ∈ L} : Language Bool) := by
    ext x
    constructor
    · rintro ⟨u, t, rfl, ⟨s, y, rfl, -, hy⟩, -⟩
      exact ⟨y, ⟨s, t, rfl⟩, hy⟩
    · rintro ⟨y, ⟨s, t, rfl⟩, hy⟩
      exact ⟨s ++ y, t, rfl, ⟨s, y, rfl, trivial, hy⟩, trivial⟩
  rw [← heq]
  exact h2
