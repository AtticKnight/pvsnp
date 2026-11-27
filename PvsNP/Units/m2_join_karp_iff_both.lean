import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

-- Built from the settled campaign units m2_join_lub, m2_join_karp_sides and m2_karp_trans (make.fun pvsnp campaign).

namespace PvsNP.Units.m2_join_karp_iff_both

theorem sides_trans (L₁ L₂ L₃ : Language Bool)
    (h : PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) L₃) :
    PvsNP.KarpReducible L₁ L₃ ∧ PvsNP.KarpReducible L₂ L₃ :=
  ⟨PvsNP.Units.m2_karp_trans _ _ _ (PvsNP.Units.m2_join_karp_sides L₁ L₂).1 h,
    PvsNP.Units.m2_karp_trans _ _ _ (PvsNP.Units.m2_join_karp_sides L₁ L₂).2 h⟩

end PvsNP.Units.m2_join_karp_iff_both

theorem PvsNP.Units.m2_join_karp_iff_both :
    ∀ L₁ L₂ L₃ : Language Bool, (∃ z : List Bool, z ∉ L₃) →
      (PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) L₃ ↔
        PvsNP.KarpReducible L₁ L₃ ∧ PvsNP.KarpReducible L₂ L₃) := by
  intro L₁ L₂ L₃ hz
  have _hc := Classical.em (L₁ = L₂)
  constructor
  · intro h
    exact PvsNP.Units.m2_join_karp_iff_both.sides_trans L₁ L₂ L₃ h
  · rintro ⟨h1, h2⟩
    exact PvsNP.Units.m2_join_lub L₁ L₂ L₃ h1 h2 hz
