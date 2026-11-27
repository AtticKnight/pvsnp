import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_reduces_nontrivial
import PvsNP.Units.m2_p_down_closed

/-- P is exactly what reduces to any one nontrivial language in P: a language in P
reduces to any nontrivial language in P, and P is closed downward under reductions. -/
theorem PvsNP.Units.m2_p_karp_degree :
    ∀ L₀ ∈ PvsNP.P, (∃ y : List Bool, y ∈ L₀) → (∃ z : List Bool, z ∉ L₀) →
      ∀ L : Language Bool, L ∈ PvsNP.P ↔ PvsNP.KarpReducible L L₀ := by
  intro L₀ hL₀ hy hz L
  constructor
  · intro hL
    apply PvsNP.Units.m2_p_reduces_nontrivial
    all_goals assumption
  · intro hred
    exact PvsNP.Units.m2_p_down_closed L L₀ hred hL₀
