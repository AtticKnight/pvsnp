import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection

theorem PvsNP.Units.m2_np_eq_conp_sigma2 :
    PvsNP.NP = PvsNP.coNP → ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.coNP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) ∈ PvsNP.NP := by
  intro h E g p hE hg
  rw [← h] at hE
  exact PvsNP.Units.m2_np_projection E g p hE hg
