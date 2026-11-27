import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_sigma2
import PvsNP.Units.m2_p_subset_np_conp
import PvsNP.Units.m2_p_eq_np_iff_projection

set_option autoImplicit false

/-- `P = NP` iff `P` is closed under polynomial-time bounded existential projection over `coNP`. -/
theorem PvsNP.Units.m2_p_eq_np_iff_sigma2_p :
    PvsNP.P = PvsNP.NP ↔ ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.coNP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) ∈ PvsNP.P := by
  constructor
  · exact PvsNP.Units.m2_p_eq_np_sigma2
  · intro h
    refine PvsNP.Units.m2_p_eq_np_iff_projection.mpr (fun E g p hE hg => ?_)
    exact h E g p (PvsNP.Units.m2_p_subset_np_conp hE).2 hg
