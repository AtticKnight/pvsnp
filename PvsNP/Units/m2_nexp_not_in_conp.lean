import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_nexp_not_in_np
import PvsNP.Units.m2_np_subset_nexp

/-- Some NEXP language is not in coNP (TM2). -/
theorem PvsNP.Units.m2_nexp_not_in_conp :
    ∃ L : Language Bool, (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) ∧
        L ∉ PvsNP.coNP := by
  obtain ⟨L, hL_nexp, hL_not_np⟩ := PvsNP.Units.m2_nexp_not_in_np
  by_cases hco : L ∈ PvsNP.coNP
  · have hLc_np : Lᶜ ∈ PvsNP.NP := hco
    have hLc_nexp := PvsNP.Units.m2_np_subset_nexp Lᶜ hLc_np
    refine ⟨Lᶜ, hLc_nexp, fun hLc_co => ?_⟩
    have hLcc_np : Lᶜᶜ ∈ PvsNP.NP := hLc_co
    rw [compl_compl] at hLcc_np
    exact hL_not_np hLcc_np
  · exact ⟨L, hL_nexp, hco⟩
