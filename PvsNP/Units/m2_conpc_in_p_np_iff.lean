import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_subset_np_conp
import PvsNP.Units.m2_p_eq_np_iff_conp
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_np_conp_one_inclusion

theorem PvsNP.Units.m2_conpc_in_p_np_iff :
    ∀ L : Language Bool, L ∈ PvsNP.coNP → (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L) →
      (L ∈ PvsNP.P ↔ PvsNP.P = PvsNP.NP) ∧ (L ∈ PvsNP.NP ↔ PvsNP.NP = PvsNP.coNP) := by
  intro L hLco hhard
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hLP
    have hPco : PvsNP.P = PvsNP.coNP :=
      Set.Subset.antisymm
        (fun M hM => (PvsNP.Units.m2_p_subset_np_conp hM).2)
        (fun L' hL' => PvsNP.Units.m2_p_down_closed L' L (hhard L' hL') hLP)
    exact PvsNP.Units.m2_p_eq_np_iff_conp.mpr hPco
  · intro hEq
    have hPco : PvsNP.P = PvsNP.coNP := PvsNP.Units.m2_p_eq_np_iff_conp.mp hEq
    exact hPco.symm ▸ hLco
  · intro hLNP
    exact PvsNP.Units.m2_np_conp_one_inclusion.2.mp
      (fun L' hL' => PvsNP.Units.m2_np_down_closed L' L (hhard L' hL') hLNP)
  · intro hEq
    exact hEq.symm ▸ hLco
