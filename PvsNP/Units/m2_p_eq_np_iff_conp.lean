import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_eq_np_conp

/-!
# m2_p_eq_np_iff_conp

Proved from the settled units `m2_p_subset_np`, `m2_p_eq_np_conp` of github.com/makedotfun/pvsnp
(commit fe00cce97615b933d953614d674245879348ec48), imported as the unit's allowed imports.
-/

namespace PvsNP.Units.m2_p_eq_np_iff_conp


/-- P = NP exactly when P = coNP. -/
theorem h_p_np_iff_p_conp : PvsNP.P = PvsNP.NP ↔ PvsNP.P = PvsNP.coNP := by
  constructor
  · intro h
    exact h.trans (PvsNP.Units.m2_p_eq_np_conp h)
  · intro h
    apply Set.Subset.antisymm
    · exact fun L hL => PvsNP.Units.m2_p_subset_np hL
    · intro L hL
      -- Lᶜ ∈ coNP = P, so L ∈ P
      have hc : Lᶜ ∈ PvsNP.coNP := by
        show Lᶜᶜ ∈ PvsNP.NP
        simpa using hL
      have hcP : Lᶜ ∈ PvsNP.P := h ▸ hc
      have := PvsNP.Units.m2_p_eq_np_conp.p_compl hcP
      simpa using this


/-- NP ⊆ coNP exactly when NP = coNP. -/
theorem h_np_sub_conp_iff : PvsNP.NP ⊆ PvsNP.coNP ↔ PvsNP.NP = PvsNP.coNP := by
  constructor
  · intro h
    apply Set.Subset.antisymm h
    intro L hL
    have : Lᶜ ∈ PvsNP.coNP := h hL
    have h2 : Lᶜᶜ ∈ PvsNP.NP := this
    simpa using h2
  · intro h; rw [h]


/-- coNP ⊆ NP exactly when NP = coNP. -/
theorem h_conp_sub_np_iff : PvsNP.coNP ⊆ PvsNP.NP ↔ PvsNP.NP = PvsNP.coNP := by
  constructor
  · intro h
    apply Set.Subset.antisymm _ h
    intro L hL
    have hc : Lᶜ ∈ PvsNP.coNP := by
      show Lᶜᶜ ∈ PvsNP.NP
      simpa using hL
    exact h hc
  · intro h; rw [h]


end PvsNP.Units.m2_p_eq_np_iff_conp

theorem PvsNP.Units.m2_p_eq_np_iff_conp :
    PvsNP.P = PvsNP.NP ↔ PvsNP.P = PvsNP.coNP :=
  PvsNP.Units.m2_p_eq_np_iff_conp.h_p_np_iff_p_conp
