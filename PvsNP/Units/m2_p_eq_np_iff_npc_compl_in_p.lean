import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_npc_exists
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_karp_compl_iff
import PvsNP.Units.m2_p_subset_np

namespace PvsNP.Units.m2_p_eq_np_iff_npc_compl_in_p

/-- If P = NP, take any NP-complete language (they exist by Cook-Levin): it lies in NP = P, and P
is closed under complement, so its complement is in P. -/
theorem forward (h : PvsNP.P = PvsNP.NP) :
    ∃ L : Language Bool, PvsNP.NPComplete L ∧ Lᶜ ∈ PvsNP.P := by
  obtain ⟨L, hL⟩ := PvsNP.Units.m2_npc_exists
  have hLP : L ∈ PvsNP.P := h.symm ▸ hL.1
  exact ⟨L, hL, PvsNP.Units.m2_p_compl L hLP⟩

/-- If some NP-complete language has its complement in P, then every `A ∈ NP` reduces to `L`,
hence `Aᶜ` reduces to `Lᶜ ∈ P`; by downward closure of P under Karp reductions `Aᶜ ∈ P`, and
by closure of P under complement `A ∈ P`. So NP ⊆ P, and P ⊆ NP always holds. -/
theorem backward (h : ∃ L : Language Bool, PvsNP.NPComplete L ∧ Lᶜ ∈ PvsNP.P) :
    PvsNP.P = PvsNP.NP := by
  obtain ⟨L, hL, hcompl⟩ := h
  have hNPsubP : PvsNP.NP ⊆ PvsNP.P := by
    intro A hA
    have hred : PvsNP.KarpReducible A L := hL.2 A hA
    have hredc : PvsNP.KarpReducible Aᶜ Lᶜ :=
      (PvsNP.Units.m2_karp_compl_iff A L).mp hred
    have hc : Aᶜ ∈ PvsNP.P := PvsNP.Units.m2_p_down_closed Aᶜ Lᶜ hredc hcompl
    have hcc : Aᶜᶜ ∈ PvsNP.P := PvsNP.Units.m2_p_compl Aᶜ hc
    simpa using hcc
  exact Set.eq_of_subset_of_subset PvsNP.Units.m2_p_subset_np hNPsubP

end PvsNP.Units.m2_p_eq_np_iff_npc_compl_in_p

/-- P = NP exactly when some NP-complete language has its complement in P (TM2). -/
theorem PvsNP.Units.m2_p_eq_np_iff_npc_compl_in_p :
    PvsNP.P = PvsNP.NP ↔ ∃ L : Language Bool, PvsNP.NPComplete L ∧ Lᶜ ∈ PvsNP.P :=
  ⟨PvsNP.Units.m2_p_eq_np_iff_npc_compl_in_p.forward,
    PvsNP.Units.m2_p_eq_np_iff_npc_compl_in_p.backward⟩
