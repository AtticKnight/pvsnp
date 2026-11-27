import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m1_sat_npcomplete_tm2
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_flat_np_to_st_np
import PvsNP.Units.m1_st_np_to_flat_np
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_p_eq_np_iff_npc_in_p

private theorem p_down_closed {L₁ L₂ : Language Bool}
    (hred : PvsNP.KarpReducible L₁ L₂) (hP : L₂ ∈ PvsNP.P) : L₁ ∈ PvsNP.P := by
  obtain ⟨r, hr_poly, hr_iff⟩ := hred
  obtain ⟨d, hd_poly, hd_iff⟩ := hP
  refine ⟨d ∘ r, PvsNP.Units.m2_polytime_comp _ _ _ r d hr_poly hd_poly, fun x => ?_⟩
  exact (hr_iff x).trans (hd_iff (r x))

theorem main :
    (PvsNP.P = PvsNP.NP ↔ ∀ L : Language Bool, PvsNP.NPComplete L → L ∈ PvsNP.P) ∧
      (PvsNP.P = PvsNP.NP ↔ ∃ L : Language Bool, PvsNP.NPComplete L ∧ L ∈ PvsNP.P) := by
  have hSAT_NPC : PvsNP.NPComplete ({x : List Bool | SATStr x} : Language Bool) :=
    PvsNP.Units.m1_sat_npcomplete_tm2
      PvsNP.Units.m1_flat_to_st
      (fun L => ⟨PvsNP.Units.m1_flat_np_to_st_np L, PvsNP.Units.m1_st_np_to_flat_np L⟩)
      (fun ea eb f => ⟨PvsNP.Units.m1_st_to_tm2 ea eb f, PvsNP.Units.m1_tm2_to_st ea eb f⟩)
      {x : List Bool | SATStr x}
      (fun _ => Iff.rfl)
  have hex : ∃ L : Language Bool, PvsNP.NPComplete L := ⟨_, hSAT_NPC⟩
  constructor
  · constructor
    · intro hEq L hNPC
      rw [hEq]
      exact hNPC.1
    · intro hall
      obtain ⟨L₀, hL₀⟩ := hex
      have hL₀P : L₀ ∈ PvsNP.P := hall L₀ hL₀
      exact Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
        (fun L hL => p_down_closed (hL₀.2 L hL) hL₀P)
  · constructor
    · intro hEq
      obtain ⟨L₀, hL₀⟩ := hex
      exact ⟨L₀, hL₀, hEq ▸ hL₀.1⟩
    · rintro ⟨L₀, hL₀, hL₀P⟩
      exact Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
        (fun L hL => p_down_closed (hL₀.2 L hL) hL₀P)

end PvsNP.Units.m2_p_eq_np_iff_npc_in_p

theorem PvsNP.Units.m2_p_eq_np_iff_npc_in_p :
    (PvsNP.P = PvsNP.NP ↔ ∀ L : Language Bool, PvsNP.NPComplete L → L ∈ PvsNP.P) ∧
      (PvsNP.P = PvsNP.NP ↔ ∃ L : Language Bool, PvsNP.NPComplete L ∧ L ∈ PvsNP.P) :=
  PvsNP.Units.m2_p_eq_np_iff_npc_in_p.main
