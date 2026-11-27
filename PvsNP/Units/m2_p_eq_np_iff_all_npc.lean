import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_npc
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_npc_in_p

namespace PvsNP.Units.m2_p_eq_np_iff_all_npc

def singletonNil : Language Bool :=
  {x : List Bool | x ∈ ({([] : List Bool)} : Finset (List Bool))}

theorem singletonNil_in_P : singletonNil ∈ PvsNP.P :=
  PvsNP.Units.m2_p_finite {([] : List Bool)}

end PvsNP.Units.m2_p_eq_np_iff_all_npc

theorem PvsNP.Units.m2_p_eq_np_iff_all_npc :
    PvsNP.P = PvsNP.NP ↔
      ∀ L ∈ PvsNP.NP, (∃ y : List Bool, y ∈ L) → (∃ z : List Bool, z ∉ L) → PvsNP.NPComplete L := by
  constructor
  · intro hEq L hL hy hz
    exact PvsNP.Units.m2_p_eq_np_npc hEq L (hEq.symm ▸ hL) hy hz
  · intro hAll
    have hP : PvsNP.Units.m2_p_eq_np_iff_all_npc.singletonNil ∈ PvsNP.P :=
      PvsNP.Units.m2_p_eq_np_iff_all_npc.singletonNil_in_P
    have hNP : PvsNP.Units.m2_p_eq_np_iff_all_npc.singletonNil ∈ PvsNP.NP :=
      PvsNP.Units.m2_p_subset_np hP
    have hy : ∃ y : List Bool, y ∈ PvsNP.Units.m2_p_eq_np_iff_all_npc.singletonNil :=
      ⟨[], Finset.mem_singleton_self []⟩
    have hz : ∃ z : List Bool, z ∉ PvsNP.Units.m2_p_eq_np_iff_all_npc.singletonNil :=
      ⟨[true], fun h => absurd (Finset.mem_singleton.mp h) (by decide)⟩
    exact PvsNP.Units.m2_npc_in_p _ (hAll _ hNP hy hz) hP
