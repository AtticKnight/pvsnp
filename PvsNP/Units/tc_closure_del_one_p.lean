import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_del_one_conp
import PvsNP.Units.tc_closure_rotate_p
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_union

open PvsNP.Units.tc_closure_del_one_conp

/-- Decode each marked rotation at both possible inserted bits and combine polynomial deciders. -/
theorem PvsNP.Units.tc_closure_del_one_p :
    ∀ L : Language Bool, L ∈ PvsNP.P → ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  have pre (b : Bool) : ({r | W b r ∈ L} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_down_closed _ L ⟨W b, W_polytime b, fun _ => Iff.rfl⟩ hL
  have marked : M L ∈ PvsNP.P :=
    PvsNP.Units.m2_p_union _ _ (PvsNP.Units.m2_p_inter _ _ wf_in_p (pre false))
      (PvsNP.Units.m2_p_inter _ _ wf_in_p (pre true))
  exact PvsNP.Units.m2_p_down_closed _ _ ⟨T, T_polytime, mem_iff L⟩
    (PvsNP.Units.tc_closure_rotate_p _ marked)
