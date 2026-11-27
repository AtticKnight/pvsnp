import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_conp_down_closed

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Duplicating the input is one polynomial reduction shared by the three closure arguments. -/
theorem PvsNP.Units.m2_self_concat_preimage :
    ∀ L : Language Bool,
  (L ∈ PvsNP.P → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.P) ∧
    (L ∈ PvsNP.NP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP) ∧
      (L ∈ PvsNP.coNP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) := by
  intro L
  have red : PvsNP.KarpReducible ({x : List Bool | x ++ x ∈ L} : Language Bool) L :=
    ⟨fun x => x ++ x, cpt_app2 cpt_id cpt_id, fun _ => Iff.rfl⟩
  exact ⟨PvsNP.Units.m2_p_down_closed _ _ red, PvsNP.Units.m2_np_down_closed _ _ red,
    PvsNP.Units.m2_conp_down_closed _ _ red⟩
