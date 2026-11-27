import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_take_drop_length_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Reconstruct the only possible cube from the prefix of length one third of the input. -/
theorem PvsNP.Units.tl_lang_cube_p :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool) ∈ PvsNP.P := by
  have inputs := PvsNP.Units.m2_pair_build_polytime _ _ (PvsNP.Units.m2_tm_unary_div_const 3) cpt_id
  have segment : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.take (x.length / 3)) := by
    simpa only [List.length_replicate] using
      (PvsNP.Units.m2_pair_build_polytime.cpt_comp inputs PvsNP.Units.m2_take_drop_length_polytime.1)
  have cubed := cpt_app2 (cpt_app2 segment segment) segment
  have eqTest := PvsNP.Units.m2_pair_build_polytime.cpt_comp
    (PvsNP.Units.m2_pair_build_polytime _ _ cpt_id cubed) PvsNP.Units.m2_eq_polytime
  refine ⟨_, eqTest, fun x => ?_⟩
  change (∃ y : List Bool, x = y ++ y ++ y) ↔
    decide (x = x.take (x.length / 3) ++ x.take (x.length / 3) ++ x.take (x.length / 3)) = true
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨y, rfl⟩
    have len : (y ++ y ++ y).length / 3 = y.length := by simp only [List.length_append]; omega
    simp only [len, List.append_assoc, List.take_left]
  · intro h
    exact ⟨_, h⟩
