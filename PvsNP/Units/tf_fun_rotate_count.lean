import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.tf_fun_pair_rotate

open PvsNP.Units

/-- Pair the unary count with the unchanged input. The pair rotation then
uses exactly the number of true symbols as its shift. -/
theorem PvsNP.Units.tf_fun_rotate_count :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate (x.count true)) := by
  have paired := m2_pair_build_polytime _ _ tf_fun_ones_unary m2_pair_build_polytime.cpt_id
  have rotated := m2_polytime_comp _ _ _ _ _ paired tf_fun_pair_rotate
  simpa only [Function.comp_def, List.length_replicate] using rotated
