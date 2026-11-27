import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_pair_rotate
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.tf_fun_rotate_count :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate (x.count true)) := by
  have pair := m2_pair_build_polytime
    (fun x : List Bool => List.replicate (x.count true) true) (fun x : List Bool => x)
    tf_fun_ones_unary m2_pair_build_polytime.cpt_id
  have rotate := m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (List.replicate (x.count true) true, x))
    (fun p : List Bool × List Bool => p.2.rotate p.1.length) pair tf_fun_pair_rotate
  simpa only [Function.comp_apply, List.length_replicate] using rotate
