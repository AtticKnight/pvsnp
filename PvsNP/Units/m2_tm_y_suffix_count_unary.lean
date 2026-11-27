import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_polytime_comp

/-- The number of trues after the first `|x|` bits of `y`, in unary, takes
polynomial time: drop the first `|x|` bits of `y` by the second conjunct of
the settled unit `m2_take_drop_length_polytime`, then count its trues in
unary by the settled unit `tf_fun_ones_unary`, composed by the settled unit
`m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_y_suffix_count_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate ((p.2.drop p.1.length).count true) true) := by
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    (fun x : List Bool => List.replicate (x.count true) true)
    PvsNP.Units.m2_take_drop_length_polytime.2
    PvsNP.Units.tf_fun_ones_unary
  exact hcomp
