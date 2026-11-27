import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.tf_fun_self_append
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_polytime_comp

/-- Testing whether one string is at most twice as long as another takes
polynomial time: keep the first string (the identity, Mathlib's
`Turing.idComputableInPolyTime`) and write the second twice
(`tf_fun_self_append`), paired by `m2_prod_map_polytime`; then compare lengths
by `m2_len_le_polytime`, composed by `m2_polytime_comp`; the doubled length is
`2 * p.2.length` by `List.length_append` and `two_mul`. -/
theorem PvsNP.Units.m2_tm_y_length_le_double :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => decide (p.1.length ≤ 2 * p.2.length)) := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.2 ++ p.2)) :=
    PvsNP.Units.m2_prod_map_polytime _ _ hid PvsNP.Units.tf_fun_self_append
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1.length ≤ (p.2 ++ p.2).length)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpair PvsNP.Units.m2_len_le_polytime
  have hfun : (fun p : List Bool × List Bool => decide (p.1.length ≤ (p.2 ++ p.2).length))
      = (fun p : List Bool × List Bool => decide (p.1.length ≤ 2 * p.2.length)) := by
    funext p
    rw [List.length_append, two_mul]
  rw [hfun] at hcomp
  exact hcomp
