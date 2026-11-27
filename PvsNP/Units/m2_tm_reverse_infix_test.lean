import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_infix_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.m2_tm_reverse_infix_test :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => decide (p.1.reverse <:+: p.2)) := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime _⟩
  have hm := PvsNP.Units.m2_prod_map_polytime _ _ PvsNP.Units.m2_reverse_polytime hid
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _ hm PvsNP.Units.m2_tm_infix_polytime
