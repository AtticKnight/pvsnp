import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_halves_pair

/-- The pair `(1^⌊|x|/2⌋, x)` is computable in polynomial time. -/
theorem pre :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (List.replicate (x.length / 2) true, x)) :=
  PvsNP.Units.m2_pair_build_polytime _ _ (PvsNP.Units.m2_tm_unary_div_const 2)
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩

theorem first :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.take (x.length / 2)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeString _ _ pre PvsNP.Units.m2_take_drop_length_polytime.1
  convert h using 1
  funext x
  simp [Function.comp]

theorem second :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.drop (x.length / 2)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeString _ _ pre PvsNP.Units.m2_take_drop_length_polytime.2
  convert h using 1
  funext x
  simp [Function.comp]

end PvsNP.Units.m2_tm_halves_pair

theorem PvsNP.Units.m2_tm_halves_pair :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x.take (x.length / 2), x.drop (x.length / 2))) :=
  PvsNP.Units.m2_pair_build_polytime _ _
    PvsNP.Units.m2_tm_halves_pair.first PvsNP.Units.m2_tm_halves_pair.second
