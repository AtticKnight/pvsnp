import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime

namespace PvsNP.Units.m2_tm_mirror

/-- Pairing a string with its reverse is polynomial-time: the identity on the first
component (Mathlib's `Turing.idComputableInPolyTime`), the settled unit
`m2_reverse_polytime` on the second, joined by the settled unit
`m2_pair_build_polytime`. -/
theorem pair_mirror : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
    (fun x : List Bool => (x, x.reverse)) := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString id :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  exact PvsNP.Units.m2_pair_build_polytime _ _
    hid PvsNP.Units.m2_reverse_polytime

end PvsNP.Units.m2_tm_mirror

/-- Following a string by its reverse takes polynomial time (TM2).

Pair `x` with its reverse (the helper above), then join the pair with append (the third
part of the settled unit `m2_pair_split_polytime`), composed by the settled unit
`m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_mirror :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ x.reverse) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    _ _ PvsNP.Units.m2_tm_mirror.pair_mirror PvsNP.Units.m2_pair_split_polytime.2.2
